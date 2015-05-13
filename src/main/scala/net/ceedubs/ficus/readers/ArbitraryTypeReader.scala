package net.ceedubs.ficus.readers

import net.ceedubs.ficus.util.ReflectionUtils
import com.typesafe.config.Config
import scala.language.experimental.macros
import scala.reflect.internal.{StdNames, SymbolTable, Definitions}
import com.google.common.base.CaseFormat
import scala.annotation.StaticAnnotation
import scala.collection.JavaConversions._

trait ArbitraryTypeReader {
  @ArbitraryTypeReader.settings(identity, false)
  implicit def arbitraryTypeValueReader[T]: ValueReader[T] = macro ArbitraryTypeReaderMacros.arbitraryTypeValueReader[T]
}

object ArbitraryTypeReader extends ArbitraryTypeReader {
  class settings(paramKeyMapper: String => String = identity[String], exhaustiveMapping: Boolean = false) extends StaticAnnotation
}

trait OtherArbitraryTypeReader {
  @ArbitraryTypeReader.settings(_.toLowerCase, true)
  implicit def arbitraryTypeValueReader[T]: ValueReader[T] = macro ArbitraryTypeReaderMacros.arbitraryTypeValueReader[T]
}

object OtherArbitraryTypeReader extends OtherArbitraryTypeReader

object ArbitraryTypeReaderMacros {
  import scala.reflect.macros.blackbox.Context

  def assertExhaustive(cfg: Config, path: String, mappedPaths: Seq[String]): Unit = {
    val relevantPaths = cfg.getObject(path).keySet.map(k => s"$path.$k")
    val unmappedPaths = relevantPaths -- mappedPaths
    if (! unmappedPaths.isEmpty) throw new IllegalArgumentException(s"config paths not exhaustively mapped: $unmappedPaths")
  }

  def arbitraryTypeValueReader[T : c.WeakTypeTag](c: Context): c.Expr[ValueReader[T]] = {
    import c.universe._

    try {
    val annotationParamExpr
      = c.macroApplication.symbol.annotations
          .filter(_.tree.tpe <:< typeOf[ArbitraryTypeReader.settings]).head.tree.children.tail

    val paramMapperExpr :: exhaustiveMappingExpr :: Nil = annotationParamExpr

    //println(paramMapperExpr)

    val readerExpr = reify {
      new ValueReader[T] {
        val paramMapper: String => String = c.Expr[String => String](c.resetLocalAttrs(paramMapperExpr)).splice
        val exhaustiveMapping: Boolean = c.Expr[Boolean](c.resetLocalAttrs(exhaustiveMappingExpr)).splice
        def read(config: Config, path: String): T = instantiateFromConfig[T](c)(
          config = c.Expr[Config](Ident(TermName("config"))),
          path = c.Expr[String](Ident(TermName("path")))).splice
      }
    }

    //println(show(readerExpr))

    readerExpr
    } catch { // FIXME: remove
      case e => e.printStackTrace(); throw e
    }
  }

  def instantiateFromConfig[T : c.WeakTypeTag](c: Context)(config: c.Expr[Config], path: c.Expr[String]): c.Expr[T] = {
    import c.universe._

    val returnType = c.weakTypeOf[T]

    def fail(reason: String) = c.abort(c.enclosingPosition, s"Cannot generate a config value reader for type $returnType, because $reason")

    val companionSymbol = returnType.typeSymbol.companion match {
      case NoSymbol => None
      case x => Some(x)
    }

    val instantiationMethod = ReflectionUtils.instantiationMethod[T](c, fail)

    val instantiationArgsAndKeys = extractMethodArgsFromConfig[T](c)(method = instantiationMethod,
      companionObjectMaybe = companionSymbol, config = config, path = path, fail = fail)
    val (instantiationArgs, instantiationKeys) = instantiationArgsAndKeys.unzip
    val instantiationObject = companionSymbol.filterNot(_ =>
      instantiationMethod.isConstructor
    ).map(Ident(_)).getOrElse(New(Ident(returnType.typeSymbol)))
    val instantiationCall = Select(instantiationObject, instantiationMethod.name)

    val assertion = reify {
      assertExhaustive(config.splice, path.splice, c.Expr[List[String]](q"List(..$instantiationKeys)").splice)
    }

    val conditionalAssertion = If(Ident(TermName("exhaustiveMapping")), assertion.tree, Literal(Constant(())))
    val instantiation = Apply(instantiationCall, instantiationArgs)
    c.Expr[T](Block(List(conditionalAssertion), instantiation))
  }

  def extractMethodArgsFromConfig[T : c.WeakTypeTag](c: Context)(method: c.universe.MethodSymbol, companionObjectMaybe: Option[c.Symbol],
                                              config: c.Expr[Config], path: c.Expr[String], fail: String => Nothing): List[(c.Tree, c.Tree)] = {
    import c.universe._

    val decodedMethodName = method.name.decodedName.toString

    if (!method.isPublic) fail(s"'$decodedMethodName' method is not public")

    method.paramLists.head.zipWithIndex map { case (param, index) =>
      val name = param.name.decodedName.toString
      val key = q"""$path + "." + paramMapper($name)"""
      val returnType: Type = param.typeSignatureIn(c.weakTypeOf[T])

      (companionObjectMaybe.filter(_ => param.asTerm.isParamWithDefault) map { companionObject =>
        // class has companion object and param has default
        val optionType = appliedType(weakTypeOf[Option[_]].typeConstructor, List(returnType))
        val optionReaderType = appliedType(weakTypeOf[ValueReader[_]].typeConstructor, List(optionType))
        val optionReader = c.inferImplicitValue(optionReaderType, silent = true) match {
          case EmptyTree => fail(s"an implicit value reader of type $optionReaderType must be in scope to read parameter '$name' on '$decodedMethodName' method since '$name' has a default value")
          case x => x
        }
        val argValueMaybe = q"$optionReader.read($config, $key)"
        Apply(Select(argValueMaybe, TermName("getOrElse")), List({
          // fall back to default value for param
          val u = c.universe.asInstanceOf[Definitions with SymbolTable with StdNames]
          val getter = u.nme.defaultGetterName(u.TermName(decodedMethodName), index + 1)
          Select(Ident(companionObject), TermName(getter.encoded))
        }))
      } getOrElse {
        val readerType = appliedType(weakTypeOf[ValueReader[_]].typeConstructor, List(returnType))
        val reader = c.inferImplicitValue(readerType, silent = true) match {
          case EmptyTree => fail(s"an implicit value reader of type $readerType must be in scope to read parameter '$name' on '$decodedMethodName' method")
          case x => x
        }
        q"$reader.read($config, $key)"
      }, key)
    }
  }
}
