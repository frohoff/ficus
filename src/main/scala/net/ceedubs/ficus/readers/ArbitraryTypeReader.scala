package net.ceedubs.ficus.readers

import net.ceedubs.ficus.util.ReflectionUtils
import com.typesafe.config.Config
import scala.language.experimental.macros
import scala.reflect.internal.{StdNames, SymbolTable, Definitions}
import com.google.common.base.CaseFormat
import scala.annotation.StaticAnnotation
import scala.collection.JavaConversions._

trait ArbitraryTypeReader {
  implicit def arbitraryTypeValueReader[T]: ValueReader[T] = macro ArbitraryTypeReaderMacros.arbitraryTypeValueReader[T]
  val checkExhaustivity: Boolean = false
  def mapParam(n: String): String = n
  def assertExhaustive(cfg: Config, path: String, mappedPaths: Seq[String]): Unit = {
    val relevantPaths = cfg.getObject(path).keySet.map(k => s"$path.$k")
    val unmappedPaths = relevantPaths -- mappedPaths
    if (! unmappedPaths.isEmpty) throw new IllegalArgumentException(s"config paths not exhaustively mapped: $unmappedPaths")
  }
}

object ArbitraryTypeReader extends ArbitraryTypeReader

object ArbitraryTypeReaderMacros {
  import scala.reflect.macros.blackbox.Context


  def arbitraryTypeValueReader[T : c.WeakTypeTag](c: Context): c.Expr[ValueReader[T]] = {
    import c.universe._

    val readerExpr = reify {
      new ValueReader[T] {
        def read(config: Config, path: String): T = instantiateFromConfig[T](c)(
          config = c.Expr[Config](Ident(TermName("config"))),
          path = c.Expr[String](Ident(TermName("path")))).splice
      }
    }

    readerExpr
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

    val enclosingObject = c.Expr[ArbitraryTypeReader](c.prefix.tree)

    val keyListExpr = c.Expr[List[String]](q"List(..$instantiationKeys)")

    val conditionalAssertion = reify {
      if (enclosingObject.splice.checkExhaustivity) {
        enclosingObject.splice.assertExhaustive(config.splice, path.splice, keyListExpr.splice)
      }
    }.tree
    val instantiation = Apply(instantiationCall, instantiationArgs)
    c.Expr[T](Block(List(conditionalAssertion), instantiation))
  }

  def extractMethodArgsFromConfig[T : c.WeakTypeTag](c: Context)(method: c.universe.MethodSymbol, companionObjectMaybe: Option[c.Symbol],
                                              config: c.Expr[Config], path: c.Expr[String], fail: String => Nothing): List[(c.Tree, c.Tree)] = {
    import c.universe._

    val decodedMethodName = method.name.decodedName.toString

    if (!method.isPublic) fail(s"'$decodedMethodName' method is not public")

    val enclosingObject = c.Expr[ArbitraryTypeReader](c.prefix.tree)

    method.paramLists.head.zipWithIndex map { case (param, index) =>
      val name = param.name.decodedName.toString
      val key = reify { path.splice + "." + enclosingObject.splice.mapParam(c.Expr[String](q"$name").splice) }.tree
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
