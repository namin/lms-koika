package lms.collection.mutable

import lms.core._
import lms.util._
import lms.core.stub._
import lms.core.Backend._
import lms.core.virtualize
import lms.core.utils.time
import lms.macros.SourceContext
import lms.macros.RefinedManifest


import language.experimental.macros
import scala.annotation.StaticAnnotation
import scala.reflect.macros.whitebox.Context
import scala.util.matching.Regex

trait StructOps extends Base with ArrayOps {
  object StructOpsImpl {
    // TODO: do we need a better constraint on T?
    def readField[T: RefinedManifest, U: Manifest](p: Rep[T], field: String): Rep[U] =
      p match {
        case Wrap(_, provenance) =>
          Wrap[U](Adapter.g.reflectRead("struct_get", Unwrap(p), Unwrap(field))(Unwrap(p)), Unwrap(p)::provenance)
      }

    def writeField[T: RefinedManifest, U: Manifest](p: Rep[T], field: String, v: Rep[U]): Unit =
      p match {
        case Wrap(_, provenance) =>
          Adapter.g.reflectWrite("struct_set", Unwrap(p), Unwrap(field), Unwrap(v))((Unwrap(p)::provenance):_*)
      }
  }
}

object CStruct_Impl {
  def impl(c: Context)(annottees: c.Expr[Any]*): c.Expr[Any] = {
    import c.universe._

    val List(a) = annottees
    a.tree match {
      case q"case class $name(..${fields: Seq[ValDef]})" =>
        val manifestName = internal.reificationSupport.freshTermName(name.toString+"Manifest")
        // XXX cwong: This can't be fresh, because we need it to have a predictable name
        // (so the end-user can actually use it). Of course, that runs the risk of actually
        // shadowing something. What to do...?
        val opsTraitName = TypeName(name.toString+"Ops")
        val accessorClassName = internal.reificationSupport.freshTypeName(name.toString+"Accessors")
        val fieldDecls = fields.map { f => q"""(${f.name.toString}, manifest[${f.tpt}])""" }
        val getters = fields.map { f =>
          q"""def ${f.name}: Rep[${f.tpt}] =
            StructOpsImpl.readField[$name, ${f.tpt}](p, ${f.name.toString})"""
        }
        val setters = fields.map { f =>
          val setter = TermName(f.name + "_$eq")
          q"""def $setter(v: Rep[${f.tpt}]): Unit =
            StructOpsImpl.writeField[$name, ${f.tpt}](p, ${f.name.toString}, v)"""
        }
        val res = c.Expr(q"""
          case class $name(..$fields)
          implicit val $manifestName = new RefinedManifest[$name] {
            def fields: List[(String, Manifest[_])] = List(..$fieldDecls)
            def runtimeClass = classOf[$name]
            override def name = Some(${name.toString})
          }
          trait $opsTraitName extends StructOps {
            implicit class $accessorClassName(p: Rep[$name]) {
              ..$getters
              ..$setters
            }
          }
        """)
        res
    }
  }
}

class CStruct extends StaticAnnotation {
  def macroTransform(annottees: Any*): Any = macro CStruct_Impl.impl
}

trait CCodeGenStruct extends ExtendedCCodeGen {
  override def traverse(n: Node): Unit = n match {
    case n @ Node(s, "reffield_set", List(ptr, Const(field: String), v), _) =>
      shallowP(ptr, precedence("reffield_get"))
      esln"->$field = $v;"
    case n @ Node(s, "struct_set", List(ptr, Const(field: String), v), _) =>
      shallowP(ptr, precedence("struct_get"))
      esln".$field = $v;"
    case n @ Node(s, "local_struct", Nil, _) =>
      val tpe = remap(typeMap.getOrElse(s, manifest[Unknown]))
      emitln(s"$tpe ${quote(s)} = { 0 };") // FIXME: uninitialized? or add it as argument?
    case _ => super.traverse(n)
  }

  override def shallow(n: Node): Unit = n match {
    case n @ Node(s, "ref_new", List(v), _) =>
      emit("&"); shallowP(v, precedence("ref_new"))
    case n @ Node(s, "reffield_get", List(ptr, Const(field: String)), _) =>
      shallowP(ptr, precedence("reffield_get")); emit("->"); emit(field)
    case n @ Node(s, "struct_get", List(ptr, Const(field: String)), _) =>
      shallowP(ptr, precedence("struct_get")); emit("."); emit(field)
    case n @ Node(s, "deref", List(ptr), _) =>
      es"*$ptr"
    case _ => super.shallow(n)
  }
}
