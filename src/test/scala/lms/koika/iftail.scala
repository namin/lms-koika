package lms.koika

import lms.core._
import lms.core.stub._
import lms.core.virtualize
import lms.macros.SourceContext
import lms.core.utils.time
import lms.core.Backend._

abstract class IfTailTransformer extends CPSTransformer {
  override def traverse(n: Node)(k: => Exp): Exp = n match {
    case Node(f,"?",c::(a:Block)::(b:Block)::_,es) =>
      val kIf = (v:Exp) => withSubstScope(f)(v)(k)
      withSubst(f) {
        reflectHelper(es, "?", c match {case c: Exp => transform(c); case c => ???},
          transform(a)(kIf), transform(b)(kIf))
      }
    case _ => super.traverse(n)(k)
  }
}

abstract class IfTailDslDriver[A:Manifest,B:Manifest] extends DslSnippet[A,B] with DslExp with CompileScala { q =>
  val codegen = new DslGen {
    val IR: q.type = q
  }

  Adapter.typeMap = new scala.collection.mutable.HashMap[lms.core.Backend.Exp, Manifest[_]]()
  Adapter.funTable = Nil

  lazy val g: Graph = time("staging") { Adapter.program(Adapter.g.reify(x => Unwrap(wrapper(Wrap[A](x))))) }

  // Transformation
  val transformer = new IfTailTransformer { g = Adapter.mkGraphBuilder() }

  lazy val tg: Graph = time("transforming") { transformer.transform(g) }

  lazy val code: String = utils.captureOut{ (new ScalaCodeGen).emitAll(tg)(manifest[A],manifest[B]) }

  def eval(x: A): B = {val f1 = f; time("eval")(f1(x))}

  lazy val f = { val c1 = code; time("scalac") { Global.sc.compile[A,B]("Snippet", c1, Nil) }}

}

@virtualize
class IfTail extends TutorialFunSuite {
  val under = "iftail_"
 
  test("test") {
    val driver = new IfTailDslDriver[Int, Int] {
      @virtualize
      def snippet(arg: Rep[Int]): Rep[Int] = {
        val x = if (arg == 0) {
          println("a")
          arg + 1
        } else {
          println("b")
          arg + 2
        }
        println(x)
        arg
      }
    }
    check("test", driver.code)
  }
}
