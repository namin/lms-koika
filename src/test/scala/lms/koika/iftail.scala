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

abstract class IfTailCDslDriver[A:Manifest,B:Manifest] extends DslSnippet[A,B] with DslExp { q =>
  val codegen = new DslGenC {
    val IR: q.type = q
  }

  Adapter.typeMap = new scala.collection.mutable.HashMap[lms.core.Backend.Exp, Manifest[_]]()
  Adapter.funTable = Nil

  lazy val g: Graph = time("staging") { Adapter.program(Adapter.g.reify(x => Unwrap(wrapper(Wrap[A](x))))) }

  // Transformation
  val transformer = new IfTailTransformer { g = Adapter.mkGraphBuilder() }

  lazy val tg: Graph = time("transforming") { transformer.transform(g) }

  lazy val code: String = {
    val source = new java.io.ByteArrayOutputStream()
    val gen = new ExtendedCCodeGen
    gen.typeMap = Adapter.typeMap
    gen.stream = new java.io.PrintStream(source)
    gen.emitAll(tg, "Snippet")(manifest[A],manifest[B])
    source.toString
  }

  //def eval(x: A): B = {val f1 = f; time("eval")(f1(x))}

  //lazy val f = { val c1 = code; time("scalac") { Global.sc.compile[A,B]("Snippet", c1, Nil) }}

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

  test("testc") {
    val driver = new IfTailCDslDriver[Int, Int] {
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
    check("testc", driver.code, "c")
  }
}

/*
@virtualize
class InterpCaIfTailTest extends TutorialFunSuite {
  val under = "interpca_iftail_" 

  override def exec(label: String, code: String, suffix: String = "c") =
    super.exec(label, code, suffix)

  override def check(label: String, code: String, suffix: String = "c") =
    super.check(label, code, suffix)

  type stateT = Array[Int]
  trait InterpCaIfTail extends Dsl with lms.thirdparty.CLibs {
    def state_pc(s: Rep[stateT]): Rep[Int] =
      s(0)
    def set_state_pc(s: Rep[stateT], pc: Rep[Int]): Rep[Unit] =
      s(0) = pc

    def state_reg(s: Rep[stateT], i: Rep[Int]): Rep[Int] =
      s(6+i)
    def set_state_reg(s: Rep[stateT], i: Rep[Int], v: Rep[Int]): Rep[Unit] =
      s(6+i) = v

    def state_epoch(s: Rep[stateT]): Rep[Int] =
      s(1)
    def set_state_epoch(s: Rep[stateT],  v: Rep[Int]): Rep[Unit] =
      s(1) = v

    def state_f2d_valid(s: Rep[stateT]): Rep[Int] =
      s(2)
    def set_state_f2d_valid(s: Rep[stateT],  v: Rep[Int]): Rep[Unit] =
      s(2) = v

    def state_f2d_pc(s: Rep[stateT]): Rep[Int] =
      s(3)
    def set_state_f2d_pc(s: Rep[stateT],  v: Rep[Int]): Rep[Unit] =
      s(3) = v

    def state_f2d_ppc(s: Rep[stateT]): Rep[Int] =
      s(4)
    def set_state_f2d_ppc(s: Rep[stateT],  v: Rep[Int]): Rep[Unit] =
      s(4) = v


    def state_f2d_epoch(s: Rep[stateT]): Rep[Int] =
      s(5)
    def set_state_f2d_epoch(s: Rep[stateT],  v: Rep[Int]): Rep[Unit] =
      s(5) = v

      // Here the intention is that the following function is not a getter, but the predictor function
    def state_btb(s: Rep[stateT]): Rep[Int] =
      libFunction[Int]("state_btb", Unwrap(s))(Seq(0), Seq(), Set[Int]())

      // Here the intention is that the following function is not a setter, but the update function
    def set_state_btb(s: Rep[stateT],  v: Rep[Int], pc : Rep[Int]): Rep[Unit] =
      libFunction[Unit]("set_state_btb", Unwrap(s), Unwrap(v), Unwrap(pc))(Seq(0,1,2), Seq(0), Set[Int]())

    abstract sealed class Instruction
    case class Add(rd: Int, rs1: Int, rs2: Int) extends Instruction
    case class Branch(rs: Int, target: Int) extends Instruction

    type State = (
      Array[Instruction],
      Rep[stateT]
    )

    val prog: Array[Instruction] = List(Add(0, 0, 0), Branch(0, 0)).toArray

    def id(a: Rep[Int]) = a

    def fetch(s: Rep[stateT]): Unit = {
      // We should log in somewhere the sequence of pc that we generate here
      if ( state_f2d_valid(s) == unit(0)) {
        set_state_f2d_valid(s,unit(1))
        set_state_f2d_epoch(s, state_epoch(s))
        val predpc = state_btb(s)
        val pc = state_pc(s)
        set_state_f2d_pc(s, pc)
        set_state_f2d_ppc(s, predpc)
        set_state_pc(s, predpc)
      }
    }

    def execute(ins: Array[Instruction], s: Rep[stateT]): Unit = {
      if (state_f2d_valid(s) == unit(1)) {
        if (state_f2d_epoch(s) == state_epoch(s)) {
          var pc = state_f2d_pc(s)
          var ppc = state_f2d_ppc(s)
          set_state_f2d_valid(s,unit(0))
          for (ipc <- (0 until ins.size): Range) {
            if (pc == unit(ipc)) {
              ins(ipc) match {
                case Add(rd, rs1, rs2) => {
                  set_state_reg(s, rd, state_reg(s, rs1) + state_reg(s, rs2))
                  if (ppc != unit(ipc + 1)) {
                    set_state_pc(s, ipc+1)
                    set_state_epoch(s, ~(state_epoch(s)))
                  } 
                }
                case Branch(rs, target) => {
                  set_state_btb(s, state_reg(s,rs), ipc)
                  if (state_reg(s, rs) == unit(0)) {
                    if (ppc != unit(target)) {
                      set_state_pc(s, target)
                      set_state_epoch(s, ~(state_epoch(s)))
                    } 
                  } else {
                    if (ppc != ipc + 1) {
                      set_state_pc(s, ipc + 1)
                      set_state_epoch(s, ~(state_epoch(s)))
                    } 
                  }
                }
              }
            }
          }
        }
        else {
          set_state_f2d_valid(s,unit(0))
        }
      }
    }

    def step_aux(ins: Array[Instruction], s: Rep[stateT], pc: Int): Unit = {
      set_state_pc(s, pc+1)
      ins(pc) match {
        case Add(rd, rs1, rs2) =>
          set_state_reg(s, rd, state_reg(s, rs1) + state_reg(s, rs2))
        case Branch(rs, target) => {
          if (state_reg(s, rs) == unit(0))
            set_state_pc(s, target)
        }
      }
    }

    def step(ins: Array[Instruction], s: Rep[stateT]): Unit = {
      val pc = state_pc(s)
      for (i <- (0 until ins.size): Range) {
        if (pc == unit(i))
          step_aux(ins, s, i)
      }
    }
  }

  abstract class DslDriverX[A:Manifest,B:Manifest] extends DslDriverC[A,B] { q =>
    override val codegen = new DslGenC with lms.thirdparty.CCodeGenLibs {
      val IR: q.type = q

      registerHeader("\"state.h\"")
    }
  }

  test("interp 1") {
    val snippet = new DslDriverX[Int,Int] with InterpCaIfTail {
      def snippet(a: Rep[Int]) = id(id(a))
    }
    check("1", snippet.code)
  }

  test("interp 2") {
    val snippet = new DslDriverX[stateT,stateT] with InterpCaIfTail {
      def snippet(s: Rep[stateT]) = {
        step_aux(prog, s, 0)
        s
      }
    }
    check("2", snippet.code)
  }

  test("interp 3") {
    val snippet = new DslDriverX[stateT,stateT] with InterpCaIfTail {
      def snippet(s: Rep[stateT]) = {
        step(prog, s)
        s
      }
    }
    check("3", snippet.code)
  }

  test("interp 4") {
    val snippet = new DslDriverX[stateT,stateT] with InterpCaIfTail {
      def snippet(s: Rep[stateT]) = {
        set_state_pc(s, 0)
        step(prog, s)
        s
      }
    }
    // TODO: this no longer optimizes.
    check("4", snippet.code)
  }

  test("interp 5") {
    val snippet = new DslDriverX[stateT,stateT] with InterpCaIfTail {
      def snippet(s: Rep[stateT]) = {
        set_state_pc(s, 0)
        step(prog, s)
        step(prog, s)
        step(prog, s)
        step(prog, s)
        s
      }
    }
    // this program should simplify the branches, but it does not
    check("5", snippet.code)
  }
  test("interp 6") {
    val snippet = new DslDriverX[stateT,stateT] with InterpCaIfTail {
      def snippet(s: Rep[stateT]) = {
        set_state_pc(s, 0)
        fetch(s)
        execute(prog,s)
        fetch(s)
        execute(prog,s)
        fetch(s)
        execute(prog,s)
        fetch(s)
        execute(prog,s)
        s
      }
    }
    // this program should simplify the branches, but it does not
    check("6", snippet.code)
  }
}
 */
