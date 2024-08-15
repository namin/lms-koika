package lms.koika

import scala.collection.immutable.Set
import scala.collection.immutable.Map

import lms.core.stub._
import lms.core.virtualize
import lms.collection.mutable._
import lms.macros.SourceContext
import lms.macros.RefinedManifest

@virtualize
class ImpTest extends TutorialFunSuite {
  val under = "imp_"

  import ImpLang._

  override def exec(label: String, code: String, suffix: String = "c") =
    super.exec(label, code, suffix)

  override def check(label: String, code: String, suffix: String = "c") =
    super.check(label, code, suffix)

  trait StateOps extends Dsl {
    trait AbstractRepState {
      def readVar(ident: String): Rep[Int]
      def writeVar(ident: String, v: Rep[Int]): Rep[Unit]

      def readMem(idx: Rep[Int]): Rep[Int]
      def writeMem(idx: Rep[Int], v: Rep[Int]): Rep[Unit]

      def exec(prg: List[Stmt]): Rep[Unit] = {
        for (stmt <- prg) {
          this.execS(stmt)
        }
      }

      def execS(s: Stmt): Rep[Unit] = s match {
        case Assign(id, e) => this.writeVar(id, this.evalE(e))
        case Skip => unit(())
        case IfThen(c, tthen, els) =>
          if (this.evalC(c)) {
            this.exec(tthen)
          }
          else {
            this.exec(els)
          }
        case While(c, body) =>
          while (this.evalC(c)) {
            this.exec(body)
          }
        case PrintT(t) => println(t)
        case PrintExp(e) => println(this.evalE(e))
      }

      def evalE(e: Expr): Rep[Int] = e match {
        case I(n) => n
        case V(id) => this.readVar(id)
        case Deref(e) => this.readMem(this.evalE(e))
        case Mul(e1, e2) => this.evalE(e1) * this.evalE(e2)
        case Add(e1, e2) => this.evalE(e1) + this.evalE(e2)
      }

      def evalC(c: Cond): Rep[Boolean] = c match {
        case T => true
        case F => false
        case Eq(e1, e2) => this.evalE(e1) == this.evalE(e2)
        case Le(e1, e2) => this.evalE(e1) <= this.evalE(e2)
        case Not(c) => !this.evalC(c)
        case And(c1, c2) => this.evalC(c1) && this.evalC(c2)
      }
    }
  }

  // TODO (cam): this is a hack to wrap up these two arrays into one logical
  // input.
  @CStruct
  case class ProgramStateT(vars: Array[Int], mem: Array[Int])

  trait InterpImpUntimed extends Dsl with StateOps with ArrayOps with ProgramStateTOps {
    class BasicState private (
      varLookup: Map[String, Int],
      vars: Rep[Array[Int]],
      mem: Rep[Array[Int]]
    ) extends AbstractRepState {
      def readVar(ident: String): Rep[Int] = vars(varLookup(ident))
      def writeVar(ident: String, v: Rep[Int]): Rep[Unit] = vars(varLookup(ident)) = v

      def readMem(idx: Rep[Int]): Rep[Int] = mem(idx)
      def writeMem(idx: Rep[Int], v: Rep[Int]): Rep[Unit] = mem(idx) = v

      def decompose(): (Rep[Array[Int]], Rep[Array[Int]]) = (vars, mem)
    }

    object BasicState {
      def init(prg: List[Stmt], st: Rep[ProgramStateT]): BasicState = {
        val prgVars = vars(prg)
        val varLookup = prgVars.toList.zipWithIndex.toMap
        new BasicState(varLookup, st.vars, st.mem)
      }
    }
  }

  abstract class DslDriverX[A:Manifest,B:Manifest] extends DslDriverC[A,B] { q =>
    val main: String = """
int main(int argc, char *argv[]) {
  if (argc != 2) {
    printf("usage: %s <arg>\n", argv[0]);
    return 0;
  }
  return 0;
}
"""

    override val codegen = new DslGenC with CCodeGenStruct {
      val IR: q.type = q

      override def emitAll(g: lms.core.Graph, name: String)(m1:Manifest[_],m2:Manifest[_]): Unit = {
        val ng = init(g)
        val efs = "" //quoteEff(g.block.ein)
        val stt = dce.statics.toList.map(quoteStatic).mkString(", ")
        prepareHeaders
        emitln("""
    |/*****************************************
    |Emitting C Generated Code
    |*******************************************/
    """.stripMargin)
        val src = run(name, ng)
        emitDefines(stream)
        emitHeaders(stream)
        emitDatastructures(stream)
        emitFunctionDecls(stream)
        emitFunctions(stream)
        emitInit(stream)
        emitln(s"\n/**************** $name ****************/")
        emit(src)
        emitln("""
    |/*****************************************
    |End of C Generated Code
    |*******************************************/
    |""".stripMargin)
        emit(main)
      }
    }
  }

  abstract class UntimedImpDriver
    extends DslDriverX[ProgramStateT, ProgramStateT]
    with InterpImpUntimed
  {
    val prog: List[Stmt]

    def snippet(s: Rep[ProgramStateT]): Rep[ProgramStateT] = {
      val ctx = BasicState.init(prog, s)
      ctx.exec(prog)
      val (vars, mem) = ctx.decompose()
      s.vars = vars
      s.mem = mem
      s
    }
  }

  /*
     result = 1;
     i = 0;
     while (result == 1 && i <= 5) {
       if (*i != *i+SECRET_OFFSET) {
         result = 0;
       }
       i = i + 1;
     }
   */
  val shortCircuitLoop: List[Stmt] =
    List(
      Assign("result", I(1)),
      Assign("i", I(1)),
      While(
        And(Eq(V("result"), I(1)), Le(V("i"), I(5))),
        List(
          IfThen(
            Not(Eq(
              Deref(V("i")),
              Deref(Add(V("i"), I(10)))
            )),
            List(Assign("result", I(0))),
            List(),
          ),
          Assign("i", Add(V("i"), I(1)))
        )
      ),
    )

  test("shortCircuit_untimed") {
    val snippet = new UntimedImpDriver {
      override val prog = shortCircuitLoop
    }
    check("shortCircuit_untimed", snippet.code)
  }
}
