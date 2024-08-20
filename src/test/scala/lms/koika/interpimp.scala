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

  val mem_size = 30;
  val secret_size = 5;
  val secret_offset = 20;

  // TODO (cam): this is a hack to wrap up these two arrays into one logical
  // input.
  @CStruct
  case class ProgramStateT(vars: Array[Int], mem: Array[Int])

  trait InterpImpUntimed extends Dsl
    with StateOps
    with ArrayOps
    with ProgramStateTOps
  {
    class State private (
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

    object State {
      def init(prg: List[Stmt], st: Rep[ProgramStateT]): State = {
        val prgVars = vars(prg)
        val varLookup = prgVars.toList.zipWithIndex.toMap
        new State(varLookup, st.vars, st.mem)
      }
    }
  }

  @CStruct
  case class TimedStateT(
    vars: Array[Int],
    mem: Array[Int],
    timer: Int
  )

  trait InterpImpTimed extends Dsl
    with StateOps
    with ArrayOps
    with TimedStateTOps
  {
    class State private (
      varLookup: Map[String, Int],
      inner: Rep[TimedStateT]
    ) extends AbstractRepState {
      def readVar(ident: String): Rep[Int] = inner.vars(varLookup(ident))
      def writeVar(ident: String, v: Rep[Int]): Rep[Unit] = inner.vars(varLookup(ident)) = v

      def readMem(idx: Rep[Int]): Rep[Int] = inner.mem(idx)
      def writeMem(idx: Rep[Int], v: Rep[Int]): Rep[Unit] = inner.mem(idx) = v

      override def execS(s: Stmt): Rep[Unit] = {
        inner.timer += 1
        super.execS(s)
      }

      override def evalE(e: Expr): Rep[Int] = {
        e match {
          case I(n) => ()
          case V(id) => ()
          case Deref(e) => ()
          case Mul(e1, e2) => inner.timer += 1
          case Add(e1, e2) => inner.timer += 1
        }
        super.evalE(e)
      }

      override def evalC(c: Cond): Rep[Boolean] = {
        c match {
          case T => ()
          case F => ()
          case Eq(e1, e2) => inner.timer += 1
          case Le(e1, e2) => inner.timer += 1
          case Not(c) => inner.timer += 1
          case And(c1, c2) => inner.timer += 1
        }
        super.evalC(c)
      }

      def unwrap(): Rep[TimedStateT] = inner
    }

    object State {
      def init(prg: List[Stmt], st: Rep[TimedStateT]): State = {
        val prgVars = vars(prg)
        val varLookup = prgVars.toList.zipWithIndex.toMap
        new State(varLookup, st)
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

    def dyn(): String

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
        emit(dyn)
        emit(main)
      }
    }
  }

  abstract class UntimedImpDriver
    extends DslDriverX[ProgramStateT, ProgramStateT]
    with InterpImpUntimed
  {
    val prog: List[Stmt]

    def dyn() = ""

    def snippet(s: Rep[ProgramStateT]): Rep[ProgramStateT] = {
      val ctx = State.init(prog, s)
      ctx.exec(prog)
      val (vars, mem) = ctx.decompose()
      s.vars = vars
      s.mem = mem
      s
    }
  }

  abstract class TimedImpDriver
    extends DslDriverX[TimedStateT, TimedStateT]
    with InterpImpTimed
  {
    val prog: List[Stmt]

    def dyn(): String = {
      val num_vars = vars(prog).size

      s"""
#define MEM_SIZE $mem_size
#define SECRET_SIZE $secret_size
#define SECRET_OFFSET $secret_offset
int bounded(int low, int high) {
  int x = nondet_uint();
  if (x < low) {
    x = low;
  }
  if (x > high) {
    x = high;
  }
  return x;
}
void init(struct TimedStateT *st) {
  st->timer = 0;
  st->mem = calloc(sizeof(int), MEM_SIZE);
  st->vars = calloc(sizeof(int), $num_vars);
}
"""
    }

    override val main = """
int main(int argc, char* argv[]) {
  struct TimedStateT s1;
  init(&s1);
  struct TimedStateT s2;
  init(&s2);

  int i;
  int x;

  // initialize input
  // TODO (cwong): this is ugly
  for (i=0; i<SECRET_SIZE; i++) {
    x = bounded(0, 20);
    s1.mem[i] = x;
    s2.mem[i] = x;
  }

  // initialize secret
  for (i=0; i<SECRET_SIZE; i++) {
    s1.mem[i+SECRET_OFFSET] = bounded(0, 20);
    s2.mem[i+SECRET_OFFSET] = bounded(0, 20);
  }

  struct TimedStateT s1_ = Snippet(s1);
  struct TimedStateT s2_ = Snippet(s2);
  __CPROVER_assert(s1_.timer==s2_.timer, "timing leak");
  return 0;
}
"""

    def snippet(s: Rep[TimedStateT]): Rep[TimedStateT] = {
      val ctx = State.init(prog, s)
      ctx.exec(prog)
      ctx.unwrap()
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
        And(Eq(V("result"), I(1)), Le(V("i"), I(secret_size))),
        List(
          IfThen(
            Not(Eq(
              Deref(V("i")),
              Deref(Add(V("i"), I(secret_offset)))
            )),
            List(Assign("result", I(0))),
            List(),
          ),
          Assign("i", Add(V("i"), I(1)))
        )
      ),
    )

  test("sanity_check") {
    val snippet = new UntimedImpDriver {
      override val prog = shortCircuitLoop
    }
    check("sanity_check", snippet.code)
  }

  test("shortCircuit_timed") {
    val snippet = new TimedImpDriver {
      override val prog = shortCircuitLoop
    }
    check("shortCircuit_timed", snippet.code)
  }
}
