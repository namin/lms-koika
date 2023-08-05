package lms.koika

import lms.core.stub._
import lms.core.virtualize
import lms.macros.SourceContext
import lms.macros.RefinedManifest

import lms.collection.mutable._

@virtualize
class InterpCcStructTest extends TutorialFunSuite {
  val under = "interpcc_struct_"

  override def exec(label: String, code: String, suffix: String = "c") =
    super.exec(label, code, suffix)

  override def check(label: String, code: String, suffix: String = "c") =
    super.check(label, code, suffix)

  // TODO (cwong): it would be nice to be able to extend this, instead of
  // needing to have all necessary fields
  @CStruct
  case class stateT
    // TODO (cwong): These [Array]s are currently raw int pointers, not
    // length-checked C arrays.
    ( regs: Array[Int]
    , saved_regs: Array[Int]
    , mem: Array[Int]
    , cache_key: Int
    , cache_val: Int
    , timer: Int
    )

  trait InterpCc extends Dsl with stateTOps {
    def state_reg(s: Rep[stateT], i: Rep[Int]): Rep[Int] =
      s.regs(i)
    def set_state_reg(s: Rep[stateT], i: Rep[Int], v: Rep[Int]): Rep[Unit] =
      s.regs(i) = v
    def state_mem(s: Rep[stateT], i: Rep[Int]): Rep[Int] =
      s.mem(i)
    def set_state_mem(s: Rep[stateT], i: Rep[Int], v: Rep[Int]): Rep[Unit] =
      s.mem(i) = v

    abstract sealed class Instruction
    case class Add(rd: Int, rs1: Int, rs2: Int) extends Instruction
    case class Branch(rs: Int, target: Int) extends Instruction
    case class Load(rd: Int, im: Int, rs: Int) extends Instruction
    case class Store(rd: Int, im: Int, rs: Int) extends Instruction

    val prog: Vector[Instruction]

    lazy val cache: Array[Option[Rep[stateT => stateT]]] = (for (p <- prog) yield None).toArray

    def useCache: Boolean = true
    def call(i: Int, s: Rep[stateT]): Rep[stateT] =
      if (useCache) {
        if (i < cache.length) {
          val f = cache(i) match {
            case None => {
              val f = topFun { (s: Rep[stateT]) => execute(i, s) }
              cache(i) = Some(f)
              f
            }
            case Some(f) => f
          }
          f(s)
        } else {
          s
        }
      } else {
        execute(i, s)
      }

    def execute(i: Int, s: Rep[stateT]): Rep[stateT] = if (i < prog.length) {
      prog(i) match {
        case Add(rd, rs1, rs2) => {
          set_state_reg(s, rd, state_reg(s, rs1) + state_reg(s, rs2))
          call(i+1, s)
        }
        case Branch(rs, target) => {
          if (state_reg(s, rs) == unit(0)) {
            call(target, s)
          } else {
            call(i+1, s)
          }
        }
        case Load(rd, im, rs) => {
          set_state_reg(s, rd, state_mem(s, im+state_reg(s, rs)))
          call(i+1, s)
        }
        case Store(rd, im, rs) => {
          set_state_mem(s, im+state_reg(s, rs), state_reg(s, rd))
          call(i+1, s)
        }
      }
    } else {
      s
    }
  }

  trait InterpCcCache extends InterpCc {
    def state_cache_key(s: Rep[stateT]): Rep[Int] =
      s.cache_key
    def state_cache_val(s: Rep[stateT]): Rep[Int] =
      s.cache_val
    def set_state_cache(s: Rep[stateT], key: Rep[Int], v: Rep[Int]): Rep[Unit] = {
      s.cache_key = key
      s.cache_val = v
    }
    override def state_mem(s: Rep[stateT], i: Rep[Int]): Rep[Int] = {
      if (state_cache_key(s) == i) {
        state_cache_val(s)
      } else {
        val v = s.mem(i)
        set_state_cache(s, i, v)
        v
      }
    }
    override def set_state_mem(s: Rep[stateT], i: Rep[Int], v: Rep[Int]): Rep[Unit] = {
      s.mem(i) = v
      set_state_cache(s, i, v)
    }
  }

  trait InterpCcSpeculative extends InterpCc {
    def saveForRollback(s: Rep[stateT], x: Instruction): Rep[Unit] = {}
    def rollback(s: Rep[stateT]): Rep[Unit] = {}
    def resetSaved(): Unit = {}
    var inBranch: Option[Branch] = None
    override def useCache: Boolean = inBranch == None
    override def execute(i: Int, s: Rep[stateT]): Rep[stateT] = inBranch match {
      case None => {
        if (i < prog.length) {
          prog(i) match {
            case Branch(rs, target) if target > i => {
              inBranch = Some(Branch(rs, target))
              call(i+1, s)
            }
            case _ => super.execute(i, s)
          }
        } else {
          s
        }
      }
      case Some(Branch(rs, target)) => {
        if (i == target) {
          inBranch = None
          if (state_reg(s, rs) == unit(0)) {
            rollback(s)
          }
          resetSaved()
        }
        if (i < prog.length) {
          prog(i) match {
            case Load(rd, im, r) if rd != rs => {
              saveForRollback(s, Load(rd, im, r))
              super.execute(i, s)
            }
            case _ => {
              inBranch = None
              if (state_reg(s, rs) == unit(0)) {
                rollback(s)
                call(target, s)
              } else {
                super.execute(i, s)
              }
              resetSaved();
              s
            }
          }
        } else {
          s
        }
      }
    }
  }

  trait InterpCcRollback extends InterpCcSpeculative {
    val savedRegisters = scala.collection.mutable.Set[Int]()

    def save_state_reg(s: Rep[stateT], rd: Rep[Int], v: Rep[Int]): Rep[Unit] = {
      s.saved_regs(rd) = v
    }

    def saved_state_reg(s: Rep[stateT], rd: Rep[Int]): Rep[Int] = {
      s.saved_regs(rd)
    }

    override def saveForRollback(s: Rep[stateT], x: Instruction): Rep[Unit] = x match {
      case Load(rd, _, _) => {
        if (!savedRegisters.contains(rd)) {
          save_state_reg(s, rd, state_reg(s, rd))
          savedRegisters += rd
          unit(())
        }
      }
      case _ => unit(())
    }
    override def rollback(s: Rep[stateT]): Rep[Unit] = {
      for (rd <- savedRegisters) {
        set_state_reg(s, rd, saved_state_reg(s, rd))
      }
    }
    override def resetSaved(): Unit = { savedRegisters.clear() }
  }

  trait InterpCcTimed extends InterpCcSpeculative with InterpCcCache {
    val TIME = 6
    def tick(s: Rep[stateT]): Rep[Unit] =
      s.timer += 1

    override def set_state_cache(s: Rep[stateT], key: Rep[Int], v: Rep[Int]) = {
      tick(s)
      tick(s)
      super.set_state_cache(s, key, v)
    }

    override def execute(i: Int, s: Rep[stateT]): Rep[stateT] = {
      tick(s)
      super.execute(i, s)
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

  trait TimedNiDriver extends DslDriverX[stateT,stateT] with InterpCcTimed {
      override val main = """
#define NUM_REGS 3
#define MEM_SIZE 30
#define SECRET_SIZE 20
#define SECRET_OFFSET 10
int init(struct stateT *s) {
  s->regs = calloc(sizeof(int), NUM_REGS);
  s->cache_key = -1;
  s->cache_val = 0;
  s->timer = 0;
  s->mem = calloc(sizeof(int), NUM_REGS);
  for (int i=0; i<MEM_SIZE; i++) {
    s->mem[i] = 0;
  }

  return 0;
}
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
int main(int argc, char* argv[]) {
  struct stateT s1;
  init(&s1);
  struct stateT s2;
  init(&s2);
  int x = bounded(0, 20);
  s1.regs[0] = x;
  s2.regs[0] = x;
  int i;
  for (i=0; i<SECRET_SIZE; i++) {
    s1.mem[i+SECRET_OFFSET] = bounded(0, 20);
    s2.mem[i+SECRET_OFFSET] = bounded(0, 20);
  }
  struct stateT s1_ = Snippet(s1);
  struct stateT s2_ = Snippet(s2);
  __CPROVER_assert(s1_.timer==s2_.timer, "timing leak");
  return 0;
}
"""

    def snippet(s: Rep[stateT]): Rep[stateT] = call(0, s)
  }

  test("interp 2sctr ni") {
    val snippet = new TimedNiDriver with InterpCcRollback {
      override val prog =  Vector(Branch(0, 3), Load(1, 0, 0), Load(2, 4, 1))
    }
    check("2sctr_ni", snippet.code)
  }
}
