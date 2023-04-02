package lms.koika

import lms.core.stub._
import lms.core.virtualize
import lms.macros.SourceContext

@virtualize
class InterpCcTest extends TutorialFunSuite {
  val under = "interpcc_"

  override def exec(label: String, code: String, suffix: String = "c") =
    super.exec(label, code, suffix)

  override def check(label: String, code: String, suffix: String = "c") =
    super.check(label, code, suffix)

  type stateT = Array[Int]
  trait InterpCcCache extends InterpCc {
    val CACHE_KEY = 4
    val CACHE_VAL = 5
    override val MEM = 10
    def state_cache_key(s: Rep[stateT]): Rep[Int] =
      s(CACHE_KEY)
    def state_cache_val(s: Rep[stateT]): Rep[Int] =
      s(CACHE_VAL)
    def set_state_cache(s: Rep[stateT], key: Rep[Int], v: Rep[Int]): Rep[Unit] = {
      s(CACHE_KEY) = key
      s(CACHE_VAL) = v
    }
    override def state_mem(s: Rep[stateT], i: Rep[Int]): Rep[Int] = {
      val key = i+MEM
      if (state_cache_key(s) == key) {
        state_cache_val(s)
      } else {
        val v = s(key)
        set_state_cache(s, key, v)
        v
      }
    }
  }

  trait InterpCc extends Dsl {
    val MEM = 4
    def state_reg(s: Rep[stateT], i: Rep[Int]): Rep[Int] =
      s(i)
    def set_state_reg(s: Rep[stateT], i: Rep[Int], v: Rep[Int]): Rep[Unit] =
      s(i) = v
    def state_mem(s: Rep[stateT], i: Rep[Int]): Rep[Int] =
      s(i+MEM)
    def set_state_mem(s: Rep[stateT], i: Rep[Int], v: Rep[Int]): Rep[Unit] =
      s(i+MEM) = v

    abstract sealed class Instruction
    case class Add(rd: Int, rs1: Int, rs2: Int) extends Instruction
    case class Branch(rs: Int, target: Int) extends Instruction
    case class Load(rd: Int, im: Int, rs: Int) extends Instruction
    case class Store(rd: Int, im: Int, rs: Int) extends Instruction

    val prog: Vector[Instruction]

    lazy val cache: Array[Option[Rep[stateT => Unit]]] = (for (p <- prog) yield None).toArray

    def useCache: Boolean = true
    def call(i: Int, s: Rep[stateT]): Rep[Unit] = if (useCache) {
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
        unit(())
      }
    } else {
      execute(i, s)
    }

    def execute(i: Int, s: Rep[stateT]): Rep[Unit] = if (i < prog.length) {
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
    }
  }

  trait InterpCcSpeculative extends InterpCc {
    var inBranch: Option[Branch] = None
    override def useCache: Boolean = inBranch == None
    override def execute(i: Int, s: Rep[stateT]): Rep[Unit] = inBranch match {
      case None => {
        if (i < prog.length) {
          prog(i) match {
            case Branch(rs, target) if target > i => {
              inBranch = Some(Branch(rs, target))
              call(i+1, s)
            }
            case _ => super.execute(i, s)
          }
        }
      }
      case Some(Branch(rs, target)) => {
        if (i == target) {
          inBranch = None
        }
        if (i < prog.length) {
          prog(i) match {
            case Load(rd, im, r) if rd != rs => {
              super.execute(i, s)
            }
            case _ => {
              inBranch = None
              if (state_reg(s, rs) == unit(0)) {
                call(target, s)
              } else {
                super.execute(i, s)
              }
            }
          }
        }
      }
    }
  }

  trait InterpCcTimed extends InterpCcSpeculative with InterpCcCache {
    val TIME = 6
    def tick(s: Rep[stateT]): Rep[Unit] =
      s(TIME) += 1

    override def set_state_cache(s: Rep[stateT], key: Rep[Int], v: Rep[Int]) = {
      tick(s)
      tick(s)
      super.set_state_cache(s, key, v)
    }

    override def execute(i: Int, s: Rep[stateT]): Rep[Unit] = {
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

    override val codegen = new DslGenC {
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
        emitFunctionDecls(stream)
        emitDatastructures(stream)
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

  test("interp 1") {
    val snippet = new DslDriverX[stateT,Unit] with InterpCc {
      override val prog =  Vector(Add(0, 0, 0), Branch(0, 0))
      def snippet(s: Rep[stateT]): Rep[Unit] = call(0, s)
    }
    check("1", snippet.code)
  }

  test("interp 1s") {
    val snippet = new DslDriverX[stateT,Unit] with InterpCcSpeculative {
      override val prog =  Vector(Add(0, 0, 0), Branch(0, 0))
      def snippet(s: Rep[stateT]): Rep[Unit] = call(0, s)
    }
    check("1", snippet.code)
  }

  test("interp 2") {
    val snippet = new DslDriverX[stateT,Unit] with InterpCc {
      override val prog =  Vector(Branch(0, 3), Load(1, 0, 0), Load(2, 4, 1))
      def snippet(s: Rep[stateT]): Rep[Unit] = call(0, s)
    }
    check("2", snippet.code)
  }

    test("interp 2s") {
    val snippet = new DslDriverX[stateT,Unit] with InterpCcSpeculative {
      override val prog =  Vector(Branch(0, 3), Load(1, 0, 0), Load(2, 4, 1))
      def snippet(s: Rep[stateT]): Rep[Unit] = call(0, s)
    }
    check("2s", snippet.code)
  }

  test("interp 2sc") {
    val snippet = new DslDriverX[stateT,Unit] with InterpCcSpeculative with InterpCcCache {
      override val prog =  Vector(Branch(0, 3), Load(1, 0, 0), Load(2, 4, 1))
      def snippet(s: Rep[stateT]): Rep[Unit] = call(0, s)
    }
    check("2sc", snippet.code)
  }

  test("interp 2sct") {
    val snippet = new DslDriverX[stateT,Unit] with InterpCcTimed {
      override val main = """
int init(int* s) {
  for (int i=0; i<100; i++) {
    s[i] = 0;
  }
  return 0;
}
int main(int argc, char* argv[]) {
  int s1[100];
  init(s1);
  s1[0] = 5;
  s1[15] = 1;
  int s2[100];
  init(s2);
  s2[0] = 5;
  Snippet(s1);
  Snippet(s2);
  __CPROVER_assert(s1[6]==s2[6], "timing leak");
  return 0;
}
"""
      override val prog =  Vector(Branch(0, 3), Load(1, 0, 0), Load(2, 4, 1))
      def snippet(s: Rep[stateT]): Rep[Unit] = call(0, s)
    }
    check("2sct", snippet.code)
  }

  test("interp 2sct alt") {
    val snippet = new DslDriverX[stateT,Unit] with InterpCcTimed {
      override val main = """
int init(int* s) {
  for (int i=0; i<100; i++) {
    s[i] = 0;
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
  int s1[100];
  init(s1);
  int x = bounded(0, 20);
  s1[0] = x;
  int i = 10+bounded(0, 20);
  s1[i] = 1;
  int s2[100];
  init(s2);
  s2[0] = x;
  Snippet(s1);
  Snippet(s2);
  __CPROVER_assert(s1[6]==s2[6], "timing leak");
  return 0;
}
"""
      override val prog =  Vector(Branch(0, 3), Load(1, 0, 0), Load(2, 4, 1))
      def snippet(s: Rep[stateT]): Rep[Unit] = call(0, s)
    }
    check("2sct_alt", snippet.code)
  }

}
