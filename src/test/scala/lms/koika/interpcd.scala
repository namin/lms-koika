package lms.koika

import lms.core.stub._
import lms.core.virtualize
import lms.macros.SourceContext

@virtualize
class InterpCdTest extends TutorialFunSuite {
  val under = "interpcd_"

  override def exec(label: String, code: String, suffix: String = "c") =
    super.exec(label, code, suffix)

  override def check(label: String, code: String, suffix: String = "c") =
    super.check(label, code, suffix)

  type stateT = Array[Int]
  trait InterpCdCache extends InterpCd {
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
    override def set_state_mem(s: Rep[stateT], i: Rep[Int], v: Rep[Int]): Rep[Unit] = {
      val key = i+MEM
      s(key) = v
      set_state_cache(s, key, v)
    }
  }

  trait InterpCd extends Dsl {
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

    def call(init: Rep[Int], s: Rep[stateT]): Rep[Unit] = {
      var pc = init
      while (unit(0) <= pc && pc < unit(prog.length)) {
        for (i <- (0 until prog.length): Range) {
          if (i == pc) {
            pc = execute(i, s)
          }
        }
      }
    }

    def execute(i: Int, s: Rep[stateT]): Rep[Int] =
      prog(i) match {
        case Add(rd, rs1, rs2) => {
          set_state_reg(s, rd, state_reg(s, rs1) + state_reg(s, rs2))
          i+1
        }
        case Branch(rs, target) => {
          if (state_reg(s, rs) == unit(0)) {
            target
          } else {
            i+1
          }
        }
        case Load(rd, im, rs) => {
          set_state_reg(s, rd, state_mem(s, im+state_reg(s, rs)))
          i+1
        }
        case Store(rd, im, rs) => {
          set_state_mem(s, im+state_reg(s, rs), state_reg(s, rd))
          i+1
        }
      }
    }

  trait InterpCdTimed extends InterpCd with InterpCdCache {
    val TIME = 6
    def tick(s: Rep[stateT]): Rep[Unit] =
      s(TIME) += 1

    override def set_state_cache(s: Rep[stateT], key: Rep[Int], v: Rep[Int]) = {
      tick(s)
      tick(s)
      super.set_state_cache(s, key, v)
    }

    override def execute(i: Int, s: Rep[stateT]): Rep[Int] = {
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
    val snippet = new DslDriverX[stateT,Unit] with InterpCd {
      override val prog =  Vector(Add(0, 0, 0), Branch(0, 0))
      def snippet(s: Rep[stateT]): Rep[Unit] = call(0, s)
    }
    check("1", snippet.code)
  }

  test("interp 2") {
    val snippet = new DslDriverX[stateT,Unit] with InterpCd {
      override val prog =  Vector(Load(1, 0, 0), Load(2, 4, 1))
      def snippet(s: Rep[stateT]): Rep[Unit] = call(0, s)
    }
    check("2", snippet.code)
  }

  test("interp 2c") {
    val snippet = new DslDriverX[stateT,Unit] with InterpCd with InterpCdCache {
      override val prog =  Vector(Load(1, 0, 0), Load(2, 4, 1))
      def snippet(s: Rep[stateT]): Rep[Unit] = call(0, s)
    }
    check("2sc", snippet.code)
  }

  test("interp 2ct") {
    val snippet = new DslDriverX[stateT,Unit] with InterpCdTimed {
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
  int s2[100];
  init(s2);
  s1[0] = 5;
  s1[15] = 1;
  s2[0] = 5;
  Snippet(s1);
  Snippet(s2);
  __CPROVER_assert(s1[6]==s2[6], "timing leak");
  return 0;
}
"""
      override val prog =  Vector(Load(1, 0, 0), Load(2, 4, 1))
      def snippet(s: Rep[stateT]): Rep[Unit] = call(0, s)
    }
    check("2sct", snippet.code)
  }

  trait TimedDriver extends DslDriverX[stateT,Unit] with InterpCdTimed {
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
  int s2[100];
  init(s2);
  int x = bounded(0, 20);
  s1[0] = x;
  int i = 10+bounded(0, 20);
  s1[i] = 1;
  s2[0] = x;
  Snippet(s1);
  Snippet(s2);
  __CPROVER_assert(s1[6]==s2[6], "timing leak");
  return 0;
}
"""

    def snippet(s: Rep[stateT]): Rep[Unit] = call(0, s)
  }

  test("interp 2ct alt") {
    val snippet = new TimedDriver {
      override val prog =  Vector(Load(1, 0, 0), Load(2, 4, 1))
    }
    check("2ct_alt", snippet.code)
  }

  test("interp 3ct alt") {
    val snippet = new TimedDriver {
      override val prog =  Vector(Load(1, 0, 0), Load(2, 0, 0))
    }
    check("3ct_alt", snippet.code)
  }

  trait TimedNiDriver extends TimedDriver {
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
  int s2[100];
  init(s2);
  int x = bounded(0, 20);
  s1[0] = x;
  s2[0] = x;
  int i;
  for (i=0; i<20; i++) {
    s1[i+10] = bounded(0, 20);
    s2[i+10] = bounded(0, 20);
  }
  Snippet(s1);
  Snippet(s2);
  __CPROVER_assert(s1[6]==s2[6], "timing leak");
  return 0;
}
"""
  }

  test("interp 2ct ni") {
    val snippet = new TimedNiDriver {
      override val prog =  Vector(Load(1, 0, 0), Load(2, 4, 1))
    }
    check("2ct_ni", snippet.code)
  }

  test("interp 3ct ni") {
    val snippet = new TimedNiDriver {
      override val prog =  Vector(Load(1, 0, 0), Load(2, 0, 0))
    }
    check("3ct_ni", snippet.code)
  }
}
