package lms.koika

import lms.core.stub._
import lms.core.virtualize
import lms.macros.SourceContext

@virtualize
class StagedProcInterp1bPC extends TutorialFunSuite {
  val under = "proci1b_staged_"

  val regfile_main = """
int main(int argc, char *argv[]) {
  int regfile[7] = {0, 0, 0, 0, 0, 0, 0};
  Snippet(regfile);
  for (int i = 0; i < 6; i++) {
    printf("%d ", regfile[i]);
  }
  printf("\n");
  return 0;
}
"""

  def constructMain(expected: Array[Int]): String = {
    var ret = s"""
// cc file.c for execution
// cbmc -DCBMC file.c for verification
#ifndef CBMC
#define __CPROVER_assert(b,s) 0
#endif
int main(int argc, char *argv[]) {
  int regfile[7] = {0, 0, 0, 0, 0, 0, 0};
  Snippet(regfile);
"""
    var printexpected = s"""
  printf("\\nexpected:\\n");
  printf(""""
    for (i <- 0 until expected.length) {
      printexpected += s"""${expected(i)} """
    }
    printexpected += s""" ");
"""
    for (i <- 0 until expected.length) {
      ret += s"""
  __CPROVER_assert(regfile[$i]==${expected(i)}, "failure $i");
  if (regfile[$i] != ${expected(i)}) {
    printf("error: regfile[$i] = %d, expected ${expected(i)}\\n", regfile[$i]);
    goto error;
  }
"""
    }
    ret += s"""
  printf("OK\\n");
  return 0;
error:
  printf("\\nRegfile:\\n");
  for (int i = 0; i < 6; i++) {
    printf("%d ", regfile[i]);
  }
  ${printexpected}
  printf("\\n\\nFAILED\\n");
  return 1;

}
"""
    ret
  }

  override def exec(label: String, code: String, suffix: String = "c") =
    super.exec(label, code, suffix)

  override def check(label: String, code: String, suffix: String = "c") =
    super.check(label, code, suffix)

  val DEBUG = true

  trait Interp extends Dsl {

    abstract sealed class Instruction
    case class Add(rd: Reg, rs1: Reg, rs2: Reg) extends Instruction
    case class Addi(rd: Reg, rs1: Reg, imm: Int) extends Instruction
    case class JumpNZ(rs: Reg, imm: Int) extends Instruction
    case class JumpNeg(rs: Reg, imm: Int) extends Instruction

    type Program = List[Instruction]
    type RegFile = Array[Int]

    case class Reg(id: Int)
    val ZERO: Reg = Reg(0)
    val A0: Reg = Reg(1)
    val A1: Reg = Reg(2)
    val A2: Reg = Reg(3)
    val A3: Reg = Reg(4)
    val A4: Reg = Reg(5)
    val A5: Reg = Reg(6)

    val NOP = Addi(ZERO, ZERO, 0)

    implicit def reg2int(r: Reg): Int = r.id
    implicit def reg2rep(r: Reg): Rep[Int] = unit(r.id)

    class Port[T: Manifest](
        init: T,
        customEqual: Option[(Rep[T], Rep[T]) => Rep[Boolean]] = None
    ) {

      private var readport: Var[T] = __newVar(init)
      private var writeport: Var[T] = __newVar(init)

      private def equal(a: Rep[T], b: Rep[T]): Rep[Boolean] =
        customEqual match {
          case Some(f) => f(a, b)
          case None    => a == b
        }

      def read: Rep[T] = readVar(readport)

      def write(d: Rep[T]): Rep[Unit] = writeport = d

      def flush(): Rep[Unit] = writeport = init

      def update(): Rep[Unit] = readport = writeport

      def isDefault: Rep[Boolean] = equal(read, unit(init))
      def isAmong(vs: T*): Rep[Boolean] =
        vs.foldLeft(unit(false))((acc, v) => acc || equal(read, unit(v)))
    }

    def println(s: String) = if (DEBUG) Predef.println(s) else ()

    def readProgram(file: String): Program = {
      scala.io.Source
        .fromFile(file)
        .getLines()
        .map { line =>
          val tokens = line.split(" ")
          tokens match {
            case Array("add", rd, rs1, rs2) =>
              Add(Reg(rd.toInt), Reg(rs1.toInt), Reg(rs2.toInt))
            case Array("addi", rd, rs1, imm) =>
              Addi(Reg(rd.toInt), Reg(rs1.toInt), imm.toInt)
            case Array("jumpnz", rs, imm) =>
              JumpNZ(Reg(rs.toInt), imm.toInt)
            case Array("jumpneg", rs, imm) =>
              JumpNeg(Reg(rs.toInt), imm.toInt)
            case _ => Predef.println(s"Unknown instruction: $line"); NOP
          }
        }
        .toList
    }

    def expectedResult(prog: Program): Array[Int] = {
      var rf: Array[Int] = List(0, 0, 0, 0, 0, 0, 0).toArray
      var i: Int = 0
      while (i < prog.length) {
        prog(i) match {
          case Add(rd, rs1, rs2) => {
            rf(rd) = rf(rs1) + rf(rs2)
            i = i + 1
          }
          case Addi(rd, rs1, imm) => {
            rf(rd) = rf(rs1) + imm
            i = i + 1
          }
          case JumpNZ(rs, target) => {
            if (rf(rs) != 0) i = i + target
            else i = i + 1
          }
          case JumpNeg(rs, target) => {
            if (rf(rs) < 0) i = i + target
            else i = i + 1
          }
        }
      }
      rf

    }

    def run(prog: Program, state: Rep[RegFile]): Rep[RegFile] = {
      val regfile: Rep[RegFile] = state
      var pc: Port[Int] = new Port[Int](0)
      var e2c_dst: Port[Int] = new Port[Int](0)
      var e2c_val: Port[Int] = new Port[Int](0)

      while (0 <= pc.read && pc.read < prog.length) {
        // The reason why we need this is because the branch instruction could
        // stall in E stage, waiting on C stage to update rs.
        // So pc should stay the same until the branch is executed.
        pc.update()

        // Commit stage
        regfile(e2c_dst.read) = e2c_val.read

        // pipeline update
        e2c_dst.update()
        e2c_val.update()

        // Execute stage
        for (i <- (0 until prog.length): Range) {
          if (i == pc.read) {
            prog(i) match {
              case Add(rd, rs1, rs2) => {
                if (!e2c_dst.isAmong(rd, rs1, rs2) || e2c_dst.isDefault) {
                  e2c_dst.write(rd)
                  e2c_val.write(regfile(rs1) + regfile(rs2))
                  pc.write(pc.read + 1)
                } else {
                  // stall
                  e2c_dst.flush()
                  e2c_val.flush()
                }
              }

              case Addi(rd, rs1, imm) => {
                if (!e2c_dst.isAmong(rd, rs1) || e2c_dst.isDefault) {
                  e2c_dst.write(rd)
                  e2c_val.write(regfile(rs1) + imm)
                  pc.write(pc.read + 1)
                } else {
                  // stall
                  e2c_dst.flush()
                  e2c_val.flush()
                }
              }

              case JumpNZ(rs, target) => {
                if (e2c_dst.read != rs.id) {
                  if (regfile(rs) == 0) {
                    pc.write(pc.read + 1)
                  } else {
                    pc.write(pc.read + target)
                  }
                }
                e2c_dst.flush()
                e2c_val.flush()
              }
              case JumpNeg(rs, target) => {
                if (e2c_dst.read != rs.id) {
                  if (regfile(rs) >= 0) {
                    pc.write(pc.read + 1)
                  } else {
                    pc.write(pc.read + target)
                  }
                }
                e2c_dst.flush()
                e2c_val.flush()
              }
            }
          }
        }
      }
      // let a cycle bubble through
      regfile(e2c_dst.read) = e2c_val.read
      regfile
    }
  }

  abstract class DslDriverX[A: Manifest, B: Manifest] extends DslDriverC[A, B] {
    q =>
    val main: String = ""

    override val codegen = new DslGenC {
      val IR: q.type = q

      override def emitAll(
          g: lms.core.Graph,
          name: String
      )(m1: Manifest[_], m2: Manifest[_]): Unit = {
        val ng = init(g)
        val efs = "" // quoteEff(g.block.ein)
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

  test("proc 1") {
    val snippet = new DslDriverX[Array[Int], Array[Int]] with Interp {
      val N = A3
      val Temp = A2
      val F_n = A1
      val F_n_1 = A0
      val Fibprog = List(
        Addi(F_n, ZERO, 1),
        Addi(F_n_1, ZERO, 0),
        Addi(N, ZERO, 15),
        Addi(Temp, ZERO, 0),
        Add(Temp, F_n, F_n_1),
        Add(F_n_1, F_n, ZERO),
        Add(F_n, Temp, ZERO),
        Addi(N, N, -1),
        JumpNZ(N, -4)
      )
      val expected = expectedResult(Fibprog)
      override val main = constructMain(expected)
      def snippet(initRegFile: Rep[RegFile]) = {

        run(Fibprog, initRegFile)
      }
    }
    check("1", snippet.code)
  }

  test("proc rar hazard") {
    val snippet = new DslDriverX[Array[Int], Array[Int]] with Interp {
      val prog = List(
        Addi(A1, A0, 1), //
        Addi(A3, A0, 2), // RAR
        Addi(A2, A4, 3) // NO RAR
      )
      val expected = expectedResult(prog)
      override val main = constructMain(expected)
      def snippet(initRegFile: Rep[RegFile]) = {
        run(prog, initRegFile)
      }
    }
    check("rar_hazard", snippet.code)
  }

  test("proc waw hazard") {
    val snippet = new DslDriverX[Array[Int], Array[Int]] with Interp {
      val prog = List(
        Addi(A0, ZERO, 1),
        Addi(A0, A0, 1), // WAW
        Addi(A3, A2, 2) // NO WAW
      )
      val expected = expectedResult(prog)
      override val main = constructMain(expected)
      def snippet(initRegFile: Rep[RegFile]) = {
        run(prog, initRegFile)
      }
    }
    check("waw_hazard", snippet.code)
  }

  test("proc raw hazard") {
    val snippet = new DslDriverX[Array[Int], Array[Int]] with Interp {
      val prog = List(
        Addi(A0, ZERO, 1),
        Addi(A1, A0, 1), // RAW
        Addi(A3, A2, 2) // NO RAW
      )
      val expected = expectedResult(prog)
      override val main = constructMain(expected)
      def snippet(initRegFile: Rep[RegFile]) = {
        run(prog, initRegFile)
      }
    }
    check("raw_hazard", snippet.code)
  }

  test("proc war hazard") {
    val snippet = new DslDriverX[Array[Int], Array[Int]] with Interp {
      val prog = List(
        Addi(A1, A0, 1), //
        Addi(A0, A3, 2), // WAR
        Addi(A2, A4, 3) // NO WAR
      )
      val expected = expectedResult(prog)
      override val main = constructMain(expected)
      def snippet(initRegFile: Rep[RegFile]) = {
        run(prog, initRegFile)
      }
    }
    check("war_hazard", snippet.code)
  }

  test("proc loop") {
    val snippet = new DslDriverX[Array[Int], Array[Int]] with Interp {
      val prog = List(
        Addi(A0, ZERO, 3),
        Addi(A0, A0, -1),
        JumpNZ(A0, -1)
      )
      val expected = expectedResult(prog)
      override val main = constructMain(expected)
      def snippet(initRegFile: Rep[RegFile]) = {
        run(prog, initRegFile)
      }
    }
    check("loop_hazard", snippet.code)
  }

  test("proc hazard") {
    val snippet = new DslDriverX[Array[Int], Array[Int]] with Interp {
      val prog = List(
        Addi(A0, ZERO, 1),
        Add(A1, A0, A0), // RAW
        Add(A2, A1, A0),
        Add(A3, A2, A1),
        Add(A0, A3, A2), // RAW
        Add(A1, A0, A3), // RAW, RAR
        Add(A2, A1, A0), // RAW, RAR
        Add(A3, A2, A1), // RAW, RAR
        Add(A3, A0, A3) // WAW, RAW
      )
      val expected = expectedResult(prog)
      override val main = constructMain(expected)
      def snippet(initRegFile: Rep[RegFile]) = {
        run(prog, initRegFile)
      }
    }
    check("hazard", snippet.code)

  }

  ignore("proc stress") {
    // read from file 1.asm and get the program
    val snippet = new DslDriverX[Array[Int], Array[Int]] with Interp {
      val filename = "src/out/1.asm"
      val program = readProgram(filename)
      val expected: Array[Int] = expectedResult(program)
      override val main = constructMain(expected)

      def snippet(initRegFile: Rep[RegFile]) = {
        run(program, initRegFile)
      }

    }
    exec("stress", snippet.code)
  }

}
