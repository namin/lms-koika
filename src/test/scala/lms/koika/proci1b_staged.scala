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

  val DEBUG = true

  trait Interp extends Dsl {

    abstract sealed class Instruction
    case class Add(rd: Reg, rs1: Reg, rs2: Reg) extends Instruction
    case class Addi(rd: Reg, rs1: Reg, imm: Int) extends Instruction
    case class BrNEZ(rs: Reg, imm: Int) extends Instruction

    type Program = List[Instruction]
    type RegFile = Rep[Array[Int]]
    type PC = Rep[Int]

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

    type State = (RegFile, PC)

    class Port[T: Manifest](
        init: T,
        customEqual: Option[(Rep[T], Rep[T]) => Rep[Boolean]] = None
    ) {

      private var rdata: Var[T] = __newVar(init)
      private var wdata: Var[T] = __newVar(init)

      def equal(a: Rep[T], b: Rep[T]): Rep[Boolean] = customEqual match {
        case Some(f) => f(a, b)
        case None    => a == b
      }

      def read: Rep[T] = readVar(rdata)

      def write(d: Rep[T]): Rep[Unit] = wdata = d

      def update(): Rep[Unit] = rdata = wdata

      def isZero(): Rep[Boolean] = equal(read, unit(init))
      def isAmong(vs: List[T]): Rep[Boolean] =
        vs.foldLeft(unit(false))((acc, v) => acc || read == unit(v))
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
            case Array("br", rs, imm) =>
              BrNEZ(Reg(rs.toInt), imm.toInt)
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
          case BrNEZ(rs, target) => {
            if (rf(rs) != 0) i = i + target
            else i = i + 1
          }
        }
      }
      rf

    }

    def run(prog: Program, state: (RegFile, PC)): RegFile = {
      val regfile: RegFile = state._1
      var pc: Port[Int] = new Port[Int](0)
      var e2c_dst: Port[Int] = new Port[Int](0)
      var e2c_val: Port[Int] = new Port[Int](0)

      while (0 <= pc.read && pc.read < prog.length) {
        pc.update() // TODO formalise why this is needed
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
                if (
                  !e2c_dst
                    .isAmong(List(rd, rs1, rs2)) || unit(0) == e2c_dst.read
                ) {
                  e2c_dst.write(rd)
                  e2c_val.write(regfile(rs1) + regfile(rs2))
                  pc.write(pc.read + 1)
                } else {
                  // stall
                  e2c_dst.write(0)
                  e2c_val.write(0)
                }
              }

              case Addi(rd, rs1, imm) => {
                if (
                  !e2c_dst.isAmong(List(rd, rs1)) || unit(0) == e2c_dst.read
                ) {
                  e2c_dst.write(rd)
                  e2c_val.write(regfile(rs1) + imm)
                  pc.write(pc.read + 1)
                } else {
                  // stall
                  e2c_dst.write(0)
                  e2c_val.write(0)
                }
              }

              case BrNEZ(rs, target) => {
                if (e2c_dst.read != rs.id) {
                  if (regfile(rs) == 0) {
                    pc.write(pc.read + 1)
                  } else {
                    pc.write(pc.read + target)
                  }
                } // otherwise stall
                e2c_dst.write(0)
                e2c_val.write(0)
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
        BrNEZ(N, -4)
      )
      val expected = expectedResult(Fibprog)
      override val main = constructMain(expected)
      def snippet(initRegFile: RegFile) = {

        run(Fibprog, (initRegFile, 0))
      }
    }
    exec("1", snippet.code)
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
      def snippet(initRegFile: RegFile) = {
        run(prog, (initRegFile, 0))
      }
    }
    exec("raw_hazard", snippet.code)
  }

  test("proc loop") {
    val snippet = new DslDriverX[Array[Int], Array[Int]] with Interp {
      val prog = List(
        Addi(A0, ZERO, 3),
        Addi(A0, A0, -1),
        BrNEZ(A0, -1)
      )
      val expected = expectedResult(prog)
      override val main = constructMain(expected)
      def snippet(initRegFile: RegFile) = {
        run(prog, (initRegFile, 0))
      }
    }
    exec("loop_hazard", snippet.code)
  }

  test("proc hazard") {
    val snippet = new DslDriverX[Array[Int], Array[Int]] with Interp {
      // TODO: these hazards are not really hazards, because we commit before we execute the next stage.
      // We should consider moving the commit phase later,
      // and then also stalling in case of a dependency.
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
      def snippet(initRegFile: RegFile) = {
        run(prog, (initRegFile, 0))
      }
    }
    exec("hazard", snippet.code)

  }

  test("proc stress") {
    // read from file 1.asm and get the program
    val snippet = new DslDriverX[Array[Int], Array[Int]] with Interp {
      val filename = "src/out/1.asm"
      val program = readProgram(filename)
      val expected: Array[Int] = expectedResult(program)
      override val main = constructMain(expected)

      def snippet(initRegFile: RegFile) = {
        run(program, (initRegFile, 0))
      }

    }
    exec("stress", snippet.code)
  }

}
