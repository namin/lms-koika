package lms.koika

import lms.core.stub._
import lms.core.virtualize
import lms.macros.SourceContext

@virtualize
class StagedProcInterp1bPC extends TutorialFunSuite {
  val under = "proci1b_staged_"

  val DEBUG = true

  type Reg = Int

  abstract sealed class Instruction
  case class Add(rd: Reg, rs1: Reg, rs2: Reg) extends Instruction
  case class Addi(rd: Reg, rs1: Reg, imm: Int) extends Instruction
  case class BrNEZ(rs: Reg, imm: Int) extends Instruction

  trait Interp extends Dsl {
    type Program = List[Instruction]
    type RegFile = Rep[Array[Int]]
    type PC = Rep[Int]

    type State = (RegFile, PC)

    def println(s: String) = if (DEBUG) Predef.println(s) else ()

    def run(
      prog: Program,
      state: (RegFile, PC)): RegFile = {
      var regfile: RegFile = state._1
      var pc: Var[Int] = __newVar(state._2)

      while (0 <= readVar(pc) && pc < prog.length) {
        for (i <- (0 until prog.length): Range) {
          if (i == pc) {
            prog(i) match {
              case Add(rd, rs1, rs2) =>
                regfile(rd) = regfile(rs1) + regfile(rs2)
                pc = pc + 1

              case Addi(rd, rs1, imm) =>
                regfile(rd) = regfile(rs1) + imm
                pc = pc + 1

              case BrNEZ(rs, target) =>
                if (regfile(rs) != 0) pc = pc + target
                else pc = pc + 1
            }
          }
        }
      }
      regfile
    }
  }

  test("proc 1") {
    val snippet = new DslDriver[Array[Int], Int] with Interp {
      def snippet(initRegFile: RegFile) = {

        //val initRegFile = List(0, 0, 1, 0, 15, -1)
        val N = 4
        val Temp = 3
        val F_n = 2
        val F_n_1 = 1
        val Zero = 0
        val MinusOne = 5
        val Fibprog = List(
          Add(Temp, F_n, F_n_1),
          Add(F_n_1, F_n, Zero),
          Add(F_n, Temp, Zero),
          Add(N, N, MinusOne),
          BrNEZ(N, -4)
        )

        val res = run(Fibprog, (initRegFile, 0))
        val expected = Array(0, 610, 987, 987, 0, -1)

        // assert(res === expected)
        res(F_n)
      }

    }
    check("1", snippet.code)

  }
  /*
  test("proc 2") {
    var initRegFile = Array(0, 0, 0, 0, 0, 0, 0)
    val N = 4
    val Temp = 3
    val F_n = 2
    val F_n_1 = 1
    val Zero = 0

    val Fibprog = List(
      Addi(F_n, Zero, 1),
      Addi(F_n_1, Zero, 0),
      Addi(N, Zero, 15),
      Addi(Temp, Zero, 0),
      Add(Temp, F_n, F_n_1),
      Add(F_n_1, F_n, Zero),
      Add(F_n, Temp, Zero),
      Addi(N, N, -1),
      BrNEZ(N, -4)
    )

    init(Fibprog, (initRegFile, 0))
    val res = run()
    val expected = Array(0, 610, 987, 987, 0, 0, 0)

    assert(res === expected)

  }
   */
}
