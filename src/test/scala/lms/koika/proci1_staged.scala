package lms.koika

import lms.core.stub._
import lms.core.virtualize
import lms.macros.SourceContext

@virtualize
class StagedProcInterpPC extends TutorialFunSuite {
  val under = "proci1_staged_"

  val DEBUG = true

  type Reg = Int

  abstract sealed class Instruction
  case class Add(rd: Reg, rs1: Reg, rs2: Reg) extends Instruction
  case class Addi(rd: Reg, rs1: Reg, imm: Int) extends Instruction
  // case class BrNEZ(rs: Reg, imm: Int) extends Instruction

  trait Interp extends Dsl {
    type Program = List[Instruction]
    type RegFile = Rep[Array[Int]]
    type PC = Int

    type State = (RegFile, PC)

    def println(s: String) = if (DEBUG) Predef.println(s) else ()

    var regfile: RegFile = unit(List(0, 0, 0, 0, 0, 0, 0).toArray)
    var pc: PC = 0
    var prog: Program = List(Add(0, 0, 0))

    def run(): RegFile = {
      while (this.pc < prog.length) {
        prog(this.pc) match {

          case Add(rd, rs1, rs2) =>
            this.regfile(rd) = this.regfile(rs1) + this.regfile(rs2)
            this.pc = pc + 1

          case Addi(rd, rs1, imm) =>
            this.regfile(rd) = this.regfile(rs1) + imm
            this.pc = pc + 1

          // case BrNEZ(rs, target) =>
          // if (this.regfile(rs) != 0) this.pc = pc + target
          // else this.pc = pc + 1
        }
      }
      this.regfile
    }

    def init(
        prog: Program,
        state: (RegFile, Int)
    ): Unit = {
      this.prog = prog
      this.regfile = state._1
      this.pc = state._2
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
          Add(N, N, MinusOne)
          // BrNEZ(N, -4)
        )

        init(Fibprog, (initRegFile, 0))

        val res = run()
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
