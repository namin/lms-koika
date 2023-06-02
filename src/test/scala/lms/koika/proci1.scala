package lms.koika

class ProcInterpPC extends TutorialFunSuite {
  val under = "proci1_"

  val DEBUG = true

  type Reg = Int

  abstract sealed class Instruction
  case class Add(rd: Reg, rs1: Reg, rs2: Reg) extends Instruction
  case class Addi(rd: Reg, rs1: Reg, imm: Int) extends Instruction
  case class BrNEZ(rs: Reg, imm: Int) extends Instruction

  type Program = List[Instruction]
  type RegFile = Array[Int]
  type PC = Int
  type F2C = (PC, Instruction)

  type State = (RegFile, PC, F2C)

  def println(s: String) = if (DEBUG) Predef.println(s) else ()

  var regfile: RegFile = Array(0, 0, 0, 0, 0, 0, 0)
  var pc: PC = 0
  var f2c: F2C = (0, Add(0, 0, 0))
  var prog: Program = List(Add(0, 0, 0))

  def mkString(state: State): String = {
    val (regfile, pc, f2c) = state
    s"regfile: ${regfile.mkString(",")}\n" +
      s"PC: ${pc}\n" +
      s"F2C: ${f2c}"

  }

  def fetch(): F2C = {
    val (regfile, pc, f2c) = (this.regfile, this.pc, this.f2c)
    (pc, prog(pc))
  }

  def commit(): State = {
    val (regfile, pc, f2c) = (this.regfile, this.pc, this.f2c)
    val (fpc, f) = f2c
    (regfile, fpc, (fpc, f))
  }

  def run(): RegFile = {
    var cutate = (this.regfile, this.pc, this.f2c)
    while (this.pc < prog.length) {
      println(mkString(cutate))
      this.pc = prog(this.pc) match {

        case Add(rd, rs1, rs2) =>
          this.regfile(rd) = this.regfile(rs1) + this.regfile(rs2)
           pc + 1

        case Addi(rd, rs1, imm) =>
          this.regfile(rd) = this.regfile(rs1) + imm
          pc + 1

        case BrNEZ(rs, target) =>
          (if (this.regfile(rs) != 0) (pc + target) else pc + 1)
      }
    }
    this.regfile
  }

  def init(
      prog: Program,
      state: State = (Array(0, 0, 0, 0, 0, 0, 0), 0, (0, Add(0, 0, 0)))
  ): Unit = {
    this.prog = prog
    this.regfile = state._1
    this.pc = state._2
    this.f2c = state._3
  }

  test("proc 1") {
    val initRegFile = Array(0, 0, 1, 0, 15, -1)
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

    init(Fibprog, (initRegFile, 0, (0, Add(0, 0, 0))))

    val res = run()
    val expected = Array(0, 610, 987, 987, 0, -1)

    assert(res === expected)
  }

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

    init(Fibprog, (initRegFile, 0, (0, Add(0, 0, 0))))
    val res = run()
    val expected = Array(0, 610, 987, 987, 0, 0, 0)

    assert(res === expected)

  }
}
