package lms.koika

class ProcInterpPC extends TutorialFunSuite {
  val under = "proci1_"

  val DEBUG = false  
  val MAX_STEPS = 1000
  val NOP = Addi(0, 0, 0)

  type Reg = Int

  abstract sealed class Instruction
  case class Add(rd: Reg, rs1: Reg, rs2: Reg) extends Instruction
  case class Addi(rd: Reg, rs1: Reg, imm: Int) extends Instruction
  case class BrNEZ(rs: Reg, imm: Int) extends Instruction
  case class Exit() extends Instruction

  type Program = List[Instruction]
  type RegFile = Array[Int]
  type PC = Int
  type F2C = (PC, Instruction)

  type State = (RegFile, PC, F2C)

  var regfile: RegFile = Array(0, 0, 0, 0, 0, 0, 0)
  var pc: PC = 0 // pc register used by the fetch stage
  var f2c: F2C = (0, NOP) //  fetch to commit stage, read by the commit stage
  var prog: Program = List(NOP)

  def log(): Unit = {
    if (DEBUG) {
      val str = s"regfile: ${this.regfile.mkString(",")}\n" +
        s"PC: ${this.pc}\n" +
        s"F2C: ${this.f2c}\n"
      println(str)
    }

  }
  def println(str: String): Unit = {
    if (DEBUG) {
      Predef.println(str)
    }
  }

  // updates pc
  def fetch(): F2C = {
    val (regfile, pc, f2c) = (this.regfile, this.pc, this.f2c)
    this.pc = pc + 1 // keep fetching next instruction
    pc match {
      case pc if pc < prog.length => (pc, prog(pc))
      case _                      => (pc, NOP)
    }
  }

  // updates regfile
  def commit(): (PC, Boolean) = {
    val (regfile, pc, f2c) = (this.regfile, this.pc, this.f2c)
    val (fpc, i) = f2c
    i match {
      case Add(rd, rs1, rs2) =>
        this.regfile(rd) = this.regfile(rs1) + this.regfile(rs2)
      case Addi(rd, rs1, imm) =>
        this.regfile(rd) = this.regfile(rs1) + imm
      case BrNEZ(rs, imm) =>
        return (if (this.regfile(rs) != 0) (fpc + imm) else fpc + 1, false)
      case Exit() =>
        return (0, true)
    }

    (fpc+1, false)
  }

  def run_stages(): RegFile = {
    var cnt = 0
    var continue = true 
    while (cnt < MAX_STEPS && continue)  {
      var (actualPC, break) = commit()
      this.f2c = fetch()
      if (actualPC != this.f2c._1) {
        println(s"revert. actualPC: ${actualPC}, f2c: ${this.f2c}")
        this.pc = actualPC
        this.f2c = (actualPC-1, NOP)
      }
      log()
      continue = !break
      cnt += 1
    }
    if (cnt == MAX_STEPS) {
      println(s"MAX_STEPS reached")
    }
    this.regfile
  }

  def run(): RegFile = {
    while (this.pc < prog.length) {
      this.pc = prog(this.pc) match {

        case Add(rd, rs1, rs2) =>
          this.regfile(rd) = this.regfile(rs1) + this.regfile(rs2)
          pc + 1

        case Addi(rd, rs1, imm) =>
          this.regfile(rd) = this.regfile(rs1) + imm
          pc + 1

        case BrNEZ(rs, target) =>
          (if (this.regfile(rs) != 0) (pc + target) else pc + 1)
        case Exit() => prog.length
      }
    }
    this.regfile
  }

  def init(
      prog: Program,
      state: State = (Array(0, 0, 0, 0, 0, 0, 0), 0, (0, NOP))
  ): Unit = {
    this.prog = prog
    this.regfile = state._1
    this.pc = state._2
    this.f2c = state._3
  }

  test("proc 1 run") {
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
      BrNEZ(N, -4),
      Exit()
    )

    init(Fibprog, (initRegFile, 0, (-1, NOP)))

    val res = run()
    val expected = Array(0, 610, 987, 987, 0, -1)

    assert(res === expected)

  }

  test("proc 1 run stages") {
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
      BrNEZ(N, -4),
      Exit()
    )

    init(Fibprog, (initRegFile, 0, (-1, NOP)))

    val res = run_stages()

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
      BrNEZ(N, -4),
      Exit()
    )

    init(Fibprog, (initRegFile, 0, (-1, NOP)))
    println("")
    println("proc 2")
    println("")
    val res = run_stages()
    val expected = Array(0, 610, 987, 987, 0, 0, 0)

    assert(res === expected)

  }
}
