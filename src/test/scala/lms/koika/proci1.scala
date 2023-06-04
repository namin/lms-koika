package lms.koika


// TODO: use something better than an Exit instruction
// TODO: use valid signal between stages
// TODO: use better alternative than this.pc = -1 at the start of the program
//
//
// TODO: (hard) add load/store instructions
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
  type F2E = (PC, Instruction)
  type E2C = (PC, Option[Reg], Int, PC, Boolean)// (PC, rd, value, nextPC, break)

  type State = (RegFile, PC, F2E, E2C) 

  var regfile: RegFile = Array(0, 0, 0, 0, 0, 0, 0)
  var pc: PC = -1 // pc register used by the fetch stage
  var f2e: F2E = (0, NOP) //  fetch to execute stage, read by the execute stage
  var e2c: E2C = (0, None, 0, 0, false) // execute to commit stage, read by the commit stage
  var prog: Program = List(NOP)

  def log(): Unit = {
    if (DEBUG) {
      val str = s"regfile: ${this.regfile.mkString(",")}\n" +
        s"PC: ${this.pc}\n" +
        s"f2e: ${this.f2e}\n" +
        s"e2c: ${this.e2c}\n"
      println(str)
    }

  }
  def println(str: String): Unit = {
    if (DEBUG) {
      Predef.println(str)
    }
  }

  // updates pc
  def fetch(): F2E = {
    val (regfile, pc ) = (this.regfile, this.pc)
    this.pc = pc + 1 // keep fetching next instruction
    pc match {
      case pc if pc < prog.length => (pc, prog(pc))
      case _                      => (pc, NOP)
    }
  }

  // updates E2C
  def exec(): E2C = {
    val (regfile, f2e) = (this.regfile, this.f2e)
    val (fpc, inst) = f2e
    inst match {
      case Add(rd, rs1, rs2) =>
        (fpc, Some(rd), regfile(rs1) + regfile(rs2), fpc + 1, false)
      case Addi(rd, rs1, imm) =>
        (fpc, Some(rd), regfile(rs1) + imm, fpc + 1, false)
      case BrNEZ(rs, imm) =>
        (fpc, None, 0, if (regfile(rs) != 0) fpc + imm else fpc + 1, false)
      case Exit() =>
        (fpc, None, 0, fpc+1, true)
    }
  }

  // updates regfile
  def commit(): Boolean = {
    val (regfile, e2c) = (this.regfile, this.e2c)
    val (fpc, rd, value, nextPC, break) = e2c 
    rd match {
      case Some(rd) => regfile(rd) = value
      case None     => ()
    }
    break
  }

  def run_stages(): RegFile = {
    var cnt = 0
    var continue = true 
    while (cnt < MAX_STEPS && continue)  {
      var break = commit()
      this.e2c = exec()
      this.f2e = fetch()
      val nextPC = this.e2c._4
      if (nextPC != this.f2e._1) { 
        println(s"revert. nextPC: ${nextPC}, f2e: ${this.f2e}, e2c: ${this.e2c}")
        this.pc = nextPC
        this.f2e = (nextPC-1, NOP)
        this.e2c = (nextPC-2, None, 0, nextPC-1, false)
      }
      log()
      continue = !break
      cnt += 1
    }
    if (cnt == MAX_STEPS) {
      println(s"MAX_STEPS reached")
      assert(false)
    }
    this.regfile
  }

  def run(): RegFile = {
    var cnt = 0
    while (this.pc < prog.length && cnt < MAX_STEPS) {
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
      log()
      cnt += 1
    }
    this.regfile
  }

  def init(
      prog: Program,
      state: State = (Array(0, 0, 0, 0, 0, 0, 0), 0, (-1, NOP), (-2, None, 0, 0, false))
  ): Unit = {
    this.prog = prog
    this.regfile = state._1
    this.pc = state._2
    this.f2e = state._3
    this.e2c = state._4
  }
  
  // compare run_stages with run on a given program
  // with the standard initial state
  //
  // Used to test the correctness of the run_stages method
  private def check(prog: Program) = {
    init(prog)
    val res = run()
    init(prog)
    val res_stages = run_stages()
    assert(res === res_stages)
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

    init(Fibprog, (initRegFile, 0, (-1, NOP), (-2, None, 0, 0, false)))

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

    init(Fibprog, (initRegFile, 0, (-1, NOP), (-2, None, 0, 0, false)))

    val res = run_stages()

    val expected = Array(0, 610, 987, 987, 0, -1)
    assert(res === expected)

  }

  test("proc 2 compare")  {
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

    init(Fibprog)
    val res = run()
    val expected = Array(0, 610, 987, 987, 0, 0, 0)

    assert(res === expected)

    check(Fibprog)

  }


  test("proc 3 compare") {
    val A = 1
    val B = 2
    val EarlyExit = List(
      Addi(A, A, 1),
      Addi(B, B, 1),
      Addi(A, A, -1),
      Exit(),
      Addi(B, B, -1),
      Exit(),
    )

    init(EarlyExit)
    val res = run()
    val expected = Array(0, 0, 1, 0, 0, 0, 0)

    assert(res === expected)

    check(EarlyExit)
  }

  test("proc 4 compare") {

    val N = 0
    
    val FibTri = List(
      Addi(5, 5, 1),
      Addi(N, N, 4),

      Add(1, 1, 2),
      Add(2, 2, 3),
      Add(3, 3, 4),
      Add(4, 4, 5),
      Add(5, 5, 6),
      Addi(N, N, -1),
      BrNEZ(N, -6),
      Exit()
      )

    init(FibTri)
    val res = run()
    val expected = Array(0, 1, 4, 6, 4, 1, 0)

    assert(res === expected)

    check(FibTri)
  }

}
