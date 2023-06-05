package lms.koika

// TODO: use something better than an Exit instruction
// TODO: use better alternative than this.pc = -1 at the start of the program
//
//
// TODO: (hard) add load/store instructions
class ProcInterpPC extends TutorialFunSuite {
  val under = "proci1_"

  val DEBUG = true
  val MAX_STEPS = 1000
  val NOP = Addi(0, 0, 0)

  type Reg = Int
  type Heap = Array[Int]

  abstract sealed class Instruction
  case class Add(rd: Reg, rs1: Reg, rs2: Reg) extends Instruction
  case class Addi(rd: Reg, rs1: Reg, imm: Int) extends Instruction
  case class BrNEZ(rs: Reg, imm: Int) extends Instruction
  case class Load(rd: Reg, rs1: Reg, imm: Int) extends Instruction
  case class Store(rs1: Reg, rs2: Reg, imm: Int) extends Instruction
  case class Exit() extends Instruction

  type Program = List[Instruction]
  type RegFile = Array[Int]
  type PC = Int
  type F2E = (PC, Instruction)
  type E2C =
    (PC, Option[Reg], Int, PC, Boolean) // (PC, rd, value, nextPC, break)

  type State = (Heap, RegFile, PC, Option[F2E], Option[E2C])

  var regfile: RegFile = Array(0, 0, 0, 0, 0, 0, 0)
  var pc: PC = -1 // pc register used by the fetch stage
  var f2e: Option[F2E] =
    None //  fetch to execute stage, read by the execute stage
  var e2c: Option[E2C] =
    None // execute to commit stage, read by the commit stage
  var prog: Program = List(NOP)
  var heap: Heap = Array(0, 0, 0, 0, 0, 0, 0, 0, 0, 0)

  def log(): Unit = {
    if (DEBUG) {
      val str = s"regfile: ${this.regfile.mkString(",")}\n" +
        s"PC: ${this.pc}\n" +
        s"f2e: ${this.f2e}\n" +
        s"e2c: ${this.e2c}\n" +
        s"\nheap: ${this.heap.mkString(",")}\n"
      println(str)
    }
  }

  def println(str: String): Unit = {
    if (DEBUG) {
      Predef.println(str)
    }
  }

  // updates pc
  def fetch(): Option[F2E] = {
    val (regfile, pc) = (this.regfile, this.pc)
    this.pc = pc + 1 // keep fetching next instruction
    pc match {
      case pc if pc < prog.length => Some(pc, prog(pc))
      case _                      => None
    }
  }

  // updates E2C
  def exec(): Option[E2C] = {
    this.f2e map { (st: F2E) =>
      val (fpc, instr) = st
      instr match {
        case Add(rd, rs1, rs2) =>
          (fpc, Some(rd), this.regfile(rs1) + this.regfile(rs2), fpc + 1, false)
        
        case Addi(rd, rs1, imm) =>
          (fpc, Some(rd), this.regfile(rs1) + imm, fpc + 1, false)
        
        case BrNEZ(rs, imm) =>
          val nextPC = if (this.regfile(rs) != 0) fpc + imm else fpc + 1
          (fpc, None, 0, nextPC, false)
        
        case Load(rd, rs1, imm) =>
          (fpc, Some(rd), this.heap(this.regfile(rs1) + imm), fpc + 1, false)
        
        case Store(rs1, rs2, imm) =>
          this.heap(this.regfile(rs1) + imm) = this.regfile(rs2)
          (fpc, None, 0, fpc + 1, false)
        
        case Exit() =>
          (fpc, None, 0, fpc + 1, true)
        
        case _ =>
          println(s"unknown instruction: ${instr}")
          assert(false)
          (fpc, None, 0, fpc + 1, false)
      }
    }
  }

  // updates regfile
  def commit(): Boolean = {
    this.e2c match {
      case Some(e2c_) =>
        val (fpc, rd, value, nextPC, break) = e2c_
        rd map { (rd_) =>
          this.regfile(rd_) = value
        }
        break
      case None => false
    }
  }

  def run_stages(): RegFile = {
    var cnt = 0
    var continue = true
    while (cnt < MAX_STEPS && continue) {
      var break = commit()
      this.e2c = exec()
      this.f2e = fetch()
      this.e2c map { (e2c_) =>
        this.f2e map { (f2e_) =>
          val (fpc, _) = f2e_
          val (_, _, _, nextPC, _) = e2c_
          if (nextPC != fpc) {
            println(
              s"revert. nextPC: ${nextPC}, f2e: ${f2e_}, e2c: ${e2c_}"
            )
            this.pc = nextPC
            this.f2e = None
            this.e2c = None
          }
        }
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

        case Load(rd, rs, offset) =>
          this.regfile(rd) = this.heap(this.regfile(rs) + offset)
          pc + 1

        case Store(rs1, rs2, offset) =>
          this.heap(this.regfile(rs1) + offset) = this.regfile(rs2)
          pc + 1

        case Exit() => prog.length
        case _ =>
          println(s"unknown instruction: ${prog(pc)}")
          assert(false)
          pc + 1
      }
      log()
      cnt += 1
    }
    this.regfile
  }

  def init(
      prog: Program,
      state: State = (
        Array(0, 0, 0, 0, 0, 0, 0, 0, 0, 0),
        Array(0, 0, 0, 0, 0, 0, 0),
        0,
        None,
        None
      )
  ): Unit = {
    this.prog = prog
    this.heap = state._1
    this.regfile = state._2
    this.pc = state._3
    this.f2e = state._4
    this.e2c = state._5
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

    init(
      Fibprog,
      (Array(0), initRegFile, 0, None, None)
    )

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

    init(
      Fibprog,
      (Array(0), initRegFile, 0, None, None)
    )

    val res = run_stages()

    val expected = Array(0, 610, 987, 987, 0, -1)
    assert(res === expected)

  }
  // tests addi
  test("proc 2 compare") {
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

  // tests early exit
  test("proc 3 compare") {
    val A = 1
    val B = 2
    val EarlyExit = List(
      Addi(A, A, 1),
      Addi(B, B, 1),
      Addi(A, A, -1),
      Exit(),
      Addi(B, B, -1),
      Exit()
    )

    init(EarlyExit)
    val res = run()
    val expected = Array(0, 0, 1, 0, 0, 0, 0)

    assert(res === expected)

    check(EarlyExit)
  }

  // tests branching
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

  // tests load and store
  test("proc 5 compare") {
    val testHeap = List(
      Load(1, 0, 0),
      Load(2, 1, 0),
      Load(3, 2, 0),
      Load(4, 3, 0),
      Load(5, 4, 0),
      Addi(1, 1, 2),
      Addi(2, 2, 3),
      Addi(3, 3, 4),
      Addi(4, 4, 5),
      Addi(5, 5, 6),
      Store(1, 0, 0),
      Store(2, 1, 0),
      Store(3, 2, 0),
      Store(4, 3, 0),
      Store(5, 4, 0),
      Exit()
    )

    init(testHeap)
    val res = run()
    val expected = Array(0, 2, 3, 4, 5, 6, 0)

    assert(res === expected)

    check(testHeap)
  }

}
