package lms.koika

// TODO: use something better than an Exit instruction


// Models a single cycle cache
trait cache {
  type Heap = Array[Int]
  var heap: Heap =
    Array(0)

  def available: Boolean
  def read(addr: Int): Unit
  def write(addr: Int, value: Int): Unit
  def output: Option[Int]

  def get_heap: Heap
  def reset: Unit
}

class MagicMem extends cache {
  var toReturn: Option[Int] = None

  def available: Boolean = true

  def read(addr: Int): Unit = {
    toReturn = Some(heap(addr))
  }

  def write(addr: Int, value: Int): Unit = {
    heap(addr) = value
  }

  def output: Option[Int] = toReturn

  def reset: Unit = {
    heap = Array.fill(10)(0)
    toReturn = None
  }

  def get_heap: Heap = heap

}


// Interpreter for a 3-stage pipelined processor
// Fetch, Execute, Commit
//
// Each stage is modeled as a function that modies the state of the processor class.
// All three stages are orchestrated by the run_stages function.
//
// Fetch: fetches the next instruction - Right now, it just copies the instruction from the program.
//        After the inclusion of iCache, it will read from the iCache.
//
// Execute: executes the instruction and produces a value to be committed.
//
// Commit: commits the value to the register file.
class ProcInterpPC extends TutorialFunSuite {
  val under = "proci1_"

  val DEBUG = false 
  val MAX_STEPS = 1000
  
  case class Reg(id: Int)

  // transform Reg to Int implicitly
  implicit def reg2int(reg: Reg): Int = reg.id


  val dCache: cache = new MagicMem

  val ZERO: Reg = Reg(0)
  val A0: Reg = Reg(1)
  val A1: Reg = Reg(2)
  val A2: Reg = Reg(3)
  val A3: Reg = Reg(4)
  val A4: Reg = Reg(5)
  val A5: Reg = Reg(6)

  val NOP = Addi(ZERO, ZERO, 0)


  abstract sealed class Instruction
  case class Add(rd: Reg, rs1: Reg, rs2: Reg) extends Instruction
  case class Addi(rd: Reg, rs1: Reg, imm: Int) extends Instruction
  case class BrNEZ(rs: Reg, imm: Int) extends Instruction
  case class Load(rd: Reg, rs1: Reg, imm: Int) extends Instruction
  case class Store(rs1: Reg, rs2: Reg, imm: Int) extends Instruction // *(rs2 + imm) = rs1
  case class Exit() extends Instruction

  type Program = List[Instruction]
  type RegFile = Array[Int]
  type PC = Int
  type F2E = (PC, Instruction)
  type E2C =
    (PC, Option[Reg], Int, PC, Boolean) // (PC, rd, value, nextPC, finished)

  type State = (RegFile, PC, Option[F2E], Option[E2C])

  var regfile: RegFile = Array(0, 0, 0, 0, 0, 0, 0)
  var pc: PC = 0 // pc register used by the fetch stage
  var f2e: Option[F2E] =
    None //  fetch to execute stage, read by the execute stage
  var e2c: Option[E2C] =
    None // execute to commit stage, read by the commit stage
  var prog: Program = List(NOP)

  def log(): Unit = {
    if (DEBUG) {
      val str: String = s"regfile: ${this.regfile.mkString(",")}\n" +
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
          dCache.read(this.regfile(rs1) + imm)
          (fpc, Some(rd), dCache.output.get, fpc + 1, false)

        case Store(rs1, rs2, imm) =>
          dCache.write(this.regfile(rs2) + imm, this.regfile(rs1))
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
  // returns true if the program is done
  def commit(): Boolean = {
    this.e2c match {
      case Some(e2c_) =>
        val (fpc, rd, value, nextPC, break) = e2c_
        rd map (regfile(_) = value)
        break
      case None => false
    }
  }

  def run_stages(): RegFile = {
    var cnt = 0
    var continue = true
    while (cnt < MAX_STEPS && continue) {

      // driver for the three stages
      var break = commit()
      this.e2c = exec()
      this.f2e = fetch()

      // Revert in the case of misprediction
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

  // A single cycle implementation for debugging
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
          dCache.read(this.regfile(rs) + offset)
          this.regfile(rd) = dCache.output.get
          pc + 1

        case Store(rs1, rs2, offset) =>
          dCache.write(this.regfile(rs2) + offset, this.regfile(rs1))
          pc + 1

        case Exit() => prog.length
        case _ =>
          println(s"unknown instruction: ${prog(pc)}")
          assert(false)
          pc + 1
      }
      cnt += 1
    }
    this.regfile
  }

  def get_heap(): Array[Int] = {
    dCache.get_heap
  }

  def init(
      prog: Program,
      state: State = (
        Array(0, 0, 0, 0, 0, 0, 0),
        0,
        None,
        None
      )
  ): Unit = {
    this.prog = prog
    val (regfile, pc, f2e, e2c) = state
    this.regfile = regfile
    this.pc = pc
    this.f2e = f2e
    this.e2c = e2c
    dCache.reset
  }

  // compare run_stages with run on a given program
  // with the standard initial state
  //
  // Used to test the correctness of the run_stages method
  private def check(prog: Program) = {
    init(prog)
    val res = run().clone()
    val res_heap = get_heap().clone()
    init(prog)
    val res_stages = run_stages().clone()
    val res_stages_heap = get_heap().clone()
    assert(res === res_stages)
    assert(res_heap === res_stages_heap)
  }

  test("proc 1 run") {
    val initRegFile = Array(0, 0, 1, 0, 15, -1)
    val N = A3
    val Temp = A2
    val F_n = A1
    val F_n_1 = A0
    val Zero = ZERO
    val MinusOne = A4
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
      (initRegFile, 0, None, None)
    )

    val res = run()
    val expected = Array(0, 610, 987, 987, 0, -1)

    assert(res === expected)
  }

  test("proc 1 run stages") {
    val initRegFile = Array(0, 0, 1, 0, 15, -1)
    val N = A3
    val Temp = A2
    val F_n = A1
    val F_n_1 = A0
    val Zero = ZERO
    val MinusOne = A4
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
      (initRegFile, 0, None, None)
    )

    val res = run_stages()

    val expected = Array(0, 610, 987, 987, 0, -1)
    assert(res === expected)
  }

  // tests addi
  test("proc 2 compare") {
    val N = A3
    val Temp = A2
    val F_n = A1
    val F_n_1 = A0
    val Zero = ZERO

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
    val A = A0
    val B = A1
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
    val N = ZERO

    val FibTri = List(
      Addi(A4, A4, 1),
      Addi(N, N, 4),
      Add(A0, A0, A1),
      Add(A1, A1, A2),
      Add(A2, A2, A3),
      Add(A3, A3, A4),
      Add(A4, A4, A5),

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

    val addr: Reg = A3
    val N: Reg = A4

    val FibOnHeap = List(
      Addi(N, N, 8),
      Addi(A5, ZERO, 1),
      Store(A5, ZERO, 1),
      Addi(addr, ZERO, 0),
      NOP,
      NOP,
      Load(A0, addr, 0),
      Load(A1, addr, 1),
      Add(A2, A0, A1),
      Store(A2, addr, 2),
      Addi(addr, addr, 1),
      Addi(N, N, -1),
      BrNEZ(N, -6),
      Exit()
    )

    init(FibOnHeap)
    val res = run()
    val expected = Array(0, 13, 21, 34, 8, 0, 1)
    val expected_heap = Array(0, 1, 1, 2, 3, 5, 8, 13, 21, 34)

    assert(get_heap() === expected_heap)

    assert(res === expected)
  }

}
