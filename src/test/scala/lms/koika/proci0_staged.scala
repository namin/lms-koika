package lms.koika



// EXPERIMENTAL
//
// This is an experimental implementation of a single-cycle processor
// interpreter. The goal is to get rid of PC and use labels instead.
//
// Maybe it would be more suitable for LMS since it is more functional
class ProcInterpStaged extends TutorialFunSuite {
  val under = "proci0_"

  val DEBUG = false 
  val MAX_STEPS = 1000

  case class Reg(id: Int)

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
  case class BrTarget(id: String) extends Instruction
  case class BrNEZ(rs: Reg, id: String) extends Instruction

  type Program = List[Instruction]
  type RegFile =
    Map[Reg, Int] // todo: consider using Array[Int] and perform translation

  var regfile: RegFile = Map[Reg, Int]()
  var id_to_prog = Map[String, Program]()
  var program: Program = List(NOP)

  def log(): Unit = {
    if (DEBUG) {
      var regfilestr = ""
      regfile.foreach { case (reg, value) =>
        regfilestr += s"${reg.id}: $value, "
      }
      val str: String = s"regfile: ${regfilestr}\n" +
        s"program: ${program.mkString("\n")}\n"

      println(str)
    }
  }

  def println(str: String): Unit = {
    if (DEBUG) {
      Predef.println(str)
    }
  }

  def buildmap(program: Program): Unit =
    program.foreach {
      case BrTarget(id) =>
        id_to_prog += (id -> program.dropWhile(_ != BrTarget(id)).tail)
      case _ => ()
    }

  def init(
      program: Program,
      regfile: RegFile = ((0 to 6).map(Reg(_) -> 0)).toMap
  ): Unit = {
    this.id_to_prog = Map[String, Program]()
    buildmap(program)
    this.program = program
    this.regfile = regfile
  }

  def run(): RegFile = {
    var cnt = 0
    while (!program.isEmpty && cnt < MAX_STEPS) {
      program = program match {
        case Add(rd, rs1, rs2) :: rest if rd != 0 =>
          regfile = regfile + (rd -> (regfile(rs1) + regfile(rs2)))
          rest

        case Addi(rd, rs1, imm) :: rest if rd != 0 =>
          regfile = regfile + (rd -> (regfile(rs1) + imm))
          rest

        case BrNEZ(rs, target) :: rest =>
          (if (regfile(rs) != 0) id_to_prog(target) else rest)

        case BrTarget(id) :: rest =>
          rest

        case Nil => Nil
      }
      cnt += 1
      log()
    }
    if (cnt >= MAX_STEPS) {
      println(s"MAX_STEPS($MAX_STEPS) exceeded")
    }
    regfile
  }

  test("proc 1") {
    val initRegFile = Array(0, 0, 1, 0, 15, -1).zipWithIndex.map {
      case (v, i) => Reg(i) -> v
    }.toMap
    val N = A3
    val Temp = A2
    val F_n = A1
    val F_n_1 = A0
    val Zero = ZERO
    val MinusOne = A4
    val Fibprog = List(
      BrTarget("start"),
      Add(Temp, F_n, F_n_1),
      Add(F_n_1, F_n, Zero),
      Add(F_n, Temp, Zero),
      Add(N, N, MinusOne),
      BrNEZ(N, "start")
    )
    init(Fibprog, initRegFile)
    val res = run()
    val expected = Array(0, 610, 987, 987, 0, -1).zipWithIndex.map {
      case (v, i) => Reg(i) -> v
    }.toMap

    assert(res === expected)
  }

  test("proc 2") {
    val N = A3
    val Temp = A2
    val F_n = A1
    val F_n_1 = A0

    val Fibprog = List(
      Addi(F_n, ZERO, 1),
      Addi(F_n_1, ZERO, 0),
      Addi(N, ZERO, 15),
      Addi(Temp, ZERO, 0),
      BrTarget("start"),
      Add(Temp, F_n, F_n_1),
      Add(F_n_1, F_n, ZERO),
      Add(F_n, Temp, ZERO),
      Addi(N, N, -1),
      BrNEZ(N, "start")
    )

    init(Fibprog)
    val res = run()
    val expected = Array(0, 610, 987, 987, 0, 0, 0).zipWithIndex.map {
      case (v, i) => Reg(i) -> v
    }.toMap

    assert(res === expected)

  }
}
