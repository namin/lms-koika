package lms.koika

class ProcInterp extends TutorialFunSuite {
  val under = "proci0_"

  type Reg = Int

  val DEBUG = false

  abstract sealed class Instruction
  case class Add(rd: Reg, rs1: Reg, rs2: Reg) extends Instruction
  case class Addi(rd: Reg, rs1: Reg, imm: Int) extends Instruction
  case class BrTarget(id: String) extends Instruction
  case class BrNEZ(rs: Reg, id: String) extends Instruction

  type Program = List[Instruction]
  type RegFile = Array[Int]

  type State = (RegFile, Program)

//  var F2C = 

  def println(s: String) = if (DEBUG) Predef.println(s) else ()

  def mkString(state: State): String = {
    val (regFile, program) = state
    s"regFile: ${regFile.mkString(",")}\n" +
      s"program: ${program.mkString(",")}"
  }


  def run(state: State): RegFile = {
    val (regFile, program) = state
    var curstate = state
    var id_to_prog = Map[String, Program]()
    program.foreach {
      case BrTarget(id) =>
        id_to_prog += (id -> program.dropWhile(_ != BrTarget(id)).tail)
      case _ => ()
    }
    while (!curstate._2.isEmpty) {
      println(mkString(curstate))
      val (regFile, program) = curstate
      curstate = program match {
        case Add(rd, rs1, rs2) :: rest =>
          regFile(rd) = regFile(rs1) + regFile(rs2)
          (regFile, rest)

        case Addi(rd, rs1, imm) :: rest =>
          regFile(rd) = regFile(rs1) + imm
          (regFile, rest)

        case BrNEZ(rs, target) :: rest =>
          (regFile, (if (regFile(rs) != 0) id_to_prog(target) else rest))

        case BrTarget(id) :: rest =>
          (regFile, rest)

        case Nil => (regFile, Nil)
      }
    }
    curstate._1
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
      BrTarget("start"),
      Add(Temp, F_n, F_n_1),
      Add(F_n_1, F_n, Zero),
      Add(F_n, Temp, Zero),
      Add(N, N, MinusOne),
      BrNEZ(N, "start")
    )

    val state = (initRegFile, Fibprog)
    val res = run(state)
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
      
      BrTarget("start"),
      Add(Temp, F_n, F_n_1),
      Add(F_n_1, F_n, Zero),
      Add(F_n, Temp, Zero),
      Addi(N, N, -1),
      BrNEZ(N, "start")
    )

    val state = (initRegFile, Fibprog)
    val res = run(state)
    val expected = Array(0, 610, 987, 987, 0, 0, 0)

    assert(res === expected)

  }
}
