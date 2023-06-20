package lms.koika

import lms.core.stub._
import lms.core.virtualize
import lms.macros.SourceContext

@virtualize
class StagedProcInterp1bPC extends TutorialFunSuite {
  val under = "proci1b_staged_"

  override def exec(label: String, code: String, suffix: String = "c") =
    super.exec(label, code, suffix)

  override def check(label: String, code: String, suffix: String = "c") =
    super.check(label, code, suffix)

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
      val regfile: RegFile = state._1
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

  abstract class DslDriverX[A:Manifest,B:Manifest] extends DslDriverC[A,B] { q =>
    val main: String = ""

    override val codegen = new DslGenC {
      val IR: q.type = q

      override def emitAll(g: lms.core.Graph, name: String)(m1:Manifest[_],m2:Manifest[_]): Unit = {
        val ng = init(g)
        val efs = "" //quoteEff(g.block.ein)
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
    val snippet = new DslDriverX[Array[Int], Int] with Interp {
      override val main = """
int main(int argc, char *argv[]) {
  int regfile[6] = {0, 0, 1, 0, 15, -1};
  int r = Snippet(regfile);
  printf("%d\n", r);
  return 0;
}
"""
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
