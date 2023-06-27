package lms.koika

import lms.core.stub._
import lms.core.virtualize
import lms.macros.SourceContext


// TODO: use topFun in interpcc, look at call. 
// topFun solves the function call problem. (Prog => (Rep[A=>B]))
@virtualize
class StagedProcInterp0b extends TutorialFunSuite {
  val under = "proci0b_staged_"

  val regfile_main = """
int main(int argc, char *argv[]) {
  int regfile[7] = {0, 0, 0, 0, 0, 0, 0};
  Snippet(regfile);
  for (int i = 0; i < 6; i++) {
    printf("%d ", regfile[i]);
  }
  printf("\n");
  return 0;
}
"""

  def constructMain(expected: Array[Int]): String = {
    var ret = s"""
int main(int argc, char *argv[]) {
  int regfile[7] = {0, 0, 0, 0, 0, 0, 0};
  Snippet(regfile);
"""
    for (i <- 0 until expected.length) {
      ret += s"""
  if (regfile[$i] != ${expected(i)}) {
    printf("error: regfile[$i] = %d, expected ${expected(i)}\\n", regfile[$i]);
    return 1;
  }
"""
    }
    ret += """
  printf("OK\n");
  return 0;
}
"""
    ret
  }
  override def exec(label: String, code: String, suffix: String = "c") =
    super.exec(label, code, suffix)

  override def check(label: String, code: String, suffix: String = "c") =
    super.check(label, code, suffix)

  val DEBUG = true

  trait Interp extends Dsl {

    abstract sealed class Instruction
    case class Add(rd: Reg, rs1: Reg, rs2: Reg) extends Instruction
    case class Addi(rd: Reg, rs1: Reg, imm: Int) extends Instruction
    case class BrTarget(id: String) extends Instruction
    case class BrNEZ(rs: Reg, id: String) extends Instruction

    type Program = List[Instruction]
    type RegFile = Array[Int]

    case class Reg(id: Int)
    val ZERO: Reg = Reg(0)
    val A0: Reg = Reg(1)
    val A1: Reg = Reg(2)
    val A2: Reg = Reg(3)
    val A3: Reg = Reg(4)
    val A4: Reg = Reg(5)
    val A5: Reg = Reg(6)

    val NOP = Addi(ZERO, ZERO, 0)

    implicit def reg2int(r: Reg): Int = r.id
    implicit def reg2rep(r: Reg): Rep[Int] = unit(r.id)

    type State = RegFile

    def println(s: String) = if (DEBUG) Predef.println(s) else ()

    def readProgram(file: String): Program = {
      scala.io.Source
        .fromFile(file)
        .getLines()
        .map { line =>
          val tokens = line.split(" ")
          tokens(0) match {
            case "add" =>
              Add(
                Reg(tokens(1).toInt),
                Reg(tokens(2).toInt),
                Reg(tokens(3).toInt)
              )
            case "addi" =>
              Addi(Reg(tokens(1).toInt), Reg(tokens(2).toInt), tokens(3).toInt)
            case "br" => BrNEZ(Reg(tokens(1).toInt), tokens(2))
            case "target" => BrTarget(tokens(1))
            case _    => println(s"Unknown instruction: $line"); NOP
          }
        }
        .toList
    }

    def expectedResult(prog: Program): Array[Int] = {
      var rf: Array[Int] = List(0, 0, 0, 0, 0, 0, 0).toArray
      var id_to_pc: Map[String, Int] = Map[String, Int]()
      prog.foreach {
        case BrTarget(id) =>
          id_to_pc += (id -> prog.indexWhere(_ == BrTarget(id)))
        case _ => ()
      }
      var i: Int = 0
      while (i < prog.length) {
        prog(i) match {
          case Add(rd, rs1, rs2) => {
            rf(rd) = rf(rs1) + rf(rs2)
            i = i + 1
          }
          case Addi(rd, rs1, imm) => {
            rf(rd) = rf(rs1) + imm
            i = i + 1
          }
          case BrNEZ(rs, target) => {
            if (rf(rs) != 0) i = id_to_pc(target)
            else i = i + 1
          }
          case BrTarget(id) => i = i + 1
        }
      }
      rf
    }

    def run(prog: Program, state: Rep[State]): Rep[RegFile] = {
      val regfile: Rep[RegFile] = state
      var id_to_prog: Map[String, Program] = Map[String, Program]()
      prog.foreach {
        case BrTarget(id) =>
          id_to_prog += (id -> prog.dropWhile(_ != BrTarget(id)).tail)
        case _ => ()
      }

      var curblock: Rep[String] = "entry" //
      // var curidx: Rep[Int] = id_to_prog.indexWhere(_._1 == "entry") //
      // val endidx: Int = id_to_prog.indexWhere(_._1 == "exit")
      var curprog: Program = prog
      var endprog: Rep[Boolean] = false
      while (!endprog) {
        for (block <- id_to_prog.keys) {
          if (block == curblock) {
            curprog = id_to_prog(block)
            println(s"curblock at start ${curblock}")
            println(s"curprog: $curprog")

            var break = false
            for (i <- (0 until curprog.length): Range) {
              if (!break) {
                curprog(i) match {
                  case Add(rd, rs1, rs2) => {
                    regfile(rd) = regfile(rs1) + regfile(rs2)
                    println("Add")
                  }

                  case Addi(rd, rs1, imm) => {
                    regfile(rd) = regfile(rs1) + imm
                    println("Addi")
                  }

                  case BrNEZ(rs, target) =>
                    if (regfile(rs) != 0) {
                      println(s"returning target $target")
                      curblock = target
                      break = true
                    } else {
                      println(s"not returning target $target")
                    }

                  case BrTarget(id) => {
                    curblock = id
                    break = true
                    println(s"target? $id")
                  }
                }
              }
            }
            println(s"curblock at end ${curblock}")
          }
          if (curblock == "exit") {
            endprog = true
          }

        }
        // for (i <- (0 until id_to_prog.length): Range) {
        //  if (id_to_prog(i)._1 == curblock) {
        //    curblock = "exit"
        //  }
        // }

      }
      regfile

    }
  }

  abstract class DslDriverX[A: Manifest, B: Manifest] extends DslDriverC[A, B] {
    q =>
    val main: String = ""

    override val codegen = new DslGenC {
      val IR: q.type = q

      override def emitAll(
          g: lms.core.Graph,
          name: String
      )(m1: Manifest[_], m2: Manifest[_]): Unit = {
        val ng = init(g)
        val efs = "" // quoteEff(g.block.ein)
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
    val snippet = new DslDriverX[Array[Int], Array[Int]] with Interp {
      val N = A3
      val Temp = A2
      val F_n = A1
      val F_n_1 = A0
      val Fibprog = List(
        BrTarget("entry"),
        Addi(F_n, ZERO, 1),
        Addi(F_n_1, ZERO, 0),
        Addi(N, ZERO, 15),
        Addi(Temp, ZERO, 0),
        BrTarget("loop"),
        Add(Temp, F_n, F_n_1),
        Add(F_n_1, F_n, ZERO),
        Add(F_n, Temp, ZERO),
        Addi(N, N, -1),
        BrNEZ(N, "loop"),
        BrTarget("exit")
      )
      val expected = expectedResult(Fibprog)
      override val main = constructMain(expected)

      def snippet(initRegFile: Rep[RegFile]) = {
        run(Fibprog, (initRegFile))
      }
    }
    exec("1", snippet.code)
  }
}
