package lms.koika

import lms.core.stub._
import lms.core.virtualize
import lms.macros.SourceContext

@virtualize
class StagedProcInterp1bPC extends TutorialFunSuite {
  val under = "proci1b_staged_"

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
// cc file.c for execution
// cbmc -DCBMC file.c for verification
#ifndef CBMC
#define __CPROVER_assert(b,s) 0
#endif
int main(int argc, char *argv[]) {
  int regfile[7] = {0, 0, 0, 0, 0, 0, 0};
  Snippet(regfile);
"""
    var printexpected = s"""
  printf("\\nexpected:\\n");
  printf(""""
    for (i <- 0 until expected.length) {
      printexpected += s"""${expected(i)} """
    }
    printexpected += s""" ");
"""
    for (i <- 0 until expected.length) {
      ret += s"""
  __CPROVER_assert(regfile[$i]==${expected(i)}, "failure $i");
  if (regfile[$i] != ${expected(i)}) {
    printf("error: regfile[$i] = %d, expected ${expected(i)}\\n", regfile[$i]);
    goto error;
  }
"""
    }
    ret += s"""
  printf("OK\\n");
  return 0;
error:
  printf("\\nRegfile:\\n");
  for (int i = 0; i < 6; i++) {
    printf("%d ", regfile[i]);
  }
  ${printexpected}
  printf("\\n\\nFAILED\\n");
  return 1;

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
    case class JumpNZ(rs: Reg, imm: Int) extends Instruction
    case class JumpNeg(rs: Reg, imm: Int) extends Instruction

    val AddOp = 0
    val EqOp = 1
    val LtOp = 2

    val BrEqOp = -1
    val BrLtOp = -2

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

    class Port[T: Manifest](
        init: T,
        customEqual: Option[(Rep[T], Rep[T]) => Rep[Boolean]] = None
    ) {

      private var readport: Var[T] = __newVar(init)
      private var writeport: Var[T] = __newVar(init)

      private def equal(a: Rep[T], b: Rep[T]): Rep[Boolean] =
        customEqual match {
          case Some(f) => f(a, b)
          case None    => a == b
        }

      def read: Rep[T] = readVar(readport)

      def write(d: Rep[T]): Rep[Unit] = writeport = d

      def flush(): Rep[Unit] = writeport = init
      def freeze(): Rep[Unit] = ()

      def update(): Rep[Unit] = readport = writeport

      def isDefault: Rep[Boolean] = equal(read, unit(init))
      def isAmong(vs: T*): Rep[Boolean] =
        vs.foldLeft(unit(false))((acc, v) => acc || equal(read, unit(v)))
    }

    def println(s: String) = if (DEBUG) Predef.println(s) else ()

    def readProgram(file: String): Program = {
      scala.io.Source
        .fromFile(file)
        .getLines()
        .map { line =>
          val tokens = line.split(" ")
          tokens match {
            case Array("add", rd, rs1, rs2) =>
              Add(Reg(rd.toInt), Reg(rs1.toInt), Reg(rs2.toInt))
            case Array("addi", rd, rs1, imm) =>
              Addi(Reg(rd.toInt), Reg(rs1.toInt), imm.toInt)
            case Array("jumpnz", rs, imm) =>
              JumpNZ(Reg(rs.toInt), imm.toInt)
            case Array("jumpneg", rs, imm) =>
              JumpNeg(Reg(rs.toInt), imm.toInt)
            case _ => Predef.println(s"Unknown instruction: $line"); NOP
          }
        }
        .toList
    }

    def expectedResult(prog: Program): Array[Int] = {
      var rf: Array[Int] = List(0, 0, 0, 0, 0, 0, 0).toArray
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
          case JumpNZ(rs, target) => {
            if (rf(rs) != 0) i = i + target
            else i = i + 1
          }
          case JumpNeg(rs, target) => {
            if (rf(rs) < 0) i = i + target
            else i = i + 1
          }
        }
      }
      rf
    }

    def execute(
        f2e: Map[String, Port[Int]]
    ): (Rep[Int], Rep[Int], Rep[Boolean], Rep[Int]) = {
      val dst = f2e("dst").read
      val op1 = f2e("val1").read
      val op2 = f2e("val2").read
      val op = f2e("op").read

      val e_val =
        if (op == AddOp) op1 + op2
        else if (op == EqOp) if (op1 == op2) 1 else 0
        else if (op == LtOp) if (op1 < op2) 1 else 0
        else 0

      val e_dst = dst

      val pred = f2e("bpred").read
      val e_annul =
        if (e_val == 0) pred == 1
        else if (e_val == 1) pred == 2
        else false

      val delta = f2e("bdelta").read

      val e_nextpc =
        if (e_val == 0) f2e("pc").read + 1
        else if (e_val == 1) f2e("pc").read + delta
        else f2e("pc").read + 1

      (e_dst, e_val, e_annul, e_nextpc)
    }

    def BTB(pc: Rep[Int]): Rep[Int] = pc + 1

    def BPredict(pc: Rep[Int]): Rep[Boolean] = false

    def run(prog: Program, state: Rep[RegFile]): Rep[RegFile] = {
      val regfile: Rep[RegFile] = state

      var f2e: Map[String, Port[Int]] = Map(
        "dst" -> new Port[Int](0),
        "val1" -> new Port[Int](0),
        "val2" -> new Port[Int](0),
        "op" -> new Port[Int](0),
        "bpred" -> new Port[Int](0), // branch prediction
        // 0: not a branch, 1: branch taken, 2: branch not taken
        "bdelta" -> new Port[Int](0),
        "pc" -> new Port[Int](0)
      )

      var e2c: Map[String, Port[Int]] = Map(
        "dst" -> new Port[Int](0),
        "val" -> new Port[Int](0)
      )

      while (0 <= f2e("pc").read && f2e("pc").read < prog.length) {

        // pipeline update
        f2e.foreach { case (_, port) => port.update() }
        e2c.foreach { case (_, port) => port.update() }

        // Commit stage
        regfile(e2c("dst").read) = e2c("val").read

        // Execute stage
        val (e_dst, e_val, e_annul, e_nextpc) = execute(f2e)

        e2c("dst").write(e_dst)
        e2c("val").write(e_val)

        // Fetch stage

        val pc = f2e("pc").read
        val nextpc = BTB(pc)
        val predict = BPredict(pc)

        for (i <- (0 until prog.length): Range) {
          if (i == pc) {
            prog(i) match {
              case Add(rd, rs1, rs2) => {

                val stall = !((!e2c("dst").isAmong(rd, rs1, rs2)
                  || e2c("dst").isDefault)
                  && (!f2e("dst").isAmong(rd, rs1, rs2)
                    || f2e("dst").isDefault))

                if (e_annul) {
                  f2e.foreach {
                    case ("pc", p) => p.write(e_nextpc);
                    case (_, p)    => p.flush()
                  }
                } else if (stall) {
                  // stall
                  f2e.foreach {
                    case ("pc", p) => p.freeze(); case (_, p) => p.flush()
                  }
                } else {
                  f2e("dst").write(rd)
                  f2e("val1").write(regfile(rs1))
                  f2e("val2").write(regfile(rs2))
                  f2e("op").write(AddOp)
                  f2e("bpred").write(0)
                  f2e("bdelta").write(1)
                  f2e("pc").write(nextpc)
                }
              }

              case Addi(rd, rs1, imm) => {
                val stall = !((!e2c("dst").isAmong(rd, rs1)
                  || e2c("dst").isDefault)
                  && (!f2e("dst").isAmong(rd, rs1)
                    || f2e("dst").isDefault))

                if (e_annul) {
                  f2e.foreach {
                    case ("pc", p) => p.write(e_nextpc);
                    case (_, p)    => p.flush()
                  }
                } else if (stall) {
                  // stall
                  f2e.foreach {
                    case ("pc", p) => p.freeze(); case (_, p) => p.flush()
                  }
                } else {
                  f2e("dst").write(rd)
                  f2e("val1").write(regfile(rs1))
                  f2e("val2").write(imm)
                  f2e("op").write(AddOp)
                  f2e("bpred").write(0)
                  f2e("bdelta").write(1)
                  f2e("pc").write(nextpc)
                }
              }

              case JumpNZ(rs, target) => {
                val stall =
                  !(e2c("dst").read != rs.id && f2e("dst").read != rs.id)

                if (e_annul) {
                  f2e.foreach {
                    case ("pc", p) => p.write(e_nextpc);
                    case (_, p)    => p.flush()
                  }
                } else if (stall) {
                  f2e.foreach {
                    case ("pc", p) => p.freeze(); case (_, p) => p.flush()
                  }
                } else {
                  f2e("dst").write(ZERO)
                  f2e("val1").write(regfile(rs))
                  f2e("val2").write(0)
                  f2e("op").write(EqOp)
                  f2e("bpred").write(2)
                  f2e("bdelta").write(target)
                  f2e("pc").write(nextpc)
                }

              }
              case JumpNeg(rs, target) => {
                val stall =
                  !(e2c("dst").read != rs.id && f2e("dst").read != rs.id)

                if (e_annul) {
                  f2e.foreach {
                    case ("pc", p) => p.write(e_nextpc);
                    case (_, p)    => p.flush()
                  }
                } else if (stall) {
                  f2e.foreach {
                    case ("pc", p) => p.freeze(); case (_, p) => p.flush()
                  }
                } else {
                  f2e("dst").write(ZERO)
                  f2e("val1").write(regfile(rs))
                  f2e("val2").write(0)
                  f2e("op").write(LtOp)
                  f2e("bpred").write(2)
                  f2e("bdelta").write(target)
                  f2e("pc").write(nextpc)
                }
              }
            }
          }
        }

      }

      // let the pipeline flush
      e2c("dst").update()
      e2c("val").update()

      f2e("dst").update()
      f2e("val1").update()
      f2e("val2").update()
      f2e("op").update()

      regfile(e2c("dst").read) = e2c("val").read

      val (e_dst, e_val, e_annul, e_nextpc) = execute(f2e)

      e2c("dst").write(e_dst)
      e2c("val").write(e_val)

      e2c("dst").update()
      e2c("val").update()

      regfile(e2c("dst").read) = e2c("val").read

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
        Addi(F_n, ZERO, 1),
        Addi(F_n_1, ZERO, 0),
        Addi(N, ZERO, 15),
        Addi(Temp, ZERO, 0),
        Add(Temp, F_n, F_n_1),
        Add(F_n_1, F_n, ZERO),
        Add(F_n, Temp, ZERO),
        Addi(N, N, -1),
        JumpNZ(N, -4)
      )
      val expected = expectedResult(Fibprog)
      override val main = constructMain(expected)
      def snippet(initRegFile: Rep[RegFile]) = {

        run(Fibprog, initRegFile)
      }
    }
    exec("1", snippet.code)
  }

  test("proc rar hazard") {
    val snippet = new DslDriverX[Array[Int], Array[Int]] with Interp {
      val prog = List(
        Addi(A1, A0, 1), //
        Addi(A3, A0, 2), // RAR
        Addi(A2, A4, 3) // NO RAR
      )
      val expected = expectedResult(prog)
      override val main = constructMain(expected)
      def snippet(initRegFile: Rep[RegFile]) = {
        run(prog, initRegFile)
      }
    }
    exec("rar_hazard", snippet.code)
  }

  test("proc waw hazard") {
    val snippet = new DslDriverX[Array[Int], Array[Int]] with Interp {
      val prog = List(
        Addi(A0, ZERO, 1),
        Addi(A0, A0, 1), // WAW
        Addi(A3, A2, 2) // NO WAW
      )
      val expected = expectedResult(prog)
      override val main = constructMain(expected)
      def snippet(initRegFile: Rep[RegFile]) = {
        run(prog, initRegFile)
      }
    }
    exec("waw_hazard", snippet.code)
  }

  test("proc raw hazard") {
    val snippet = new DslDriverX[Array[Int], Array[Int]] with Interp {
      val prog = List(
        Addi(A0, ZERO, 1),
        Addi(A1, A0, 1), // RAW
        Addi(A3, A2, 2) // NO RAW
      )
      val expected = expectedResult(prog)
      override val main = constructMain(expected)
      def snippet(initRegFile: Rep[RegFile]) = {
        run(prog, initRegFile)
      }
    }
    exec("raw_hazard", snippet.code)
  }

  test("proc war hazard") {
    val snippet = new DslDriverX[Array[Int], Array[Int]] with Interp {
      val prog = List(
        Addi(A1, A0, 1), //
        Addi(A0, A3, 2), // WAR
        Addi(A2, A4, 3) // NO WAR
      )
      val expected = expectedResult(prog)
      override val main = constructMain(expected)
      def snippet(initRegFile: Rep[RegFile]) = {
        run(prog, initRegFile)
      }
    }
    exec("war_hazard", snippet.code)
  }

  test("proc loop") {
    val snippet = new DslDriverX[Array[Int], Array[Int]] with Interp {
      val prog = List(
        Addi(A0, ZERO, 3),
        Addi(A0, A0, -1),
        JumpNZ(A0, -1)
      )
      val expected = expectedResult(prog)
      override val main = constructMain(expected)
      def snippet(initRegFile: Rep[RegFile]) = {
        run(prog, initRegFile)
      }
    }
    exec("loop_hazard", snippet.code)
  }

  test("proc hazard") {
    val snippet = new DslDriverX[Array[Int], Array[Int]] with Interp {
      val prog = List(
        Addi(A0, ZERO, 1),
        Add(A1, A0, A0), // RAW
        Add(A2, A1, A0),
        Add(A3, A2, A1),
        Add(A0, A3, A2), // RAW
        Add(A1, A0, A3), // RAW, RAR
        Add(A2, A1, A0), // RAW, RAR
        Add(A3, A2, A1), // RAW, RAR
        Add(A3, A0, A3) // WAW, RAW
      )
      val expected = expectedResult(prog)
      override val main = constructMain(expected)
      def snippet(initRegFile: Rep[RegFile]) = {
        run(prog, initRegFile)
      }
    }
    exec("hazard", snippet.code)

  }

  test("proc stress") {
    // read from file 1.asm and get the program
    val snippet = new DslDriverX[Array[Int], Array[Int]] with Interp {
      val filename = "src/out/1.asm"
      val program = readProgram(filename)
      val expected: Array[Int] = expectedResult(program)
      override val main = constructMain(expected)

      def snippet(initRegFile: Rep[RegFile]) = {
        run(program, initRegFile)
      }

    }
    exec("stress", snippet.code)
  }

}
