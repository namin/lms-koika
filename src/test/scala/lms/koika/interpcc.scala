package lms.koika

import lms.core.stub._
import lms.core.virtualize
import lms.macros.SourceContext

@virtualize
class InterpCcTest extends TutorialFunSuite {
  val under = "interpcc_"

  override def exec(label: String, code: String, suffix: String = "c") =
    super.exec(label, code, suffix)

  override def check(label: String, code: String, suffix: String = "c") =
    super.check(label, code, suffix)

  type stateT = Array[Int]
  trait InterpCc extends Dsl with lms.thirdparty.CLibs {
    def state_reg(s: Rep[stateT], i: Rep[Int]): Rep[Int] =
      s(i)
    def set_state_reg(s: Rep[stateT], i: Rep[Int], v: Rep[Int]): Rep[Unit] =
      s(i) = v

    abstract sealed class Instruction
    case class Add(rd: Int, rs1: Int, rs2: Int) extends Instruction
    case class Branch(rs: Int, target: Int) extends Instruction

    val prog: Vector[Instruction] = Vector(Add(0, 0, 0), Branch(0, 0))

    val cache: Array[Option[Rep[stateT => Unit]]] = (for (p <- prog) yield None).toArray

    def call(i: Int, s: Rep[stateT]): Rep[Unit] = if (i < cache.length) {
      val f = cache(i) match {
        case None => {
          val f = topFun { (s: Rep[stateT]) => execute(i, s) }
          cache(i) = Some(f)
          f
        }
        case Some(f) => f
      }
      f(s)
    }

    def execute(i: Int, s: Rep[stateT]): Rep[Unit] = if (i < prog.length) {
      prog(i) match {
        case Add(rd, rs1, rs2) => {
          set_state_reg(s, rd, state_reg(s, rs1) + state_reg(s, rs2))
          call(i+1, s)
        }
        case Branch(rs, target) => {
          if (state_reg(s, rs) == unit(0)) {
            call(target, s)
          } else {
            call(i+1, s)
          }
        }
      }
    }
  }

  abstract class DslDriverX[A:Manifest,B:Manifest] extends DslDriverC[A,B] { q =>
    override val codegen = new DslGenC with lms.thirdparty.CCodeGenLibs {
      val IR: q.type = q

      registerHeader("\"state.h\"")

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
    |int main(int argc, char *argv[]) {
    |  if (argc != 2) {
    |    printf("usage: %s <arg>\n", argv[0]);
    |    return 0;
    |  }""".stripMargin)
        if (initStream.size > 0) emitln("if (init()) return 0;")
        emitln(s"  $name(${convert("argv[1]", m1)});\n  return 0;\n}")
      }
    }
  }

  test("interp 1") {
    val snippet = new DslDriverX[stateT,Unit] with InterpCc {
      def snippet(s: Rep[stateT]): Rep[Unit] = execute(0, s)
    }
    check("1", snippet.code)
  }

}
