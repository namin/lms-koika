package lms.koika.demos

import lms.core.stub._
import lms.core.virtualize
import lms.macros.SourceContext
import lms.macros.RefinedManifest
import lms.collection.mutable._

import lms.koika.frontend.NanoRisc
import lms.koika.frontend.NanoRisc._

@virtualize
object KoikaInterp {
  // CR cwong: We currently don't have a good way to have a minimal [StateT]
  // that gets extended by later consumers.
  @CStruct
  case class StateT
    ( regs: Array[Int]
    , mem: Array[Int]
    , saved_regs: Array[Int]
    , cache_key: Int
    , cache_val: Int
    , timer: Int
    )

  trait Common extends Dsl with NanoRisc.Ops with StateTOps {
    val prog: Vector[NanoRisc.Instr]
    val useCache: Boolean

    lazy val cache: Array[Option[Rep[StateT => StateT]]] =
      (for (p <- prog) yield None).toArray

    def get_reg(s: Rep[StateT], i: Rep[Int]): Rep[Int]
    def set_reg(s: Rep[StateT], i: Rep[Int], v: Rep[Int]): Rep[Unit]
    def get_mem(s: Rep[StateT], i: Rep[Int]): Rep[Int]
    def set_mem(s: Rep[StateT], i: Rep[Int], v: Rep[Int]): Rep[Unit]

    def tick(s: Rep[StateT]): Rep[Unit] = s.timer += 1

    def operand(s: Rep[StateT], vl: Operand): Rep[Int] =
      vl match {
        case Imm(i) => i
        case Reg(i) => get_reg(s, i)
      }

    // The indirection via `execute` is necessary to generate functions for
    // each instruction.
    def execute(i: Int, s: Rep[StateT]): Rep[StateT]
    def call(i: Int, s: Rep[StateT]): Rep[StateT] =
      if (useCache) {
        if (i < cache.length) {
          val f = cache(i) match {
            case None => {
              val f = topFun { (s: Rep[StateT]) => execute(i, s) }
              cache(i) = Some(f)
              f
            }
            case Some(f) => f
          }
          f(s)
        }
        else {
          s
        }
      }
      else {
        execute(i, s)
      }
  }

  trait Naive extends Common {
    override val useCache = true

    override def get_reg(s: Rep[StateT], i: Rep[Int]): Rep[Int] =
      s.regs(i)
    override def set_reg(s: Rep[StateT], i: Rep[Int], v: Rep[Int]): Rep[Unit] =
      s.regs(i) = v

    override def get_mem(s: Rep[StateT], i: Rep[Int]): Rep[Int] =
      s.mem(i)
    override def set_mem(s: Rep[StateT], i: Rep[Int], v: Rep[Int]): Rep[Unit] =
      s.mem(i) = v

    def execute(i: Int, s: Rep[StateT]): Rep[StateT] =
      if (i < prog.length) {
        tick(s)
        prog(i) match {
          case Mov(dst, src) => {
            set_reg(s, dst.unReg, operand(s, src))
            call(i+1, s)
          }
          case Binop(op, dst, src1, src2) => {
            set_reg(s, dst.unReg, eval_op(op, operand(s, src1), operand(s, src2)))
            call(i+1, s)
          }
          case Load(dst, src, im) => {
            set_reg(s, dst.unReg, get_mem(s, operand(s, src) + operand(s, im)))
            call(i+1, s)
          }
          case Store(dst, src, im) => {
            set_mem(s, operand(s, src) + operand(s, im), operand(s, dst))
            call(i+1, s)
          }
          case B(mcmp, tgt) => mcmp match {
            case None => call(tgt.unAddr, s)
            case Some((cmp, src1, src2)) =>
              if (eval_cmp(cmp, operand(s, src1), operand(s, src2))) {
                call(tgt.unAddr, s)
              }
              else {
                call(i+1, s)
              }
          }
        }
      }
      else {
        s
      }
  }
}

abstract class GenericKoikaDriver[A:Manifest, B:Manifest] extends DslDriverC[A,B] { q =>
  val num_regs: Int = 8
  val mem_size: Int = 30
  val secret_size: Int = 10
  val secret_offset: Int = 20

  val header: String = s"""
#define NUM_REGS $mem_size
#define SECRET_SIZE $secret_size
#define SECRET_OFFSET $secret_offset
int nondet_uint();
int bounded(int low, int high) {
int x = nondet_uint();
  if (x < low) {
    x = low;
  }
  if (x > high) {
    x = high;
  }
  return x;
}"""

  val stateT: String = "StateT"
  val init: String

  val initialize_input: String = """
int x = bounded(0, 20);
s1.regs[0] = x;
s2.regs[0] = x;"""

  val initialize_secret: String = """
// initialize secret
for (i=0; i<SECRET_SIZE; i++) {
  s1.mem[i+SECRET_OFFSET] = bounded(0, 20);
  s2.mem[i+SECRET_OFFSET] = bounded(0, 20);
}"""

  val main: String = s"""
$header
$init
int main(int argc, char* argv[]) {
  struct $stateT s1, s2;
  init(&s1);
  init(&s2);
  $initialize_input
  $initialize_secret
  struct $stateT s1_ = Snippet(s1);
  struct $stateT s2_ = Snippet(s2);
  __CPROVER_assert(s1_.timer==s2_.timer, "timing leak");
  return 0;
}"""

  override val codegen = new DslGenC with CCodeGenStruct {
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
      emitDatastructures(stream)
      emitFunctionDecls(stream)
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
