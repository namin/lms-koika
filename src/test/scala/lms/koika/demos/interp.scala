package lms.koika.demos

import lms.core.stub._
import lms.core.virtualize
import lms.macros.SourceContext
import lms.macros.RefinedManifest
import lms.collection.mutable._

import lms.koika.frontend.NanoRisc
import lms.koika.frontend.NanoRisc._

@virtualize
object Interp {
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
          // CR-soon cwong: It refuses to compile if we try to just use [Math],
          // even if we import it and I have no idea why.
          case Binop(op, rd, rs1, rs2) => {
            set_reg(s, rd.unReg, eval_op(op, operand(s, rs1), operand(s, rs2)))
            call(i+1, s)
          }
          case Load(rd, rs, im) => {
            set_reg(s, rd.unReg, get_mem(s, operand(s, rs) + operand(s, im)))
            call(i+1, s)
          }
          case Store(rd, rs, im) => {
            set_mem(s, operand(s, rs) + operand(s, im), operand(s, rd))
            call(i+1, s)
          }
          case B(mcmp, tgt) => mcmp match {
            case None => call(tgt.unAddr, s)
            case Some((cmp, rs1, rs2)) =>
              if (eval_cmp(cmp, operand(s, rs1), operand(s, rs2))) {
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
