package lms.koika.frontend

import lms.core.stub._
import lms.macros.SourceContext

object NanoRisc {
  abstract sealed class Operand

  // CR cwong: It's not clear to me how much these newtypes actually help; we
  // just end up peppering the code with `unReg` everywhere.
  case class Imm(i: Int) extends Operand {
    def unImm = i
  }
  case class Reg(i: Int) extends Operand {
    def unReg = i
  }

  case class Addr(i: Int) {
    def unAddr = i
  }

  abstract sealed class Cmp
  case object Eq extends Cmp
  case object Ne extends Cmp
  case object Lt extends Cmp
  case object Ge extends Cmp

  abstract sealed class Op
  case object Plus extends Op
  case object Sub extends Op
  case object Mul extends Op

  abstract sealed class Instr
  case class Mov(dst: Reg, src: Operand) extends Instr
  case class Binop(op: Op, dst: Reg, src1: Reg, src2: Operand) extends Instr
  case class Load(dst: Reg, src: Reg, offs: Operand) extends Instr
  case class Store(dst: Reg, src: Reg, offs: Operand) extends Instr
  case class B(cmp: Option[(Cmp, Reg, Operand)], tgt: Addr) extends Instr

  // CR-someday cwong: It'd be nice to be able to just say [op.eval] instead of
  // [eval_op]. Look into using implicits for this.
  trait Ops extends Dsl {
    def eval_cmp(cmp: Cmp, op1: Rep[Int], op2: Rep[Int]): Rep[Boolean] =
      cmp match {
        case Eq => op1 == op2
        case Ne => op1 != op2
        case Lt => op1 < op2
        case Ge => op1 >= op2
      }

    def eval_op(op: Op, op1: Rep[Int], op2: Rep[Int]): Rep[Int] =
      op match {
        case Plus => op1 + op2
        case Sub => op1 - op2
        case Mul => op1 * op2
      }
  }
}
