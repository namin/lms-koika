package lms.koika.frontend

object NanoRisc {
  abstract sealed class Operand
  case class Imm(i: Int) extends Operand
  case class Reg(i: Int) extends Operand

  case class Addr(i: Int)

  // TODO: We can't actually define the semantics of each of these here, because
  // we'd need to bring the [Rep] class into scope.
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

  case class Math(op: Op, rd: Reg, rs1: Reg, rs2: Operand) extends Instr
  case class Load(rd: Reg, rs: Reg, im: Imm) extends Instr
  case class Store(rd: Reg, rs: Reg, im: Imm) extends Instr
  case class B(cmp: Option[Cmp], rs1: Reg, rs2: Reg, tgt: Addr) extends Instr
}
