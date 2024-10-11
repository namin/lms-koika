package lms.koika.demos

import lms.koika.frontend.NanoRisc._

object NanoRiscDemos {
  val r0: Reg = Reg(0)
  val r1: Reg = Reg(1)
  val r2: Reg = Reg(2)
  val r3: Reg = Reg(3)
  val r4: Reg = Reg(4)
  val r5: Reg = Reg(5)
  val r6: Reg = Reg(6)
  val r7: Reg = Reg(7)

  // Basic short-circuiting password loop.
  def build_shortcircuit_demo(secret_offset: Int, password_size: Int): Vector[Instr] =
    Vector(
      Mov(r2, Imm(0)),
      Mov(r3, Imm(secret_offset)),
      Mov(r4, Imm(0)),

      // loop:
      B(Some((Ge, r4, Imm(10))), Addr(-1)),
      Load(r0, r2, r4),
      Load(r1, r3, r4),
      B(Some((Ne, r0, r1)), Addr(-1)),
      Binop(Plus, r4, r4, Imm(1)),
      B(None, Addr(3)),

      // wrong:
      Mov(r0, Imm(0)),
      B(None, Addr(12)),

      // right:
      Mov(r1, Imm(1)),

      // done:
    )
}
