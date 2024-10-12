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
    /*
     * mov r2, #0
     * mov r3, #20
     * mov r4, #0
     * 
     * loop:
     * bge r4, #10, right
     * ldr r0, [r2, r4]
     * ldr r1, [r3, r4]
     * bne r0, r1, wrong
     * add r4, r4, #1
     * b loop
     * 
     * wrong:
     * mov r0, #0
     * b done
     * 
     * right:
     * mov r0, #1
     * 
     * done:
     */
    Vector(
      Mov(r2,Imm(0)),
      Mov(r3,Imm(secret_offset)),
      Mov(r4,Imm(0)),
      B(Some((Ge,r4,Imm(password_size))),Addr(11)),
      Load(r0,r2,r4),
      Load(r1,r3,r4),
      // CR cam: I am losing my mind. If we change this `Ne` to anything other
      // than `Eq`, then everything works properly. With either `Ne` or `Eq`,
      // however, it thinks the branch is always taken. WTF?
      B(Some((Ne,r0,r1)),Addr(9)),
      Binop(Plus,r4,r4,Imm(1)),
      B(None,Addr(3)),
      Mov(r0,Imm(0)),
      B(None,Addr(12)),
      Mov(r0,Imm(1)),
    )
}
