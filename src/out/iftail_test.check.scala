class Snippet extends (Int => Int) {
  def apply(x1: Int): Int = {
    val x2 = x1 == 0
    val x13 = if (x2) {
      val x4 = println("a")
      val x5 = x1 + 1
      val x6 = println(x5)
      x1 /*exit: x1 */
    } else {
      val x9 = println("b")
      val x10 = x1 + 2
      val x11 = println(x10)
      x1 /*exit: x1 */
    }
    x13
  }
}
