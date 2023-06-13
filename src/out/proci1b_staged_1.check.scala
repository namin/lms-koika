/*****************************************
Emitting Generated Code
*******************************************/
class Snippet() extends (Array[Int] => Int) {
  def apply(x0: Array[Int]): Int = {
    while (true) {
      x0(3) = x0(2) + x0(1)
      x0(1) = x0(2) + x0(0)
      x0(2) = x0(3) + x0(0)
      x0(4) = x0(4) + x0(5)
    }
    x0(2)
  }
}
/*****************************************
End of Generated Code
*******************************************/
