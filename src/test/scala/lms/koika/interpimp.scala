package lms.koika

import scala.collection.immutable.Set
import scala.collection.immutable.Map

import lms.core.stub._
import lms.core.virtualize
import lms.collection.mutable._
import lms.macros.SourceContext
import lms.macros.RefinedManifest

@virtualize
class ImpTest extends TutorialFunSuite {
  val under = "imp_"

  import ImpLang._

  override def exec(label: String, code: String, suffix: String = "c") =
    super.exec(label, code, suffix)

  override def check(label: String, code: String, suffix: String = "c") =
    super.check(label, code, suffix)

  trait StateOps extends Dsl {
    trait AbstractRepState {
      def readVar(ident: String): Rep[Int]
      def writeVar(ident: String, v: Rep[Int]): Rep[Unit]

      def readMem(idx: Rep[Int]): Rep[Int]
      def writeMem(idx: Rep[Int], v: Rep[Int]): Rep[Unit]

      def exec(prg: List[Stmt]): Rep[Unit] = {
        for (stmt <- prg) {
          this.execS(stmt)
        }
      }

      def execS(s: Stmt): Rep[Unit] = s match {
        case Assign(id, e) => this.writeVar(id, this.evalE(e))
        case Skip => unit(())
        case IfThen(c, tthen, els) =>
          if (this.evalC(c)) {
            this.exec(tthen)
          }
          else {
            this.exec(els)
          }
        case While(c, body) =>
          while (this.evalC(c)) {
            this.exec(body)
          }
        case PrintT(t) => println(t)
        case PrintExp(e) => println(this.evalE(e))
      }

      def evalE(e: Expr): Rep[Int] = e match {
        case I(n) => n
        case V(id) => this.readVar(id)
        case Mul(e1, e2) => this.evalE(e1) * this.evalE(e2)
        case Add(e1, e2) => this.evalE(e1) + this.evalE(e2)
      }

      def evalC(c: Cond): Rep[Boolean] = c match {
        case T => true
        case F => false
        case Eq(e1, e2) => this.evalE(e1) == this.evalE(e2)
        case Le(e1, e2) => this.evalE(e1) <= this.evalE(e2)
        case Neg(c) => !this.evalC(c)
        case And(c1, c2) => this.evalC(c1) && this.evalC(c2)
      }
    }
  }

  @CStruct
  case class ProgramState(vars: Array[Int], mem: Array[Int])

  trait InterpImpUntimed extends Dsl with StateOps with ArrayOps {
    class State private (
      varLookup: Map[String, Int],
      vars: Rep[Array[Int]],
      mem: Rep[Array[Int]]
    ) extends AbstractRepState {
      def readVar(ident: String): Rep[Int] = vars(varLookup(ident))
      def writeVar(ident: String, v: Rep[Int]): Rep[Unit] = vars(varLookup(ident)) = v

      def readMem(idx: Rep[Int]): Rep[Int] = mem(idx)
      def writeMem(idx: Rep[Int], v: Rep[Int]): Rep[Unit] = mem(idx) = v
    }

    object State {
    }
  }

  test("foo") {}
}
