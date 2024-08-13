package lms.koika

import scala.collection.immutable.Set
import scala.collection.immutable.Map

import lms.core.stub._
import lms.core.virtualize
import lms.macros.SourceContext
import lms.macros.RefinedManifest

// TODO: While might not be expressive enough to be interesting here.
object ImpLang {
  abstract sealed class Expr
  abstract sealed class Stmt
  abstract sealed class Cond

  case class Assign(id: String, target: Expr) extends Stmt
  case object Skip extends Stmt
  case class IfThen(guard: Cond, tthen: List[Stmt], els: List[Stmt]) extends Stmt
  case class While(guard: Cond, body: List[Stmt]) extends Stmt
  case class PrintT(text: String) extends Stmt
  case class PrintExp(e: Expr) extends Stmt

  case class I(n: Int) extends Expr
  case class V(id: String) extends Expr
  case class Mul(e1: Expr, e2: Expr) extends Expr
  case class Add(e1: Expr, e2: Expr) extends Expr

  case object T extends Cond
  case object F extends Cond
  case class Eq(e1: Expr, e2: Expr) extends Cond
  case class Le(e1: Expr, e2: Expr) extends Cond
  case class Neg(c: Cond) extends Cond
  case class And(c1: Cond, c2: Cond) extends Cond

  def allVars(prg: List[Stmt]): Set[String] = {
    prg.foldLeft[Set[String]](Set())((acc, st) => acc union allVarsS(st))
  }

  def allVarsS(s: Stmt): Set[String] = s match {
    case Assign(id, e) => Set(id) union allVarsE(e)
    case Skip => Set()
    case IfThen(c, tthen, els) => allVarsC(c) union allVars(tthen) union allVars(els)
    case While(c, body) => allVarsC(c) union allVars(body)
    case PrintT(t) => Set()
    case PrintExp(e) => allVarsE(e)
  }

  def allVarsE(e: Expr): Set[String] = e match {
    case I(n) => Set()
    case V(id) => Set(id)
    case Mul(e1, e2) => allVarsE(e1) union allVarsE(e2)
    case Add(e1, e2) => allVarsE(e1) union allVarsE(e2)
  }

  def allVarsC(c: Cond): Set[String] = c match {
    case T => Set()
    case F => Set()
    case Eq(e1, e2) => allVarsE(e1) union allVarsE(e2)
    case Le(e1, e2) => allVarsE(e1) union allVarsE(e2)
    case Neg(c) => allVarsC(c)
    case And(c1, c2) => allVarsC(c1) union allVarsC(c2)
  }
}

@virtualize
class ImpTest extends TutorialFunSuite {
  val under = "interpimp_"

  import ImpLang._

  override def exec(label: String, code: String, suffix: String = "c") =
    super.exec(label, code, suffix)

  override def check(label: String, code: String, suffix: String = "c") =
    super.check(label, code, suffix)

  trait InterpWhile extends Dsl {
    class Ctx private (val lookup: Map[String, Var[Int]]) {
      def apply(v: String): Var[Int] = lookup(v)

      def update(v: String, e: Rep[Int]) = {
        var vv = lookup(v)
        vv = e
      }
    }

    object Ctx {
      def initialize(vars: Set[String]): Ctx = {
        var result: Map[String, Var[Int]] = Map()

        // TODO: how to take input?
        for (v <- vars) {
          result = result + (v -> __newVar(0))
        }

        new Ctx(result)
      }
    }

    def exec(ctx: Ctx, prg: List[Stmt]): Rep[Unit] = {
      for (stmt <- prg) {
        execS(ctx, stmt)
      }
    }

    // TODO: Make a timing counter and tick on every call to each of these
    // functions
    def execS(ctx: Ctx, s: Stmt): Rep[Unit] = s match {
      case Assign(id, e) => ctx(id) = evalE(ctx, e)
      case Skip => unit(())
      case IfThen(c, tthen, els) =>
        if (evalC(ctx, c)) {
          exec(ctx, tthen)
        }
        else {
          exec(ctx, els)
        }
      case While(c, body) =>
        while (evalC(ctx, c)) {
          exec(ctx, body)
        }
      case PrintT(t) => println(t)
      case PrintExp(e) => println(evalE(ctx, e))
    }

    def evalE(ctx: Ctx, e: Expr): Rep[Int] = e match {
      case I(n) => n
      case V(id) => ctx(id)
      case Mul(e1, e2) => evalE(ctx, e1) * evalE(ctx, e2)
      case Add(e1, e2) => evalE(ctx, e1) + evalE(ctx, e2)
    }

    def evalC(ctx: Ctx, c: Cond): Rep[Boolean] = c match {
      case T => true
      case F => false
      case Eq(e1, e2) => evalE(ctx, e1) == evalE(ctx, e2)
      case Le(e1, e2) => evalE(ctx, e1) <= evalE(ctx, e2)
      case Neg(c) => !evalC(ctx, c)
      case And(c1, c2) => evalC(ctx, c1) && evalC(ctx, c2)
    }
  }

  test("foo") {}
}
