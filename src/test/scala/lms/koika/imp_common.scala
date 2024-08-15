package lms.koika

// TODO (cam): think about a final tagless style encoding
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
