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
  case class Deref(e: Expr) extends Expr
  case class Mul(e1: Expr, e2: Expr) extends Expr
  case class Add(e1: Expr, e2: Expr) extends Expr

  case object T extends Cond
  case object F extends Cond
  case class Eq(e1: Expr, e2: Expr) extends Cond
  case class Le(e1: Expr, e2: Expr) extends Cond
  case class Not(c: Cond) extends Cond
  case class And(c1: Cond, c2: Cond) extends Cond

  def vars(prg: List[Stmt]): Set[String] = {
    prg.foldLeft[Set[String]](Set())((acc, st) => acc union varsS(st))
  }

  def varsS(s: Stmt): Set[String] = s match {
    case Assign(id, e) => Set(id) union varsE(e)
    case Skip => Set()
    case IfThen(c, tthen, els) => varsC(c) union vars(tthen) union vars(els)
    case While(c, body) => varsC(c) union vars(body)
    case PrintT(t) => Set()
    case PrintExp(e) => varsE(e)
  }

  def varsE(e: Expr): Set[String] = e match {
    case I(n) => Set()
    case V(id) => Set(id)
    case Deref(e) => varsE(e)
    case Mul(e1, e2) => varsE(e1) union varsE(e2)
    case Add(e1, e2) => varsE(e1) union varsE(e2)
  }

  def varsC(c: Cond): Set[String] = c match {
    case T => Set()
    case F => Set()
    case Eq(e1, e2) => varsE(e1) union varsE(e2)
    case Le(e1, e2) => varsE(e1) union varsE(e2)
    case Not(c) => varsC(c)
    case And(c1, c2) => varsC(c1) union varsC(c2)
  }
}
