package lms.koika.demos

import lms.core.stub._
import lms.core.virtualize
import lms.macros.SourceContext
import lms.macros.RefinedManifest
import lms.collection.mutable._

import lms.koika.frontend.NanoRisc
import lms.koika.frontend.NanoRisc._

@virtualize
object KoikaInterp {
  // CR cwong: We currently don't have a good way to have a minimal [StateT]
  // that gets extended by later consumers.
  @CStruct
  case class StateT
    ( regs: Array[Int]
    , mem: Array[Int]
    , saved_regs: Array[Int]
    , cache_keys: Array[Int]
    , cache_vals: Array[Int]
    , timer: Int
    )

  trait Common extends Dsl with NanoRisc.Ops with StateTOps {
    val prog: Vector[NanoRisc.Instr]
    def useCache: Boolean

    lazy val cache: Array[Option[Rep[StateT => StateT]]] =
      (for (p <- prog) yield None).toArray

    def get_reg(s: Rep[StateT], i: Rep[Int]): Rep[Int]
    def set_reg(s: Rep[StateT], i: Rep[Int], v: Rep[Int]): Rep[Unit]
    def get_mem(s: Rep[StateT], i: Rep[Int]): Rep[Int]
    def set_mem(s: Rep[StateT], i: Rep[Int], v: Rep[Int]): Rep[Unit]

    def tick(s: Rep[StateT]): Rep[Unit] = s.timer += 1

    def operand(s: Rep[StateT], vl: Operand): Rep[Int] =
      vl match {
        case Imm(i) => i
        case Reg(i) => get_reg(s, i)
      }

    // The indirection via `execute` is necessary to generate functions for
    // each instruction.
    def execute(i: Int, s: Rep[StateT]): Rep[StateT]
    def call(i: Int, s: Rep[StateT]): Rep[StateT] =
      if (useCache) {
        if (i < cache.length) {
          val f = cache(i) match {
            case None => {
              val f = topFun { (s: Rep[StateT]) => execute(i, s) }
              cache(i) = Some(f)
              f
            }
            case Some(f) => f
          }
          f(s)
        }
        else {
          s
        }
      }
      else {
        execute(i, s)
      }

    def snippet(s: Rep[StateT]): Rep[StateT] = call(0, s)
  }

  trait Naive extends Common {
    override def useCache = true

    override def get_reg(s: Rep[StateT], i: Rep[Int]): Rep[Int] =
      s.regs(i)
    override def set_reg(s: Rep[StateT], i: Rep[Int], v: Rep[Int]): Rep[Unit] =
      s.regs(i) = v

    override def get_mem(s: Rep[StateT], i: Rep[Int]): Rep[Int] =
      s.mem(i)
    override def set_mem(s: Rep[StateT], i: Rep[Int], v: Rep[Int]): Rep[Unit] =
      s.mem(i) = v

    // CR-someday cwong: This needs to be defined here, for some reason -- if
    // we leave this function defined in `NanoRisc.Ops`, LMS seems to always
    // believe that the `Eq` and `Ne` cases are always true (and wrongly DCEs
    // accordingly).
    override def eval_cmp(cmp: Cmp, op1: Rep[Int], op2: Rep[Int]): Rep[Boolean] =
      cmp match {
        case Eq => op1 == op2
        case Ne => op1 != op2
        case Lt => op1 < op2
        case Ge => op1 >= op2
      }

    def execute(i: Int, s: Rep[StateT]): Rep[StateT] =
      if (i < prog.length) {
        tick(s)
        prog(i) match {
          case Mov(dst, src) => {
            set_reg(s, dst.unReg, operand(s, src))
            call(i+1, s)
          }
          case Binop(op, dst, src1, src2) => {
            set_reg(s, dst.unReg, eval_op(op, operand(s, src1), operand(s, src2)))
            call(i+1, s)
          }
          case Load(dst, src, im) => {
            set_reg(s, dst.unReg, get_mem(s, operand(s, src) + operand(s, im)))
            call(i+1, s)
          }
          case Store(dst, src, im) => {
            set_mem(s, operand(s, src) + operand(s, im), operand(s, dst))
            call(i+1, s)
          }
          case B(None, tgt) => call(tgt.unAddr, s)
          case B(Some((cmp, src1, src2)), tgt) =>
            if (eval_cmp(cmp, operand(s, src1), operand(s, src2))) {
              call(tgt.unAddr, s)
            }
            else {
              call(i+1, s)
            }
        }
      }
      else {
        s
      }
  }

  trait Cached extends Naive {
    def pushLRU(s: Rep[StateT], addr: Rep[Int], v: Rep[Int]): Rep[Unit] = {
      s.cache_keys(1) = s.cache_keys(0)
      s.cache_vals(1) = s.cache_vals(0)

      s.cache_keys(0) = addr
      s.cache_vals(0) = v
    }

    def runCache(s: Rep[StateT], addr: Rep[Int], v: Option[Rep[Int]]): Rep[Int] = {
      if (s.cache_keys(0) == addr) {
        // address is in cache, return value
        v match {
          case Some(x) => {
            s.cache_vals(0) = x
            x
          }
          case None => s.cache_vals(0)
        }
      }
      else if (s.cache_keys(1) == addr) {
        // key is at tail of LRU queue, so set addr as head
        val result = v match {
          case Some(x) => x
          case None => s.cache_vals(1)
        }

        pushLRU(s, addr, result)

        s.timer += 1
        result
      }
      else {
        // address not in cache
        val result = v match {
          case Some(x) => x
          case None => s.mem(addr)
        }

        // evict LRU and write back to memory
        // CR-soon cwong: Triple-check that this is correct -- I think we might
        // accidentally write back to memory too soon if a speculative
        // instruction evicts an entry.
        s.mem(s.cache_keys(1)) = s.cache_vals(1)

        pushLRU(s, addr, result)

        s.timer += 100

        result
      }
    }

    override def get_mem(s: Rep[StateT], addr: Rep[Int]): Rep[Int] =
      runCache(s, addr, None)

    override def set_mem(s: Rep[StateT], addr: Rep[Int], v: Rep[Int]): Rep[Unit] = {
      runCache(s, addr, Some(v))
      unit(())
    }
  }

  trait Speculative extends Cached {
    val savedRegisters = scala.collection.mutable.Set[Reg]()

    def saveForRollback(s: Rep[StateT], instr: Instr): Rep[Unit] = {
      instr match {
        case Load(rd, _, _) => {
          if (!savedRegisters.contains(rd)) {
            s.saved_regs(rd.unReg) = get_reg(s, rd.unReg)
            savedRegisters += rd
          }
        }
        case _ => ()
      }
      unit(())
    }
    def rollback(s: Rep[StateT]): Rep[Unit] = {
      s.timer += 15
      for (rd <- savedRegisters) {
        set_reg(s, rd.unReg, s.saved_regs(rd.unReg))
      }
      unit(())
    }
    def resetSaved(): Unit = { savedRegisters.clear() }

    var inBranch: Option[B] = None

    override def useCache: Boolean = inBranch == None
    override def execute(i: Int, s: Rep[StateT]): Rep[StateT] = inBranch match {
      case None =>
        (i < prog.length, prog(i)) match {
          case (true, B(Some(cnd), tgt)) if tgt.unAddr > i => {
            inBranch = Some(B(Some(cnd), tgt))
            call(i+1, s)
          }
          case _ => super.execute(i, s)
        }
      case Some(B(Some((cmp, src1, src2)), tgt)) => {
        if (i == tgt.unAddr) {
          inBranch = None
          if (eval_cmp(cmp, operand(s, src1), operand(s, src2))) {
            rollback(s)
            call(tgt.unAddr, s)
          }
          resetSaved()
          s
        }
        else if (i < prog.length) {
          prog(i) match {
            case Load(rd, rs, imm) if rd != src1 && rd != src2 => {
              saveForRollback(s, Load(rd, rs, imm))
              super.execute(i, s)
            }
            case _ => {
              var result: Rep[StateT] = s
              inBranch = None
              if (eval_cmp(cmp, operand(s, src1), operand(s, src2))) {
                rollback(s)
                result = call(tgt.unAddr, s)
              }
              else {
                result = super.execute(i, s)
              }
              resetSaved()
              result
            }
          }
        }
        else {
          s
        }
      }
      case _ => {
        super.execute(i, s)
      }
    }
  }
}

abstract class GenericKoikaDriver[A:Manifest, B:Manifest] extends DslDriverC[A,B] { q =>
  val num_regs: Int = 8
  val mem_size: Int = 30
  val secret_size: Int = 10
  val secret_offset: Int = 20

  val header: String = s"""
#define NUM_REGS $num_regs
#define MEM_SIZE $mem_size
#define SECRET_SIZE $secret_size
#define SECRET_OFFSET $secret_offset
#ifndef CBMC
#define __CPROVER_assert(b,s) 0
#define nondet_uint() 0
#else
int nondet_uint();
#endif
int bounded(int low, int high) {
  int x = nondet_uint();
  __CPROVER_assume(low <= x && x <= high);
  return x;
}"""

  val stateT: String = "StateT"
  val init: String

  val initialize_input: String = """
int x = bounded(0, 20);
s1.regs[0] = x;
s2.regs[0] = x;"""

  val initialize_secret: String = """
// initialize secret
for (int i=0; i<SECRET_SIZE; i++) {
  s1.mem[SECRET_OFFSET+i] = bounded(0, 20);
  s2.mem[SECRET_OFFSET+i] = bounded(0, 20);
}"""

  def main: String = s"""
$header
$init
int main(int argc, char* argv[]) {
  struct $stateT s1, s2;
  init(&s1);
  init(&s2);
  $initialize_input
  $initialize_secret
  struct $stateT s1_ = Snippet(s1);
  struct $stateT s2_ = Snippet(s2);
  __CPROVER_assert(s1_.timer==s2_.timer, "timing leak");
  return 0;
}"""

  override val codegen = new DslGenC with CCodeGenStruct {
    val IR: q.type = q

    override def emitAll(g: lms.core.Graph, name: String)(m1:Manifest[_],m2:Manifest[_]): Unit = {
      val ng = init(g)
      val efs = "" //quoteEff(g.block.ein)
      val stt = dce.statics.toList.map(quoteStatic).mkString(", ")
      prepareHeaders
      emitln("""
  |/*****************************************
  |Emitting C Generated Code
  |*******************************************/
  """.stripMargin)
      val src = run(name, ng)
      emitDefines(stream)
      emitHeaders(stream)
      emitDatastructures(stream)
      emitFunctionDecls(stream)
      emitFunctions(stream)
      emitInit(stream)
      emitln(s"\n/**************** $name ****************/")
      emit(src)
      emitln("""
  |/*****************************************
  |End of C Generated Code
  |*******************************************/
|""".stripMargin)
      emit(main)
    }
  }
}
