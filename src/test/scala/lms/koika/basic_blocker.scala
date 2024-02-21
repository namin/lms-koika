package lms.koika

import scala.collection.immutable.Map
import scala.collection.mutable.{Map => MutableMap}

import lms.core.stub._
import lms.core.virtualize
import lms.macros.SourceContext
import lms.macros.RefinedManifest

import lms.collection.mutable._

@virtualize
class BasicBlockTest extends TutorialFunSuite {
  val under = "basic_blocker"

  override def exec(label: String, code: String, suffix: String = "c") =
    super.exec(label, code, suffix)

  override def check(label: String, code: String, suffix: String = "c") =
    super.check(label, code, suffix)

  // Newtype
  case class Identifier(s: String) {
    override def equals(other: Any): Boolean = other match {
      case Identifier(s2) => s eq s2
      case _ => false
    }

    override def hashCode() = s.hashCode()
  }

  abstract sealed class Line
  case class Label(name: Identifier) extends Line

  abstract sealed class Instruction extends Line
  // Not listed under one of the more specific instructions because we want to
  // transform this into a more expressive terminator form
  case class BranchZ(rs: Int, target: Identifier) extends Instruction
  case class Branch(target: Identifier) extends Instruction

  abstract sealed class Basic extends Instruction
  case class Add(dst: Int, s1: Int, s2: Int) extends Basic
  case class Mul(dst: Int, s1: Int, s2: Int) extends Basic
  case class Load(dst: Int, base: Int, offs: Int) extends Basic
  case class Store(src: Int, base: Int, offs: Int) extends Basic

  abstract sealed class MovKind
  case object Imm extends MovKind
  case object Reg extends MovKind

  case class Mov(dst: Int, src: Int, kind: MovKind) extends Basic

  abstract sealed class Terminator
  case class Ifz(rs: Int, then: Identifier, els: Identifier) extends Terminator
  case class Goto(to: Identifier) extends Terminator
  case object Done extends Terminator

  case class Block(body: Vector[Basic], term: Terminator)

  case class Program(body: Vector[Line])
  case class CFG(blocks: Map[Identifier, Block], entry: Identifier)

  @CStruct
  case class StateT
    ( regs: Array[Int]
    , mem: Array[Int]
    , timer: Int
    )

  var counter = 0
  def fresh(): Identifier = {
    // in a real program, this is obviously not sufficient
    val result = ".label" + counter
    counter = counter + 1
    Identifier(result)
  }

  // XXX - I bet there is a way to do this _inside_ the trait that simply
  // creates the topFun on-demand, instead of building this intermediate
  // data structure first.
  def buildCFGNoHazard(p: Program): CFG = {
    var blocks: Map[Identifier, Block] = Map()

    var currentBlock: Vector[Basic] = Vector()
    var currentLabel = Identifier("main")

    for (line <- p.body) line match {
      case Label(name) => {
        blocks = blocks + (currentLabel -> Block(currentBlock, Goto(name)))
        currentLabel = name
        currentBlock = Vector()
      }
      // For now, we naively assume that the program is well-formed and that
      // all target labels exist.
      case BranchZ(rs, target) => {
        val nextLabel = fresh()
        blocks = blocks + (currentLabel -> Block(currentBlock, Ifz(rs, target, nextLabel)))
        currentLabel = nextLabel
        currentBlock = Vector()
      }
      case Branch(target) => {
        val nextLabel = fresh()
        blocks = blocks + (currentLabel -> Block(currentBlock, Goto(target)))
        currentLabel = nextLabel
        currentBlock = Vector()
      }
      // XXX - This needs to be duplicated because the typechecker can't
      // determine that all non `BranchZ` instructions must be of type `Basic`.
      case instr @ Add(_, _, _) => {
        currentBlock = currentBlock :+ instr
      }
      case instr @ Mul(_, _, _) => {
        currentBlock = currentBlock :+ instr
      }
      case instr @ Load(_, _, _) => {
        currentBlock = currentBlock :+ instr
      }
      case instr @ Store(_, _, _) => {
        currentBlock = currentBlock :+ instr
      }
      case instr @ Mov(_, _, _) => {
        currentBlock = currentBlock :+ instr
      }
    }
    blocks = blocks + (currentLabel -> Block(currentBlock, Done))

    CFG(blocks, Identifier("main"))
  }

  trait InterpDsl extends Dsl with StateTOps {
    def step(state: Rep[StateT], instr: Basic): Rep[Unit] = {
      state.timer = state.timer + 1
      instr match {
        case Add(dst, s1, s2) => state.regs(dst) = state.regs(s1) + state.regs(s2)
        case Mul(dst, s1, s2) => state.regs(dst) = state.regs(s1) * state.regs(s2)
        case Load(dst, base, offs) => state.regs(dst) = state.mem(state.regs(base) + offs)
        case Store(src, base, offs) => state.mem(state.regs(base) + offs) = src
        case Mov(dst, src, Reg) => state.regs(dst) = state.regs(src)
        case Mov(dst, src, Imm) => state.regs(dst) = src
      }
    }
  }

  trait InterpUnfusedBasicBlockNoHazards extends InterpDsl with Serializable {
    val blocks: MutableMap[Identifier, Rep[StateT => StateT]] = MutableMap()

    def runBlock(cfg: CFG, block: Block, state: Rep[StateT]): Rep[StateT] = {
      for (instr <- block.body) {
        step(state, instr)
      }

      block.term match {
        case Done => state
        case Goto(lbl) => runLabel(cfg, lbl, state)
        case Ifz(rs, then, els) =>
          if (state.regs(rs) == 0) {
            runLabel(cfg, then, state)
          }
          else {
            runLabel(cfg, els, state)
          }
      }
    }

    def runLabel(cfg: CFG, lbl: Identifier, state: Rep[StateT]): Rep[StateT] = {
      def ensure_serializable[A <: Serializable](x: A) = {}
      cfg.blocks.get(lbl) match {
        case Some(block) => {
          val f = blocks.get(lbl) match {
            case None => {
              ensure_serializable(cfg)
              ensure_serializable(block)
              System.out.println(lbl);
              val result = topFun { (st: Rep[StateT]) => block; st }
              blocks(lbl) = result
              result
            }
            case Some(f) => f
          }
          f(state)
        }

        case None => state
      }
    }

    def run(program: Program, state: Rep[StateT]): Rep[StateT] = {
      val cfg = buildCFGNoHazard(program)
      runLabel(cfg, Identifier("main"), state)
    }
  }

  abstract class DslDriverX[A:Manifest,B:Manifest] extends DslDriverC[A,B] { q =>
    val main: String = """
int main(int argc, char *argv[]) {
  if (argc != 2) {
    printf("usage: %s <arg>\n", argv[0]);
    return 0;
  }
  return 0;
}
"""

    override val codegen = new DslGenC {
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
        //emitFunctionDecls(stream)
        emitDatastructures(stream)
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

  def label(s: String): Label = Label(Identifier(s))
  val i = Identifier

  test("basic block output functions only") {
    val snippet = new DslDriverX[StateT,StateT] with InterpUnfusedBasicBlockNoHazards {
      val program = Program(Vector
        ( Mov(1, 1, Imm)
        , label("loop")
        , BranchZ(0, i("exit"))
        , Mul(1, 1, 0)
        , Mov(2, -1, Imm)
        , Add(0, 0, 2)
        , Branch(i("loop"))
        , label("exit")
        , Mov(0, 1, Reg)
        ))
      def snippet(s: Rep[StateT]): Rep[StateT] = run(program, s)
    }
    check("1", snippet.code)
  }
}
