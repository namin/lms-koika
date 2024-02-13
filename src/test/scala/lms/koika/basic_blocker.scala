package lms.koika

import scala.collection.immutable.Map

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
  case class Identifier(s: String)

  abstract sealed class Line
  case class Label(name: Identifier) extends Line

  abstract sealed class Instruction extends Line
  // Not listed under one of the more specific instructions because we want to
  // transform this into a more expressive terminator form
  case class BranchZ(rs: Int, target: Identifier) extends Instruction

  abstract sealed class Basic extends Instruction
  case class Add(rd: Int, rs1: Int, rs2: Int) extends Basic
  case class Load(rd: Int, im: Int, rs: Int) extends Basic
  case class Store(rd: Int, im: Int, rs: Int) extends Basic

  abstract sealed class Terminator
  case class Ifz(rs: Int, then: Identifier, els: Identifier) extends Terminator
  case class Goto(to: Identifier) extends Terminator
  case class Done() extends Terminator

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
  def buildCfgNoHazard(p: Program): CFG = {
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
      // XXX - This needs to be duplicated because the typechecker can't
      // determine that all non `BranchZ` instructions must be of type `Basic`.
      case instr @ Add(_, _, _) => {
        currentBlock = currentBlock :+ instr
      }
      case instr @ Load(_, _, _) => {
        currentBlock = currentBlock :+ instr
      }
      case instr @ Store(_, _, _) => {
        currentBlock = currentBlock :+ instr
      }
    }
    blocks = blocks + (currentLabel -> Block(currentBlock, Done()))

    CFG(blocks, Identifier("main"))
  }

  trait InterpFusedBasicBlockNoHazards extends Dsl with StateTOps {
  }
}
