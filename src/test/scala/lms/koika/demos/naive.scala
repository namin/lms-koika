package lms.koika.demos

import lms.core.stub._
import lms.core.virtualize
import lms.macros.SourceContext
import lms.macros.RefinedManifest
import lms.collection.mutable._

import lms.koika._
import lms.koika.frontend.NanoRisc

@virtualize
class NanoRiscNaiveTest extends TutorialFunSuite {
  val under = "demos/naive_"

  override def exec(label: String, code: String, suffix: String = "c") =
    super.exec(label, code, suffix)

  override def check(label: String, code: String, suffix: String = "c") =
    super.check(label, code, suffix)

  abstract class DslDriver[A:Manifest, B:Manifest] extends DslDriverC[A,B] { q =>
    val main: String = """
    """
  }
}
