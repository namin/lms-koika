package lms
package core

import core._
import core.stub._
import macros.SourceContext
import macros.RefinedManifest

import lms.collection.mutable._

class StructTest extends TutorialFunSuite {
  val under = "backend/"

  @CStruct case class Complex(real: Double, image: Double)

  test("basic_struct_is_OK") {
    val driver = new DslDriverC[Complex, Complex] with ComplexOps { q =>
      override val codegen = new DslGenC with CCodeGenStruct {
        val IR: q.type = q
      }

      @virtualize
      def snippet(arg: Rep[Complex]) = {
        arg.real = 1.23 // that is s.writeField("real", 1.23)
        arg.image = arg.real
        arg
      }
    }
    // TODO: this output doesn't compile; we need to adjust [convert] to check
    // for manifest[Complex].
    check("basic_struct", driver.code, "c")
  }
}
