package lms.koika.demos

import lms.core.stub._
import lms.core.virtualize
import lms.macros.SourceContext
import lms.macros.RefinedManifest
import lms.collection.mutable._

import lms.koika._
import lms.koika.frontend.NanoRisc._

@virtualize
class NanoRiscNaiveTests extends TutorialFunSuite {
  import KoikaInterp._

  val under = "demos/naive_"

  override def exec(label: String, code: String, suffix: String = "c") =
    super.exec(label, code, suffix)

  override def check(label: String, code: String, suffix: String = "c") =
    super.check(label, code, suffix)

  trait Driver extends GenericKoikaDriver[StateT, StateT] with KoikaInterp.Naive {
    // In the naive driver, we don't use caching or speculation, so we don't
    // need to initialize everything except [regs], [timer] and [mem].
    override val init = s"""
void init(struct $stateT *s) {
  s->regs = calloc(sizeof(int), NUM_REGS);
  for (int i=0; i<NUM_REGS; i++) {
    s->regs[i] = 0;
  }
  s->timer = 0;
  s->mem = calloc(sizeof(int), MEM_SIZE);
  for (int i=0; i<MEM_SIZE; i++) {
    s->mem[i] = 0;
  }
}"""
  }

  test("nanorisc naive shortcircuit") {
    val snippet = new Driver {
      override val prog = NanoRiscDemos.build_shortcircuit_demo(secret_offset, secret_size)

      override val initialize_input = """
for (int i=0; i<SECRET_SIZE; i++) {
  int x = bounded(0, 20);
  s1.mem[i] = x;
  s2.mem[i] = x;
}"""
    }
    check("shortcircuit", snippet.code)
  }

  test("nanorisc naive 2ctr") {
    val snippet = new Driver {
      override val prog = NanoRiscDemos.spec_small
    }
    check("2ctr", snippet.code)
  }

  test("nanorisc naive spectre") {
    val snippet = new Driver {
      override val prog = NanoRiscDemos.build_spectre_demo(secret_offset)
    }
    check("spectre", snippet.code)
  }
}
