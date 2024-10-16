package lms.koika.demos

import lms.core.stub._
import lms.core.virtualize
import lms.macros.SourceContext
import lms.macros.RefinedManifest
import lms.collection.mutable._

import lms.koika._
import lms.koika.frontend.NanoRisc._

@virtualize
class NanoRiscSpeculativeTests extends TutorialFunSuite {
  import KoikaInterp._

  val under = "demos/speculative_"

  override def exec(label: String, code: String, suffix: String = "c") =
    super.exec(label, code, suffix)

  override def check(label: String, code: String, suffix: String = "c") =
    super.check(label, code, suffix)

  trait Driver extends GenericKoikaDriver[StateT, StateT] with KoikaInterp.Speculative {
    override val init = s"""
#define CACHE_LRU_SIZE 2
void init(struct $stateT *s) {
  s->regs = calloc(sizeof(int), NUM_REGS);
  s->saved_regs = calloc(sizeof(int), NUM_REGS);
  for (int i=0; i<NUM_REGS; i++) {
    s->regs[i] = 0;
    s->saved_regs[i] = 0;
  }
  s->timer = 0;
  s->mem = calloc(sizeof(int), MEM_SIZE);
  for (int i=0; i<MEM_SIZE; i++) {
    s->mem[i] = 0;
  }
  s->cache_keys = calloc(sizeof(int), CACHE_LRU_SIZE);
  s->cache_vals = calloc(sizeof(int), CACHE_LRU_SIZE);
  for (int i=0; i<CACHE_LRU_SIZE; i++) {
    s->cache_keys[i] = -1;
    s->cache_vals[i] = -1;
  }
}"""
  }

  test("nanorisc speculative shortcircuit") {
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

  test("nanorisc speculative 2ctr") {
    val snippet = new Driver {
      override val prog = NanoRiscDemos.spec_small
    }
    check("2ctr", snippet.code)
  }

  test("nanorisc speculative spectre") {
    val snippet = new Driver {
      override val prog = NanoRiscDemos.build_spectre_demo(secret_offset)
    }
    check("spectre", snippet.code)
  }
}
