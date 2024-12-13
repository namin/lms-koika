# LMS-Koika nanoRISC processors

This folder contains a curated sample of staged, timed interpreters and input
programs. The corresponding demos can be found in [`out/demos`](/src/out/demos).

- `common.scala`: Contains the majority of business logic, including all staged
  interpreters and the `StateT` type.
- `naive.scala`, `cached.scala` and `speculative.scala` contain specific test drivers.
- `programs.scala` contains sample programs.

The provided sample programs and whether they are expected to pass CBMC are
detailed in `programs.scala`.

In particular, this work is presented in [PEPM '25](https://popl25.sigplan.org/details/pepm-2025-papers/4/Collapsing-Towers-for-Side-Channel-Security-Short-Paper-)

## Relation to the paper

- The common nanoRISC definitions (Figure 2) can be found in [`main/.../nanorisc.scala`](/src/main/scala/lms/koika/frontend/nanorisc.scala).
- Fig. 3 (The nanoRISC interpreter, staged) corresponds to [`execute`](common.scala#L98) in `common.scala`.
- Fig. 4a (A sample nanoRISC program exhibiting a SPECTRE vulnerability) corresponds to [`build_spectre_demo`](programs.scala#L87) in `programs.scala`.
- Fig. 4b (Residue of Fig. 4 via Fig. 3) is [`out/demos/naive_spectre.check.c`](/src/out/demos/naive_spectre.check.c).
- Fig. 5 (Enforcing noninterference in the residue) varies a bit between demos, but mostly corresponds to [`main`](common.scala#L311) in `common.scala`.
- Fig. 6 (Adjusting the interpreter to model the cache) is the [`Cached`](common.scala#L133) trait.
- Fig. 7 (Adjusting the interpreter for speculation) is the [`Speculative`](common.scala#L195) trait.
- Fig. 8 (Residue of Fig.4 with caching and speculation) is [`out/demos/speculative_spectre.check.c`](/src/out/demos/speculative_spectre.check.c).
