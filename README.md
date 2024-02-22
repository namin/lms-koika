# LMS-Koika: Collapsing Towers for Side-Channel Security

LMS-Koika is an attempt to use staged programming to detect side-channel
vulnerabilities in hardware-software systems via the [Collapsing Towers of
Interpreters](https://www.cs.purdue.edu/homes/rompf/papers/amin-popl18.pdf)
pattern. The basic idea is to take a staged hardware interpreter (including
micro-architectural details like speculation and data caching) alongside an
assembly program intended to run on that hardware to produce a *residue* C
program that is semantically equivalent to the original assembly program, but
with all side-channel information encoded explicitly. The C file can then be
analyzed by an off-the-shelf analyzer (we use CBMC) to check whether timing
information and secret inputs are noninterfering.

As an example, see [interpcc.scala](src/test/scala/lms/koika/interpcc.scala) and
one of its residues, such as [interpcc_2ct_ni.check.c](src/out/interpcc_2ct_ni.check.c).

## Run
- `sbt test`

## Troubleshoot
- It works in Java v1.8. In Mac OS X: `export JAVA_HOME=$(/usr/libexec/java_home -v1.8)`

# Contributing

see [HACKING.md](HACKING.md)

# [LMS Clean](https://github.com/TiarkRompf/lms-clean)

## Optimizations

The [`rewrite` method of `GraphBuilderOpt` in the LMS Backend](https://github.com/TiarkRompf/lms-clean/blob/master/src/main/scala/lms/core/backend.scala#L524) has the "smart constructor" optimizations that, for example, optimizes read after write for arrays and variables.

The [`GraphBuilderOpt` is linked through the `Adapter` object in the LMS Frontend](https://github.com/TiarkRompf/lms-clean/blob/master/src/main/scala/lms/core/stub.scala#L22). Because the linking is through an object as opposed to a trait, it's not easy to change -- so for now, we will experiment with more optimizations by changing LMS Clean directly.

# [Bounded Model Checking](https://www.cprover.org/cbmc/) (also see [newer releases](https://github.com/diffblue/cbmc) and [doc](http://www.cprover.org/cprover-manual/))
- cd `src/out`
- `cbmc --compact-trace interpcc_2sct_alt.check.c`
- `cbmc -DCBMC --refine --compact-trace --beautify --unwind 200 proci1b_staged_mul.check.c`

