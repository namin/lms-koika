# LMS-Koika: Collapsing Towers for Side-Channel Security

LMS-Koika is an attempt to use staged programming to detect side-channel
vulnerabilities in hardware-software systems via the [Collapsing Towers of
Interpreters](https://www.cs.purdue.edu/homes/rompf/papers/amin-popl18.pdf)
pattern. The basic idea is to take a staged hardware interpreter (including
micro-architectural details like speculation and data caching) alongside an
assembly program intended to run on that hardware to produce a *residue* C
program that is semantically equivalent to the original assembly program, but
with all side-channel information encoded explicitly. The C file can then be
analyzed by an off-the-shelf analyzer to check whether timing information and
secret inputs are noninterfering.

## Running the examples

This project is built by the [sbt](https://www.scala-sbt.org/) build manager
on Scala 2.12.8. We also depend on [lms-clean](https://github.com/TiarkRompf/lms-clean)
([vendored](vendor/lms-clean)).

Running `sbt test` from the root will regenerate all residues in [`src/out`](src/out).
Snapshot files mostly follow the naming convention of `[testfile]_[suffix].check.c`,
where `[testfile]` names the corresponding scala file in
[`src/test/scala/lms/koika`](src/test/scala/lms/koika).

For more curated examples, see [`src/out/demos`](src/out/demos), generated from
[`src/test/scala/lms/koika/demos`](src/test/scala/lms/koika/demos) (see that folder
for details).

The examples are verified as follows:

`cbmc -DCBMC --verbosity 4 --slice-formula --unwind 1000 --refine --compact-trace <file.c>`

For convenience, we also provide [`verify`](src/out/verify), invoked as

`./verify <file1.c> <file2.c> ...`

Note that not all `.check.c` files are expected to pass verification -- most
are intended to demonstrate that CBMC can detect a vulnerability. We are working
on making a comprehensive list of which files are expected to pass and which do
not.

## Further docs

- [C Bounded Model Checking (CBMC)](https://www.cprover.org/cbmc/doc/manual.pdf)
