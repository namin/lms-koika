# LMS Koika

An early experiment.

## Install
- in parent directory: `git clone https://github.com/namin/lms-clean.git`
- `cd lms-clean`
- `git checkout x-koika-rewrite-chains-rec`

## Run
- `sbt test`

## Troubleshoot
- It works in Java v1.8. In Mac OS X: `export JAVA_HOME=$(/usr/libexec/java_home -v1.8)`

# [LMS Clean](https://github.com/TiarkRompf/lms-clean)

## Optimizations

The [`rewrite` method of `GraphBuilderOpt` in the LMS Backend](https://github.com/TiarkRompf/lms-clean/blob/master/src/main/scala/lms/core/backend.scala#L524) has the "smart constructor" optimizations that, for example, optimizes read after write for arrays and variables.

The [`GraphBuilderOpt` is linked through the `Adapter` object in the LMS Frontend](https://github.com/TiarkRompf/lms-clean/blob/master/src/main/scala/lms/core/stub.scala#L22). Because the linking is through an object as opposed to a trait, it's not easy to change -- so for now, we will experiment with more optimizations by changing LMS Clean directly.
