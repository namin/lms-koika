name := "lms-koika"

scalaVersion := "2.12.8"

resolvers += Resolver.sonatypeRepo("snapshots")

libraryDependencies += "org.scalatest" % "scalatest_2.12" % "3.0.4"

libraryDependencies += "org.scala-lang" % "scala-compiler" % scalaVersion.value % "compile"

libraryDependencies += "org.scala-lang" % "scala-library" % scalaVersion.value % "compile"

libraryDependencies += "org.scala-lang" % "scala-reflect" % scalaVersion.value % "compile"

autoCompilerPlugins := true

val paradiseVersion = "2.1.0"

addCompilerPlugin("org.scalamacros" % "paradise" % paradiseVersion cross CrossVersion.full)

// tests are not thread safe
parallelExecution in Test := false

lazy val lms = (project in file("vendor/lms-clean"))
lazy val koika = (project in file(".")).dependsOn(lms)
