name := "simp"

version := "0.0.1"


sbtVersion in Global := "1.11.6"

scalaVersion := "3.7.2"

resolvers += "Typesafe Repository" at "https://repo.typesafe.com/typesafe/releases/"

resolvers += "Maven Repository" at "https://mvnrepository.com/artifact/"

resolvers += "clojars" at "https://clojars.org/repo"

resolvers += "luzhuomi github repo" at "https://raw.githubusercontent.com/luzhuomi/mavenrepo/master/"

libraryDependencies += "org.ow2.asm" % "asm" % "9.6"

libraryDependencies += "org.scalactic" % "scalactic_3" % "3.2.10"

libraryDependencies += "org.scalatest" % "scalatest_3" % "3.2.10" % "test"

libraryDependencies += "org.scalatest" % "scalatest-funsuite_3" % "3.2.10" % "test"


scalacOptions ++= Seq("-feature", "-deprecation", "-Yresolve-term-conflict:package", "-source:future") // , "-Ypartial-unification" )

val jarName = "simp_all.jar"

assembly/assemblyJarName := jarName

Compile / mainClass := Some("sutd.compiler.simp.Main")
