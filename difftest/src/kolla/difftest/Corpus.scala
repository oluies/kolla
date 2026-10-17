package kolla.difftest

import cats.effect.IO
import java.nio.file.{Files, Path}
import scala.jdk.CollectionConverters.*

/** A set of declarations to check, and how to get an export file for it.
  *
  * `modules` are passed to `lean4export` as import roots; `decls`, when
  * non-empty, restrict the export to those constants and their dependencies.
  *
  * A positive corpus is the export of an environment Lean built and accepted, so
  * each declaration in it must be accepted. That expectation is a reference in
  * its own right, and the only one available for a toolchain `lean4checker` has
  * no release for.
  *
  * A negative corpus holds declarations put into the environment with
  * `addDeclCore (doCheck := false)`, which the elaborator will do but the kernel
  * must not: at least one declaration has to be rejected.
  */
final case class Corpus(
    name: String,
    modules: List[String],
    decls: List[String] = Nil,
    source: Option[Path] = None,
    project: Option[Path] = None,
    expectRejection: Boolean = false,
    /** The toolchain versions this corpus applies to, empty meaning all of
      * them. A negative case has to call `Environment.addDeclCore` to get an
      * unchecked declaration into the environment, and that signature changes
      * between releases, so it compiles only under the toolchains it names.
      * See docs/semantics.md P7.
      */
    toolchains: List[String] = Nil
):
  def appliesTo(t: Toolchain): Boolean = toolchains.isEmpty || toolchains.contains(t.version)

object Corpus:

  /** A module from the toolchain's own library, exported in full. */
  def library(name: String, modules: String*): Corpus = Corpus(name, modules.toList)

  /** The directive a case may use to restrict itself to some toolchains. */
  val toolchainsDirective = "-- toolchains:"

  /** A handwritten `.lean` file under `difftest/cases/`. */
  def handwritten(file: Path, expectRejection: Boolean = false, contents: String = ""): Corpus =
    val mod    = file.getFileName.toString.stripSuffix(".lean")
    val prefix = if expectRejection then "bad" else "case"
    Corpus(
      s"$prefix-$mod",
      List(mod),
      source = Some(file),
      expectRejection = expectRejection,
      toolchains = declaredToolchains(contents)
    )

  /** The versions a `-- toolchains:` line names, or nothing if there is none. */
  def declaredToolchains(contents: String): List[String] =
    contents.linesIterator
      .map(_.trim)
      .find(_.startsWith(toolchainsDirective))
      .toList
      .flatMap(_.drop(toolchainsDirective.length).split("\\s+").toList.map(_.trim).filter(_.nonEmpty))

  private def lean(dir: Path, expectRejection: Boolean): IO[List[Corpus]] =
    IO.blocking {
      if !Files.isDirectory(dir) then Nil
      else
        Files
          .list(dir)
          .iterator
          .asScala
          .filter(_.getFileName.toString.endsWith(".lean"))
          .toList
          .sortBy(_.getFileName.toString)
          .map(f => handwritten(f, expectRejection, Layout.readFile(f)))
    }

  /** Every `.lean` file under `difftest/cases/`, each its own corpus. */
  def cases: IO[List[Corpus]] = lean(Layout.casesDir, expectRejection = false)

  /** Every `.lean` file under `difftest/cases-negative/`. */
  def negativeCases: IO[List[Corpus]] = lean(Layout.negativeCasesDir, expectRejection = true)

  /** The declarations named in `difftest/mathlib-sample.txt`, exported from a
    * mathlib checkout the caller provides.
    */
  def mathlibSample(project: Path): IO[Corpus] =
    IO.blocking(Layout.readFile(Layout.mathlibSampleFile)).map { contents =>
      val names = contents.linesIterator.map(_.trim).filter(l => l.nonEmpty && !l.startsWith("#")).toList
      Corpus("mathlib-sample", List("Mathlib"), decls = names, project = Some(project))
    }

  val init: Corpus = library("init", "Init")
  val std: Corpus  = library("std", "Std")
  val lean: Corpus = library("lean", "Lean")

/** Produces export files with a toolchain's own `lean4export`. */
object Exporter:

  private def exportBin(tools: Provision.Tools): Path =
    tools.lean4export.resolve(".lake/build/bin/lean4export")

  /** Compiles a handwritten case to an olean and returns its search path. */
  private def compileSource(tools: Provision.Tools, file: Path): IO[Path] =
    val out = Layout.toolchainCache(tools.toolchain).resolve("cases")
    val mod = file.getFileName.toString.stripSuffix(".lean")
    for
      _ <- IO.blocking(Files.createDirectories(out))
      _ <- Proc
             .run(
               Seq("elan", "run", tools.toolchain.spec, "lean", "-o", out.resolve(s"$mod.olean").toString, file.toString)
             )
             .flatMap(_.orFail(s"lean -o $mod.olean"))
    yield out

  /** The export file for a corpus, built if it is not cached. */
  def exportFile(tools: Provision.Tools, corpus: Corpus): IO[Path] =
    val target = Layout.exportFile(tools.toolchain, corpus.name)
    IO.blocking(Files.exists(target)).flatMap { cached =>
      if cached then IO.pure(target)
      else build(tools, corpus, target).as(target)
    }

  /** The declarations a module declares itself, sorted for determinism. */
  private def ownDecls(tools: Provision.Tools, searchPath: Path, module: String): IO[List[String]] =
    Proc
      .run(
        Seq(
          "elan", "run", tools.toolchain.spec,
          "lean", "--run", Layout.listDeclsScript.toString, module
        ),
        env = Map("LEAN_PATH" -> leanPath(searchPath))
      )
      .flatMap(_.orFail(s"ListDecls $module"))
      .map(_.stdout.linesIterator.map(_.trim).filter(_.nonEmpty).toList.sorted)

  private def build(tools: Provision.Tools, corpus: Corpus, target: Path): IO[Unit] =
    val tmp = target.resolveSibling(target.getFileName.toString + ".part")
    for
      searchPath <- corpus.source.fold(IO.pure(Option.empty[Path]))(f => compileSource(tools, f).map(Some(_)))
      // A handwritten case is exported as its own declarations plus their
      // dependencies; exporting its whole environment would pull in all of
      // `Init`, which is what the `init` corpus is for.
      decls <-
        if corpus.decls.nonEmpty then IO.pure(corpus.decls)
        else
          searchPath match
            case Some(p) => corpus.modules.foldLeft(IO.pure(List.empty[String]))((acc, m) =>
                              acc.flatMap(d => ownDecls(tools, p, m).map(d ++ _))
                            )
            case None => IO.pure(Nil)
      args = corpus.modules ++ (if decls.isEmpty then Nil else "--" :: decls)
      cmd =
        // `lake env` is needed only for a project corpus: a library module and a
        // handwritten case both resolve through the toolchain's own sysroot.
        if corpus.project.isDefined then
          Seq("elan", "run", tools.toolchain.spec, "lake", "env", exportBin(tools).toString) ++ args
        else Seq("elan", "run", tools.toolchain.spec, exportBin(tools).toString) ++ args
      env = searchPath.fold(Map.empty[String, String])(p => Map("LEAN_PATH" -> leanPath(p)))
      _ <- Proc
             .run(cmd, cwd = corpus.project, env = env, stdoutTo = Some(tmp))
             .flatMap(_.orFail(s"lean4export ${corpus.name}"))
      _ <- IO.blocking(Files.move(tmp, target, java.nio.file.StandardCopyOption.REPLACE_EXISTING)).void
    yield ()

  /** Prepends a directory to any inherited `LEAN_PATH`. */
  private def leanPath(dir: Path): String =
    Option(System.getenv("LEAN_PATH")).filter(_.nonEmpty) match
      case Some(existing) => s"$dir${java.io.File.pathSeparator}$existing"
      case None           => dir.toString
