package kolla.difftest

import cats.effect.{ExitCode, IO, IOApp}
import java.nio.file.{Files, Path, Paths as JPaths}

/** How a run was configured. */
final case class Options(
    command: String = "run",
    toolchains: List[String] = Nil,
    corpora: List[String] = Nil,
    seeds: List[Long] = List(1L),
    mathlib: Option[Path] = None,
    withChecker: Boolean = true,
    withNanoda: Boolean = true,
    withMutants: Boolean = true,
    /** Also run the native binary and the browser bundle, and compare them to
      * the JVM run declaration by declaration.
      */
    withPlatforms: Boolean = false,
    writeHistory: Boolean = false
)

object Options:

  val usage: String =
    """kolla difftest
      |
      |  run          provision, export, check and compare (default)
      |  provision    install toolchains and build lean4export and lean4checker
      |  export       produce export files only
      |  mutants      check the negative corpus only
      |  platforms    compare the native and js builds against the jvm
      |  list         show the configured toolchains and corpora
      |
      |  --toolchain <spec>     restrict to one toolchain, repeatable
      |  --corpus <name>        restrict to one corpus, repeatable
      |  --seed <n>             mutation seed, repeatable (default 1)
      |  --mathlib <dir>        a mathlib checkout, enabling the mathlib-sample corpus
      |  --no-checker           skip lean4checker
      |  --no-nanoda            skip nanoda
      |  --no-mutants           skip the negative corpus
      |  --platforms            also run the native and js builds and compare
      |  --history              append timings to difftest/history/
      |""".stripMargin

  def parse(args: List[String]): Either[String, Options] =
    def go(rest: List[String], o: Options): Either[String, Options] = rest match
      case Nil                                     => Right(o)
      case "--toolchain" :: v :: t                 => go(t, o.copy(toolchains = o.toolchains :+ v))
      case "--corpus" :: v :: t                    => go(t, o.copy(corpora = o.corpora :+ v))
      case "--seed" :: v :: t                      =>
        v.toLongOption match
          case Some(n) => go(t, o.copy(seeds = o.seeds :+ n))
          case None    => Left(s"--seed expects a number, got $v")
      case "--mathlib" :: v :: t                   => go(t, o.copy(mathlib = Some(JPaths.get(v))))
      case "--no-checker" :: t                     => go(t, o.copy(withChecker = false))
      case "--no-nanoda" :: t                      => go(t, o.copy(withNanoda = false))
      case "--no-mutants" :: t                     => go(t, o.copy(withMutants = false))
      case "--platforms" :: t                      => go(t, o.copy(withPlatforms = true))
      case "--history" :: t                        => go(t, o.copy(writeHistory = true))
      case ("-h" | "--help") :: _                  => Left(usage)
      case f :: _ if f.startsWith("--")            => Left(s"unknown option $f")
      case c :: t                                  => go(t, o.copy(command = c))
    // An explicit `--seed` replaces the default rather than adding to it.
    go(args, Options(seeds = Nil)).map(o => if o.seeds.isEmpty then o.copy(seeds = List(1L)) else o)

object Main extends IOApp:

  def run(args: List[String]): IO[ExitCode] =
    Options.parse(args) match
      case Left(msg) => IO.println(msg).as(ExitCode(2))
      case Right(o)  => dispatch(o)

  private def dispatch(o: Options): IO[ExitCode] =
    for
      toolchains <- selectedToolchains(o)
      corpora    <- selectedCorpora(o)
      code <- o.command match
                case "list"      => list(toolchains, corpora).as(ExitCode.Success)
                case "provision" => toolchains.traverseVoid(t => provisionOne(t, o)).as(ExitCode.Success)
                case "export"    => exportOnly(toolchains, corpora, o).as(ExitCode.Success)
                case "mutants"   => mutantsOnly(toolchains, corpora, o)
                case "platforms" =>
                  full(toolchains, corpora, o.copy(withPlatforms = true, withChecker = false,
                    withNanoda = false, withMutants = false))
                case "run"       => full(toolchains, corpora, o)
                case other       => IO.println(s"unknown command $other\n\n${Options.usage}").as(ExitCode(2))
    yield code

  extension [A](xs: List[A])
    private def traverseVoid(f: A => IO[Unit]): IO[Unit] =
      xs.foldLeft(IO.unit)((acc, a) => acc *> f(a))
    private def traverseAccum[B](f: A => IO[Vector[B]]): IO[Vector[B]] =
      xs.foldLeft(IO.pure(Vector.empty[B]))((acc, a) => acc.flatMap(b => f(a).map(b ++ _)))

  private def selectedToolchains(o: Options): IO[List[Toolchain]] =
    IO.blocking(Toolchains.parse(Layout.readFile(Layout.toolchainsFile))).map { all =>
      if o.toolchains.isEmpty then all
      else all.filter(t => o.toolchains.exists(s => t.spec == s || t.version == s))
    }

  private def selectedCorpora(o: Options): IO[List[Corpus]] =
    for
      cases    <- Corpus.cases
      bad      <- Corpus.negativeCases
      fixtures <- Corpus.fixtures
      ml       <- o.mathlib.fold(IO.pure(List.empty[Corpus]))(d => Corpus.mathlibSample(d).map(List(_)))
      all = cases ++ bad ++ fixtures ++ List(Corpus.init, Corpus.std, Corpus.lean) ++ ml
    yield
      if o.corpora.nonEmpty then all.filter(c => o.corpora.contains(c.name))
      // The committed fixtures need no toolchain, so the platform comparison
      // defaults to them and runs on every push; everything else defaults to
      // the handwritten corpus, which does.
      else if o.command == "platforms" then fixtures
      else cases ++ bad

  private def list(toolchains: List[Toolchain], corpora: List[Corpus]): IO[Unit] =
    IO.println("toolchains") *>
      toolchains.traverseVoid(t =>
        IO.println(s"  ${t.spec}  (profile ${t.profile.label}${if t.hasReference then "" else ", no reference"})")
      ) *>
      IO.println("corpora") *>
      corpora.traverseVoid(c =>
        IO.println(
          s"  ${c.name}  modules=${c.modules.mkString(",")}" +
            (if c.expectRejection then "  (must be rejected)" else "") +
            (if c.toolchains.isEmpty then "" else s"  only ${c.toolchains.mkString(",")}")
        )
      )

  private def provisionOne(t: Toolchain, o: Options): IO[Unit] =
    IO.println(s"provisioning ${t.spec}") *>
      Provision.provision(t, o.withChecker && t.hasReference).void *>
      // nanoda is a reference only for the newest profile, and its build is a
      // full Rust release build; the other toolchains must not pay for it.
      (if o.withNanoda && Nanoda.matchesKernel(t) then Nanoda.provision.void else IO.unit)

  private def exportOnly(toolchains: List[Toolchain], corpora: List[Corpus], o: Options): IO[Unit] =
    toolchains.traverseVoid { t =>
      Provision.provision(t, withChecker = false).flatMap { tools =>
        corpora.filter(_.appliesTo(t)).traverseVoid { c =>
          Exporter.exportFile(tools, c).flatMap(p => IO.println(s"  ${t.version} ${c.name} -> $p"))
        }
      }
    }

  private def mutantsOnly(toolchains: List[Toolchain], corpora: List[Corpus], o: Options): IO[ExitCode] =
    for
      outcomes <- toolchains.traverseAccum(t => mutantsFor(t, corpora, o))
      _        <- IO.print(outcomes.map(_.render).mkString)
      bad = outcomes.count(!_.asExpected)
      _ <- IO.println(s"${outcomes.length - bad}/${outcomes.length} mutants behaved as expected")
    yield if bad == 0 then ExitCode.Success else ExitCode(1)

  private def mutantsFor(t: Toolchain, corpora: List[Corpus], o: Options): IO[Vector[MutationOutcome]] =
    Provision.provision(t, withChecker = false).flatMap { tools =>
      // Mutating a corpus that is already invalid proves nothing, and with the
      // baseline subtraction a mutation of the declaration the baseline already
      // rejected reports no new rejection and so counts as a bad mutant.
      corpora.filter(c => c.appliesTo(t) && !c.expectRejection).traverseAccum { c =>
        for
          path  <- Exporter.exportFile(tools, c)
          items <- IO.blocking(Layout.readFile(path)).map(s => kolla.leanexport.ExportReader.fromString(s).items)
          out   <- MutationRun.run(items, t.profile, t.spec, c.name, o.seeds)
        yield out
      }
    }

  private def full(toolchains: List[Toolchain], corpora: List[Corpus], o: Options): IO[ExitCode] =
    for
      commit <- Report.commit
      at     <- Report.now
      nanoda <- if o.withNanoda && toolchains.exists(Nanoda.matchesKernel) then Nanoda.provision
                else IO.pure(None)
      parts  <- toolchains.traverseAccum(t => oneToolchain(t, corpora, o, nanoda).map(Vector(_)))
      runs        = parts.flatMap(_._1)
      overall     = parts.flatMap(_._2)
      mutations   = parts.flatMap(_._3)
      report      = Report(commit, at, runs, parts.flatMap(_._4), overall, mutations)
      _    <- IO.print(report.render)
      path <- Report.write(report)
      _    <- IO.println(s"report: $path")
      _    <- if o.writeHistory then History.append(report) else IO.unit
    yield if report.agrees then ExitCode.Success else ExitCode(1)

  private type Part =
    (Vector[CheckerRun], Vector[OverallAgreement], Vector[MutationOutcome], Vector[Comparison])

  private def referenceRun(
      tools: Provision.Tools,
      c: Corpus,
      reference: Boolean,
      workers: Option[Int]
  ): IO[Option[CheckerRun]] =
    // lean4checker replays oleans, which a prebuilt export does not have.
    if reference && c.prebuilt.isEmpty then Lean4Checker.run(tools, c, numWorkers = workers).map(Some(_))
    else IO.pure(None)

  private def mutantsOf(
      items: Vector[kolla.leanexport.ExportItem],
      t: Toolchain,
      c: Corpus,
      o: Options
  ): IO[Vector[MutationOutcome]] =
    if o.withMutants && !c.expectRejection then MutationRun.run(items, t.profile, t.spec, c.name, o.seeds)
    else IO.pure(Vector.empty)

  private def oneToolchain(
      t: Toolchain,
      corpora: List[Corpus],
      o: Options,
      nanoda: Option[java.nio.file.Path]
  ): IO[Part] =
    // A corpus that is already an export file needs no Lean at all, so a run
    // over fixtures alone does not download a toolchain.
    val needsLean = corpora.exists(c => c.appliesTo(t) && c.prebuilt.isEmpty)
    Provision.provision(t, o.withChecker && t.hasReference && needsLean, skip = !needsLean).flatMap { tools =>
      corpora
        .filter(_.appliesTo(t))
        .foldLeft(IO.pure((Vector.empty, Vector.empty, Vector.empty, Vector.empty): Part)) { (acc, c) =>
          acc.flatMap { (runs, agree, muts, cmps) =>
            oneCorpus(tools, t, c, o, nanoda).map { (r, a, m, p) =>
              (runs ++ r, agree ++ a, muts ++ m, cmps ++ p)
            }
          }
        }
    }

  private def oneCorpus(
      tools: Provision.Tools,
      t: Toolchain,
      c: Corpus,
      o: Options,
      nanoda: Option[java.nio.file.Path]
  ): IO[Part] =
    val reference = o.withChecker && t.hasReference
    for
      _    <- IO.println(s"${t.version} / ${c.name}")
      path <- Exporter.exportFile(tools, c)
      env  <- IO.blocking(Layout.readFile(path)).map(kolla.leanexport.ExportReader.fromString(_))
      items = env.items
      // Both references abort on the first problem, so kolla must too for the
      // corpus-level verdicts to be comparable.
      useNanoda = o.withNanoda && nanoda.isDefined && Nanoda.applies(t, env.format)
      kolla <- KollaChecker.check(
                 items, t.profile, t.spec, c.name, "jvm",
                 stopOnFirstRejection = reference || useNanoda,
                 expectRejection = c.expectRejection
               )
      // A library corpus is replayed with fewer workers than lean4checker's
      // default, since each loads a near-complete environment.
      workers = if c.source.isDefined || c.prebuilt.isDefined then None else Some(Lean4Checker.libraryWorkers)
      ref <- referenceRun(tools, c, reference, workers)
      nd  <- if useNanoda then Nanoda.run(nanoda, t, c, env.format, path).map(Some(_)) else IO.pure(None)
      // Mutating a corpus that is already invalid proves nothing.
      muts  <- mutantsOf(items, t, c, o)
      other <- if o.withPlatforms then otherPlatforms(path, t, c, kolla) else IO.pure((Vector.empty, Vector.empty))
    yield (
      Vector(kolla) ++ ref.toVector ++ nd.toVector ++ other._1,
      (ref.toVector ++ nd.toVector).map(r => Compare.overall(r, kolla)),
      muts,
      other._2
    )

  /** The native and js builds, compared to the JVM run declaration by
    * declaration. A platform that is not built is skipped rather than failed:
    * the comparison needs `mill cli.native.nativeLink` and `mill web.js.bundle`
    * to have run, which a plain `mill difftest.run` does not do.
    */
  private def otherPlatforms(
      exportFile: java.nio.file.Path,
      t: Toolchain,
      c: Corpus,
      jvm: CheckerRun
  ): IO[(Vector[CheckerRun], Vector[Comparison])] =
    for
      hasNative  <- Platforms.nativeAvailable
      hasNode    <- Platforms.nodeAvailable
      hasBrowser <- Platforms.browserAvailable
      _ <- if hasNative then IO.unit else IO.println("  native: not built, skipping")
      _ <- if hasNode then IO.unit else IO.println("  js: not built or node missing, skipping")
      _ <- if hasBrowser then IO.unit else IO.println("  browser: playwright not installed, skipping")
      nat <- if hasNative then Platforms.native(exportFile, t.profile, t.spec, c.name).map(Some(_))
             else IO.pure(None)
      js <- if hasNode then Platforms.node(exportFile, t.profile, t.spec, c.name).map(Some(_))
            else IO.pure(None)
      web <- if hasBrowser then Platforms.browser(exportFile, t.profile, t.spec, c.name).map(Some(_))
             else IO.pure(None)
      runs = nat.toVector ++ js.toVector ++ web.toVector
    yield (runs, runs.map(r => Compare.platforms(jvm, r)))
