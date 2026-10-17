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
    withMutants: Boolean = true,
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
      |  list         show the configured toolchains and corpora
      |
      |  --toolchain <spec>     restrict to one toolchain, repeatable
      |  --corpus <name>        restrict to one corpus, repeatable
      |  --seed <n>             mutation seed, repeatable (default 1)
      |  --mathlib <dir>        a mathlib checkout, enabling the mathlib-sample corpus
      |  --no-checker           skip lean4checker
      |  --no-mutants           skip the negative corpus
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
      case "--no-mutants" :: t                     => go(t, o.copy(withMutants = false))
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
      cases <- Corpus.cases
      ml    <- o.mathlib.fold(IO.pure(List.empty[Corpus]))(d => Corpus.mathlibSample(d).map(List(_)))
      all = cases ++ List(Corpus.init, Corpus.std, Corpus.lean) ++ ml
    yield if o.corpora.isEmpty then cases else all.filter(c => o.corpora.contains(c.name))

  private def list(toolchains: List[Toolchain], corpora: List[Corpus]): IO[Unit] =
    IO.println("toolchains") *>
      toolchains.traverseVoid(t =>
        IO.println(s"  ${t.spec}  (profile ${t.profile.label}${if t.hasReference then "" else ", no reference"})")
      ) *>
      IO.println("corpora") *>
      corpora.traverseVoid(c => IO.println(s"  ${c.name}  modules=${c.modules.mkString(",")}"))

  private def provisionOne(t: Toolchain, o: Options): IO[Unit] =
    IO.println(s"provisioning ${t.spec}") *> Provision.provision(t, o.withChecker && t.hasReference).void

  private def exportOnly(toolchains: List[Toolchain], corpora: List[Corpus], o: Options): IO[Unit] =
    toolchains.traverseVoid { t =>
      Provision.provision(t, withChecker = false).flatMap { tools =>
        corpora.traverseVoid { c =>
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
      corpora.traverseAccum { c =>
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
      parts  <- toolchains.traverseAccum(t => oneToolchain(t, corpora, o).map(Vector(_)))
      runs        = parts.flatMap(_._1)
      overall     = parts.flatMap(_._2)
      mutations   = parts.flatMap(_._3)
      report      = Report(commit, at, runs, Vector.empty, overall, mutations)
      _    <- IO.print(report.render)
      path <- Report.write(report)
      _    <- IO.println(s"report: $path")
      _    <- if o.writeHistory then History.append(report) else IO.unit
    yield if report.agrees then ExitCode.Success else ExitCode(1)

  private type Part = (Vector[CheckerRun], Vector[OverallAgreement], Vector[MutationOutcome])

  private def oneToolchain(t: Toolchain, corpora: List[Corpus], o: Options): IO[Part] =
    Provision.provision(t, o.withChecker && t.hasReference).flatMap { tools =>
      corpora.foldLeft(IO.pure((Vector.empty, Vector.empty, Vector.empty): Part)) { (acc, c) =>
        acc.flatMap { (runs, agree, muts) =>
          oneCorpus(tools, t, c, o).map { (r, a, m) =>
            (runs ++ r, agree ++ a, muts ++ m)
          }
        }
      }
    }

  private def oneCorpus(tools: Provision.Tools, t: Toolchain, c: Corpus, o: Options): IO[Part] =
    val reference = o.withChecker && t.hasReference
    for
      _     <- IO.println(s"${t.version} / ${c.name}")
      path  <- Exporter.exportFile(tools, c)
      items <- IO.blocking(Layout.readFile(path)).map(s => kolla.leanexport.ExportReader.fromString(s).items)
      // `lean4checker` aborts on the first problem, so kolla must too for the
      // corpus-level verdicts to be comparable.
      kolla <- KollaChecker.check(items, t.profile, t.spec, c.name, "jvm", stopOnFirstRejection = reference)
      ref   <- if reference then Lean4Checker.run(tools, c).map(Some(_)) else IO.pure(None)
      muts  <- if o.withMutants then MutationRun.run(items, t.profile, t.spec, c.name, o.seeds)
               else IO.pure(Vector.empty)
    yield (
      Vector(kolla) ++ ref.toVector,
      ref.toVector.map(r => Compare.overall(r, kolla)),
      muts
    )
