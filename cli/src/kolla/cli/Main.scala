package kolla.cli

import cats.effect.{ExitCode, IO, IOApp}
import cats.effect.std.Console
import fs2.io.file.{Files, Path}
import kolla.kernel.Name
import kolla.leanexport.ReplayOutcome

/** `kolla`, the command line.
  *
  * File access is `fs2.io.file`, not `java.nio`, so the same source builds the
  * JVM jar and the native binary.
  */
object Main extends IOApp:

  val version = "0.1.0"

  def run(args: List[String]): IO[ExitCode] =
    Options.parse(args) match
      case Left(message) => Console[IO].errorln(message).as(ExitCode(2))
      case Right(o) if o.help    => Console[IO].println(Options.usage).as(ExitCode.Success)
      case Right(o) if o.version =>
        Console[IO].println(s"kolla $version, default profile ${o.profile.label}").as(ExitCode.Success)
      // A listing is an answer, not a misuse: stdout and exit 0, so it pipes.
      case Right(o) if o.listProfiles => Console[IO].println(Options.profiles).as(ExitCode.Success)
      case Right(o) => checkAll(o)

  private def checkAll(o: Options): IO[ExitCode] =
    val only = o.only.toSet
    o.files
      .foldLeft(IO.pure(ExitCode.Success)) { (acc, f) =>
        acc.flatMap { worst =>
          checkOne(o, only, f).map(code => if code.code > worst.code then code else worst)
        }
      }

  private def checkOne(o: Options, only: Set[String], file: String): IO[ExitCode] =
    def emit(n: Name, outcome: ReplayOutcome, nanos: Long): IO[Unit] =
      if only.nonEmpty && !only.contains(n.toString) then IO.unit
      else if o.json then Console[IO].println(Render.json(n, outcome, nanos))
      else if o.verbose then Console[IO].println(s"  ${Render.label(outcome)} $n")
      else IO.unit

    val progress =
      if !o.progress then None
      else
        Some((p: Check.Progress) =>
          Console[IO].errorln(f"  ${p.declarations}%,d declarations, ${p.bytesRead / 1048576.0}%.0f MB read")
        )

    val withCache: IO[Option[CacheStore]] = o.cache.fold(IO.pure(None))(CacheStore.load(_).map(Some(_)))

    withCache.flatMap { store =>
      Check
        .stream(
          file, read(file), o.profile, o.abortOnReject, emit, progress,
          Options.selects(o), store, store.map(_.flush)
        )
        .flatMap(reportOne(o, file, _))
    }

  private def reportOne(o: Options, file: String, out: Either[Check.Failure, Check.Result]): IO[ExitCode] =
    out match
      case Left(f: Check.Failure.Exhausted)  => Console[IO].errorln(f.message).as(ExitCode(3))
      case Left(f: Check.Failure.Unreadable) => Console[IO].errorln(f.message).as(ExitCode(2))
      case Right(r) =>
        val reused =
          if r.reusedFromCache == 0 then IO.unit
          else Console[IO].errorln(f"  ${r.reusedFromCache}%,d reused from the cache")
        val admitted =
          if r.admittedUnchecked == 0 then IO.unit
          else Console[IO].errorln(f"  ${r.admittedUnchecked}%,d admitted unchecked")
        val late =
          if r.lateAmbient.isEmpty then IO.unit
          else
            Console[IO].errorln(
              s"  warning: ${r.lateAmbient.map(_.toString).sorted.mkString(", ")} declared after the hoisting window"
            )
        val report =
          if o.json then Console[IO].println(Render.summaryJson(file, o.profile.label, platform, r.tally, r.wallNanos))
          else if o.quiet then Console[IO].println(r.tally.counts)
          else Console[IO].print(Render.summary(file, o.profile.label, r.tally, r.wallNanos))
        reused *> admitted *> late *> report.as(if r.tally.ok then ExitCode.Success else ExitCode(1))

  /** `-` is standard input, so the CLI composes with a pipeline. */
  private def read(file: String): fs2.Stream[IO, Byte] =
    if file == "-" then fs2.io.stdin[IO](1024 * 1024)
    else Files[IO].readAll(Path(file))

  /** Which build produced this binary, for a report that names it. */
  def platform: String = Platform.name
