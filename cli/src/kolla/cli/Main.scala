package kolla.cli

import cats.effect.{ExitCode, IO, IOApp}
import cats.effect.std.Console
import fs2.io.file.{Files, Path}
import kolla.kernel.Name
import kolla.leanexport.{ReplayJson, ReplayOutcome}

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
      case Right(o) if o.evalTerm.isDefined => evalOne(o, o.evalTerm.get)
      case Right(o) => checkAll(o)

  /** Reduces a term against the export's environment.
    *
    * The environment is built by admitting the file's declarations, not by
    * checking them: the point is to compute, and re-deriving a library to
    * evaluate `Nat.add 2 2` would be absurd. That makes the answer depend on
    * the file being honest, which is why it is said out loud on stderr. Check
    * the file separately if that matters. See docs/semantics.md D13.
    */
  private def evalOne(o: Options, src: String): IO[ExitCode] =
    val file    = o.files.head
    val profile = Options.profileOf(o)
    Check
      .stream(file, read(file), profile, abortOnReject = false,
              (_, _, _) => IO.unit, None, _ => false)
      .flatMap {
        case Left(f)  => Console[IO].errorln(f.message).as(ExitCode(if f.isInstanceOf[Check.Failure.Exhausted] then 3 else 2))
        case Right(r) =>
          kolla.dsl.LeanParser.parse(src) match
            case Left(err) => Console[IO].errorln(s"--eval: ${err.message} at offset ${err.offset}").as(ExitCode(2))
            case Right(term) =>
              Console[IO].errorln(
                f"  ${r.tally.carriedOver}%,d declarations admitted unchecked as ${profile.label}"
              ) *> IO(kolla.dsl.Evaluate(r.environment, profile, term)).flatMap {
                case Left(why) => Console[IO].errorln(s"--eval: $why").as(ExitCode(1))
                case Right(res) =>
                  val out =
                    if o.json then
                      ReplayJson.evaluation(src, res.value.toString, res.tpe.toString, profile.label)
                    else s"${res.value} : ${res.tpe}"
                  Console[IO].println(out).as(ExitCode.Success)
              }
      }

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

    val profile = Options.profileOf(o)

    // Said before the run rather than after it: the point is not to start a
    // run that cannot finish. Standard input has no size to go on.
    val advise: IO[Unit] =
      if file == "-" then IO.unit
      else
        Files[IO]
          .size(Path(file))
          .attempt
          .flatMap {
            case Right(n) => Options.defeqCacheAdvice(o, n).fold(IO.unit)(Console[IO].errorln)
            case Left(_)  => IO.unit
          }

    val withCache: IO[Option[CacheStore]] = o.cache.fold(IO.pure(None))(CacheStore.load(_).map(Some(_)))

    advise *> withCache.flatMap { store =>
      Check
        .stream(
          file, read(file), profile, o.abortOnReject, emit, progress,
          Options.selects(o), store, store.map(_.flush)
        )
        .flatMap(reportOne(o, profile, file, _))
    }

  private def reportOne(
      o: Options, profile: kolla.kernel.KernelProfile, file: String,
      out: Either[Check.Failure, Check.Result]
  ): IO[ExitCode] =
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
          if o.json then Console[IO].println(Render.summaryJson(file, profile.label, platform, r.tally, r.wallNanos))
          else if o.quiet then Console[IO].println(r.tally.counts)
          else Console[IO].print(Render.summary(file, profile.label, r.tally, r.wallNanos))
        reused *> admitted *> late *> report.as(if r.tally.ok then ExitCode.Success else ExitCode(1))

  /** `-` is standard input, so the CLI composes with a pipeline. */
  private def read(file: String): fs2.Stream[IO, Byte] =
    if file == "-" then fs2.io.stdin[IO](1024 * 1024)
    else Files[IO].readAll(Path(file))

  /** Which build produced this binary, for a report that names it. */
  def platform: String = Platform.name
