package kolla.cli

import cats.effect.{ExitCode, IO, IOApp}
import cats.effect.std.Console
import fs2.io.file.{Files, Path}
import kolla.kernel.{Name, Pretty}
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
      case Right(o) if o.serve              => Serve.run(o, read)
      case Right(o) if o.axiomsOf.nonEmpty  => axiomsOf(o)
      case Right(o) if o.evalTerm.isDefined => evalOne(o, o.evalTerm.get)
      case Right(o) => checkAll(o)

  /** Reports what declarations rest on, which type-checking does not say.
    *
    * The environment is admitted rather than checked, as `--eval` does and
    * for the same reason: the question here is what the file *claims*, not
    * whether the claims follow. A `sorry` type-checks like a proof, so this is
    * the report that distinguishes them. Exit 1 when any named declaration
    * rests on `sorryAx` or on an axiom outside Lean's trust base, so a script
    * can act on it. See docs/semantics.md A1.
    */
  private def axiomsOf(o: Options): IO[ExitCode] =
    val file    = o.files.head
    val profile = Options.profileOf(o)
    Check
      .stream(file, read(file), profile, abortOnReject = false,
              (_, _, _) => IO.unit, progressOf(o), _ => false)
      .flatMap {
        case Left(f: Check.Failure.Exhausted)  => Console[IO].errorln(f.message).as(ExitCode(3))
        case Left(f)                           => Console[IO].errorln(f.message).as(ExitCode(2))
        case Right(r) =>
          val closures = o.axiomsOf.map(nm => kolla.kernel.Axioms.of(r.environment, Name.parse(nm)))
          val unknown  = closures.collect { case Left(why) => why }
          val found    = closures.collect { case Right(c) => c }
          for
            _ <- Console[IO].errorln(
                   f"  ${r.tally.carriedOver}%,d declarations read as ${profile.label}"
                 )
            _ <- unknown.foldLeft(IO.unit)((acc, w) => acc *> Console[IO].errorln(s"--axioms: $w"))
            _ <- found.foldLeft(IO.unit) { (acc, c) =>
                   acc *> Console[IO].println(
                     if o.json then ReplayJson.axioms(c.declaration.toString,
                                                      c.axioms.map(_.toString), c.hasSorry,
                                                      c.unusual.map(_.toString), profile.label)
                     else c.render.stripSuffix("\n")
                   )
                 }
          yield axiomExit(found, unknown.nonEmpty)
      }

  /** The exit code for a set of closures.
    *
    * A verdict outranks a misspelling: a closure resting on `sorryAx` or on an
    * axiom outside Lean's trust base is the answer even when another name on
    * the command line was not in the file.
    */
  private[cli] def axiomExit(found: List[kolla.kernel.Axioms.Closure], unknown: Boolean): ExitCode =
    if found.exists(c => c.hasSorry || c.unusual.nonEmpty) then ExitCode(1)
    else if unknown then ExitCode(2)
    else ExitCode.Success

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
    // Parsed before the replay, not after: a typo in the term should not cost
    // the minutes it takes to read a library export.
    kolla.dsl.LeanParser.parse(src) match
      case Left(err) =>
        Console[IO].errorln(s"--eval: ${err.message} at offset ${err.offset}").as(ExitCode(2))
      case Right(term) =>
        Check
          .stream(file, read(file), profile, abortOnReject = false,
                  (_, _, _) => IO.unit, progressOf(o), _ => false, None, None, None, o.maxSteps)
          .flatMap {
            case Left(f: Check.Failure.Exhausted)  => Console[IO].errorln(f.message).as(ExitCode(3))
            case Left(f)                           => Console[IO].errorln(f.message).as(ExitCode(2))
            case Right(r) =>
              Console[IO].errorln(
                f"  ${r.tally.carriedOver}%,d declarations admitted unchecked as ${profile.label}"
              ) *> IO(kolla.dsl.Evaluate(r.environment, profile, term, o.maxSteps)).flatMap {
                case Left(why) => Console[IO].errorln(s"--eval: $why").as(ExitCode(1))
                case Right(res) =>
                  // Printed unbounded: here the term is the answer, and
                  // `Expr.toString` truncates at `Pretty.defaultMaxChars`.
                  val value = Pretty.expr(res.value, Int.MaxValue)
                  val tpe   = Pretty.expr(res.tpe, Int.MaxValue)
                  val warn =
                    if !res.partial then IO.unit
                    else
                      Console[IO].errorln(
                        s"  warning: reduction stopped at depth ${kolla.dsl.Evaluate.maxDepth};" +
                          " the term below is only partly reduced"
                      )
                  val out =
                    if o.json then ReplayJson.evaluation(src, value, tpe, profile.label)
                    else s"$value : $tpe"
                  warn *> Console[IO].println(out).as(ExitCode.Success)
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

  /** How long a step has to take before it is worth a line of its own. */
  private val slowStepMillis: Long = 1000L

  /** Names a declaration before it is checked, and again if it was slow.
    *
    * The "start" line is the one that matters: a declaration that does not
    * terminate produces only that, so the last unpaired name is the culprit.
    * Without it a stuck run is anonymous, which is how
    * `CategoryTheory.Localization.Monoidal.braidingNatIso` took a thread dump
    * and a second run to identify. See docs/semantics.md K20.
    */
  private def traceOf(o: Options): Option[(List[Name], Option[Long]) => IO[Unit]] =
    if !o.trace then None
    else
      Some { (names, took) =>
        val what = names.headOption.fold("<nothing>")(_.toString)
        val more = if names.length > 1 then s" (+${names.length - 1} more)" else ""
        took match
          case None => Console[IO].errorln(s"  start $what$more")
          case Some(ns) =>
            val ms = ns / 1000000L
            if ms < slowStepMillis then IO.unit
            else Console[IO].errorln(f"  slow  $what$more ${ms}%,d ms")
      }

  /** The periodic note on stderr, shared by checking and `--eval`. */
  private def progressOf(o: Options): Option[Check.Progress => IO[Unit]] =
    if !o.progress then None
    else
      Some((p: Check.Progress) =>
        Console[IO].errorln(f"  ${p.declarations}%,d declarations, ${p.bytesRead / 1048576.0}%.0f MB read")
      )

  private def checkOne(o: Options, only: Set[String], file: String): IO[ExitCode] =
    def emit(n: Name, outcome: ReplayOutcome, nanos: Long): IO[Unit] =
      if only.nonEmpty && !only.contains(n.toString) then IO.unit
      else if o.json then Console[IO].println(Render.json(n, outcome, nanos))
      else if o.verbose then Console[IO].println(s"  ${Render.label(outcome)} $n")
      else IO.unit

    val progress = progressOf(o)

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
          Options.selects(o), store, store.map(_.flush), traceOf(o), o.maxSteps
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
