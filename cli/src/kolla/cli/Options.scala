package kolla.cli

import kolla.kernel.KernelProfile

/** What the command line asked for. */
final case class Options(
    files: List[String] = Nil,
    profile: KernelProfile = KernelProfile.default,
    /** Emit one JSON object per declaration instead of a human summary. */
    json: Boolean = false,
    /** Stop at the first rejection, as lean4checker does. */
    abortOnReject: Boolean = false,
    /** Print the declaration names as they are checked. */
    verbose: Boolean = false,
    /** Print only the counts and the verdict. */
    quiet: Boolean = false,
    /** Restrict the report to these declarations; empty means all. */
    only: List[String] = Nil,
    /** Note progress on stderr while a long file is being read. */
    progress: Boolean = false,
    /** Check only declarations under these name prefixes; empty means all.
      * Everything else is admitted into the environment unchecked.
      */
    checkOnly: List[String] = Nil,
    /** A file of accepted content digests to reuse and extend. */
    cache: Option[String] = None,
    /** Keep the positive `is_def_eq` cache on a profile that predates it. */
    defeqCache: Boolean = false,
    /** Reduce this term against the export's environment instead of checking. */
    evalTerm: Option[String] = None,
    /** Report what these declarations transitively rest on, repeatable. */
    axiomsOf: List[String] = Nil,
    /** Name each declaration before checking it, and time the slow ones. */
    trace: Boolean = false,
    /** The reduction budget per declaration. Lowering it makes a check that
      * does not finish report what it was doing instead (K21).
      */
    maxSteps: Long = kolla.kernel.TypeChecker.defaultMaxSteps,
    help: Boolean = false,
    version: Boolean = false,
    listProfiles: Boolean = false,
    serve: Boolean = false,
    maxTimeMillis: Option[Long] = None,
    /** The axioms a `--axioms` run accepts, if the caller named them. */
    requireAxioms: Option[Set[String]] = None
)

object Options:

  val usage: String =
    """kolla - a Lean 4 kernel type checker
      |
      |  kolla [options] <export-file>...
      |
      |An export file is lean4export output: NDJSON 3.x, or either text format.
      |'-' reads standard input. Exit code 0 means every declaration was
      |accepted, 1 that one was rejected, 2 that the file could not be read,
      |3 that kolla ran out of memory before reaching a verdict.
      |
      |  --profile <v>   the Lean release to check as (default the newest)
      |  --json          one JSON object per declaration on stdout
      |  --abort         stop at the first rejection
      |  --only <name>   report only this declaration, repeatable
      |  --check <pre>   check only declarations under this name prefix,
      |                  admitting the rest unchecked; repeatable
      |  -v, --verbose   name each declaration as it is checked
      |  -q, --quiet     only the counts and the verdict
      |  --progress      note declarations and bytes read on stderr
      |  --cache <file>  reuse and extend a file of accepted digests
      |  --defeq-cache   keep the positive is_def_eq cache on a profile that
      |                  predates it; needed for a library corpus before v4.35
      |  --max-steps <n> reduction budget per declaration; on exceeding it the
      |                  kernel reports where the reduction went
      |  --max-time <ms> wall-clock budget per declaration, with the same
      |                  report; independent of --max-steps
      |  --trace         name each declaration before checking it, so one
      |                  that never finishes can be identified
      |  --axioms <name> report the axioms this declaration rests on, and
      |                  whether it was left as sorry; repeatable
      |  --eval <term>   reduce a term against the export's environment and
      |                  print it, instead of checking the file
      |  --require-axioms <a,b,c>
      |                  with --axioms, exit 1 unless every declaration rests
      |                  only on these; an empty list permits none
      |  --serve         keep the environment and answer requests on stdin:
      |                  load, check, axioms, gate, type, unfold, names,
      |                  mentions, eval, deadline, status, quit
      |  --profiles      list the profiles and exit
      |  -h, --help      this message
      |  --version       the version and the default profile
      |""".stripMargin

  val profiles: String =
    KernelProfile.all.map(p => s"  ${p.label}").mkString("profiles\n", "\n", "")

  /** The profile a run actually uses, which `--defeq-cache` may amend. */
  def profileOf(o: Options): KernelProfile =
    if o.defeqCache then o.profile.withDefEqSuccessCache else o.profile

  /** Above this many bytes an export is a library rather than a fixture.
    *
    * The largest committed fixture is 17 MB and the smallest library corpus,
    * `init`, is 292 MB, so anything over this is the scale at which a missing
    * positive `is_def_eq` cache stops being a slowdown and starts being a
    * run that does not finish. See docs/semantics.md K18 and P12.
    */
  val libraryScaleBytes: Long = 128L * 1024L * 1024L

  /** The advisory to print before a run that is unlikely to finish.
    *
    * `None` when the profile keeps the cache, when `--defeq-cache` was asked
    * for, or when the input is too small for it to matter.
    */
  def defeqCacheAdvice(o: Options, bytes: Long): Option[String] =
    if o.defeqCache || o.profile.cacheDefEqSuccess || bytes < libraryScaleBytes then None
    else
      Some(
        s"warning: ${o.profile.label} has no positive is_def_eq cache and this input is " +
          f"${bytes / 1048576.0}%.0f MB; a library corpus can exceed 24 GB of heap on this " +
          "profile. Pass --defeq-cache to keep the cache, which changes no verdict."
      )

  /** The predicate `--check` amounts to: a name matches a prefix exactly or is
    * under it. No prefixes means everything is checked.
    */
  def selects(o: Options): kolla.kernel.Name => Boolean =
    if o.checkOnly.isEmpty then _ => true
    else
      val prefixes = o.checkOnly
      n =>
        val s = n.toString
        prefixes.exists(p => s == p || s.startsWith(p + "."))

  def parse(args: List[String]): Either[String, Options] =
    def go(rest: List[String], o: Options): Either[String, Options] = rest match
      case Nil                  => Right(o)
      case "--json" :: t        => go(t, o.copy(json = true))
      case "--abort" :: t       => go(t, o.copy(abortOnReject = true))
      case ("-v" | "--verbose") :: t => go(t, o.copy(verbose = true))
      case ("-q" | "--quiet") :: t   => go(t, o.copy(quiet = true))
      case "--progress" :: t         => go(t, o.copy(progress = true))
      case ("-h" | "--help") :: _    => Right(o.copy(help = true))
      case "--version" :: _          => Right(o.copy(version = true))
      case "--profiles" :: _         => Right(o.copy(listProfiles = true))
      case "--serve" :: t            => go(t, o.copy(serve = true))
      case "--require-axioms" :: v :: t =>
        go(t, o.copy(requireAxioms = Some(v.split(",").map(_.trim).filter(_.nonEmpty).toSet)))
      case "--only" :: v :: t        => go(t, o.copy(only = o.only :+ v))
      case "--check" :: v :: t       => go(t, o.copy(checkOnly = o.checkOnly :+ v))
      case "--cache" :: v :: t       => go(t, o.copy(cache = Some(v)))
      case "--defeq-cache" :: t      => go(t, o.copy(defeqCache = true))
      case "--eval" :: v :: t        => go(t, o.copy(evalTerm = Some(v)))
      case "--axioms" :: v :: t      => go(t, o.copy(axiomsOf = o.axiomsOf :+ v))
      case "--trace" :: t            => go(t, o.copy(trace = true))
      case "--max-time" :: v :: t    =>
        v.replace("_", "").toLongOption match
          case Some(n) if n > 0 => go(t, o.copy(maxTimeMillis = Some(n)))
          case _                => Left(s"--max-time expects a positive number of milliseconds, got $v")
      case "--max-steps" :: v :: t   =>
        v.replace("_", "").toLongOption match
          case Some(n) if n > 0 => go(t, o.copy(maxSteps = n))
          case _                => Left(s"--max-steps expects a positive number, got $v")
      case "--profile" :: v :: t =>
        KernelProfile.all.find(p => p.label == v || p.label == s"v$v") match
          case Some(p) => go(t, o.copy(profile = p))
          case None    => Left(s"unknown profile '$v'\n$profiles")
      case f :: _ if f.startsWith("-") && f != "-" => Left(s"unknown option $f\n\n$usage")
      case f :: t                                  => go(t, o.copy(files = o.files :+ f))
    go(args, Options()).flatMap { o =>
      if o.help || o.version || o.listProfiles then Right(o)
      // The environment can be built entirely through `load` requests, so a
      // file on the command line is a preload rather than the input. That is
      // the only rule `--serve` is exempt from: the checks below still apply,
      // so it cannot pass them by returning early.
      else if o.serve && o.files.length > 1 then
        Left("--serve takes at most one export file to preload")
      else if o.requireAxioms.isDefined && o.axiomsOf.isEmpty && !o.serve then
        Left("--require-axioms needs --axioms, which names what to gate")
      else if o.serve && (o.evalTerm.isDefined || o.axiomsOf.nonEmpty) then
        Left("--serve answers eval and axioms as requests, not as flags")
      // A seeded replay cannot carry a digest cache, and `Replay` refuses the
      // combination, so a cache here could only be silently unused.
      else if o.serve && o.cache.isDefined then
        Left("--serve and --cache are mutually exclusive: a resident environment carries no cache")
      else if o.serve && o.checkOnly.nonEmpty then
        Left("--serve and --check are mutually exclusive: a check request names its own file")
      else if !o.serve && o.files.isEmpty then Left(s"no export file given\n\n$usage")
      else if o.quiet && o.verbose then Left("--quiet and --verbose are mutually exclusive")
      else if o.axiomsOf.nonEmpty && o.evalTerm.isDefined then
        Left("--axioms and --eval are mutually exclusive")
      else if o.axiomsOf.nonEmpty && o.files.length != 1 then
        Left("--axioms takes exactly one export file to read")
      else if o.evalTerm.isDefined && o.files.length != 1 then
        Left("--eval takes exactly one export file to reduce against")
      // Rejected rather than ignored: `--eval` and `--axioms` check nothing,
      // so a cache has nothing to record and a selector nothing to select.
      else if o.evalTerm.isDefined && o.cache.isDefined then
        Left("--eval and --cache are mutually exclusive: --eval checks nothing")
      else if o.evalTerm.isDefined && o.checkOnly.nonEmpty then
        Left("--eval and --check are mutually exclusive: --eval checks nothing")
      else if o.axiomsOf.nonEmpty && o.cache.isDefined then
        Left("--axioms and --cache are mutually exclusive: --axioms checks nothing")
      else if o.axiomsOf.nonEmpty && o.checkOnly.nonEmpty then
        Left("--axioms and --check are mutually exclusive: --axioms checks nothing")
      else Right(o)
    }
