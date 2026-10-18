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
    help: Boolean = false,
    version: Boolean = false,
    listProfiles: Boolean = false
)

object Options:

  val usage: String =
    """kolla - a Lean 4 kernel type checker
      |
      |  kolla [options] <export-file>...
      |
      |An export file is lean4export output: NDJSON 3.x, or either text format.
      |'-' reads standard input. Exit code 0 means every declaration was
      |accepted, 1 that one was rejected, 2 that the file could not be read.
      |
      |  --profile <v>   the Lean release to check as (default the newest)
      |  --json          one JSON object per declaration on stdout
      |  --abort         stop at the first rejection
      |  --only <name>   report only this declaration, repeatable
      |  -v, --verbose   name each declaration as it is checked
      |  -q, --quiet     only the counts and the verdict
      |  --profiles      list the profiles and exit
      |  -h, --help      this message
      |  --version       the version and the default profile
      |""".stripMargin

  val profiles: String =
    KernelProfile.all.map(p => s"  ${p.label}").mkString("profiles\n", "\n", "")

  def parse(args: List[String]): Either[String, Options] =
    def go(rest: List[String], o: Options): Either[String, Options] = rest match
      case Nil                  => Right(o)
      case "--json" :: t        => go(t, o.copy(json = true))
      case "--abort" :: t       => go(t, o.copy(abortOnReject = true))
      case ("-v" | "--verbose") :: t => go(t, o.copy(verbose = true))
      case ("-q" | "--quiet") :: t   => go(t, o.copy(quiet = true))
      case ("-h" | "--help") :: _    => Right(o.copy(help = true))
      case "--version" :: _          => Right(o.copy(version = true))
      case "--profiles" :: _         => Right(o.copy(listProfiles = true))
      case "--only" :: v :: t        => go(t, o.copy(only = o.only :+ v))
      case "--profile" :: v :: t =>
        KernelProfile.all.find(p => p.label == v || p.label == s"v$v") match
          case Some(p) => go(t, o.copy(profile = p))
          case None    => Left(s"unknown profile '$v'\n$profiles")
      case f :: _ if f.startsWith("-") && f != "-" => Left(s"unknown option $f\n\n$usage")
      case f :: t                                  => go(t, o.copy(files = o.files :+ f))
    go(args, Options()).flatMap { o =>
      if o.help || o.version || o.listProfiles then Right(o)
      else if o.files.isEmpty then Left(s"no export file given\n\n$usage")
      else if o.quiet && o.verbose then Left("--quiet and --verbose are mutually exclusive")
      else Right(o)
    }
