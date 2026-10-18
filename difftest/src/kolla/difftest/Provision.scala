package kolla.difftest

import cats.effect.IO
import java.nio.file.{Files, Path}

/** Installs a Lean toolchain and builds the tools the platform needs against
  * it, caching everything under `.difftest/<toolchain>/`.
  *
  * Nothing here is cheap: each toolchain is a multi-gigabyte download and each
  * tool is a `lake build`. Every step is therefore idempotent and guarded by a
  * marker file, so a second run is a no-op.
  */
object Provision:

  val lean4exportRepo  = "https://github.com/leanprover/lean4export.git"
  val lean4checkerRepo = "https://github.com/leanprover/lean4checker.git"

  final case class Tools(
      toolchain: Toolchain,
      lean4export: Path,
      lean4checker: Option[Path]
  )

  private def marker(dir: Path, name: String): Path = dir.resolve(s".$name.ok")

  private def once(dir: Path, name: String)(step: IO[Unit]): IO[Unit] =
    IO.blocking(Files.exists(marker(dir, name))).flatMap { done =>
      if done then IO.unit
      else
        step *> IO.blocking {
          Files.createDirectories(dir)
          Files.write(marker(dir, name), Array.emptyByteArray)
          ()
        }
    }

  /** `elan toolchain install`. */
  def installToolchain(t: Toolchain): IO[Unit] =
    val dir = Layout.toolchainCache(t)
    once(dir, "toolchain") {
      Proc.which("elan").flatMap {
        case None =>
          IO.raiseError(new RuntimeException("elan is not on PATH; install it from https://github.com/leanprover/elan"))
        case Some(_) =>
          Proc.run(Seq("elan", "toolchain", "install", t.spec))
            .flatMap(_.orFail(s"elan toolchain install ${t.spec}"))
            .void
      }
    }

  /** Clones `repo` and checks out the revision that pins exactly this toolchain.
    *
    * The match has to be exact. A tool's source tracks Lean's internal APIs, so
    * a revision pinning an older release will not compile against a newer one:
    * `lean4checker` at its v4.29.0-rc8 head calls `Environment.addDeclCore` with
    * the v4.29 signature, which v4.35 changed. Building a near-miss revision
    * against the target toolchain fails, and silently accepting one would be
    * worse: a reference checker built from the wrong source is not a reference.
    */
  def cloneForToolchain(t: Toolchain, repo: String, name: String): IO[Path] =
    val dir = Layout.toolchainCache(t).resolve(name)
    once(Layout.toolchainCache(t), s"clone-$name") {
      for
        // A previous run may have been interrupted between the clone and the
        // marker write, which would leave `git clone` with a non-empty target.
        _ <- IO.blocking {
               Files.createDirectories(dir.getParent)
               Fs.removeRecursively(dir)
             }
        _ <- Proc.run(Seq("git", "clone", "--quiet", repo, dir.toString))
               .flatMap(_.orFail(s"git clone $repo"))
        rev <- resolveRevision(dir, t)
        _   <- Proc.run(Seq("git", "checkout", "--quiet", rev), cwd = Some(dir))
                 .flatMap(_.orFail(s"git checkout $rev in $name"))
      yield ()
    }.as(dir)

  /** The revision of a tool repository that pins exactly this toolchain. */
  def resolveRevision(dir: Path, t: Toolchain): IO[String] =
    val tag = s"refs/tags/${t.version}"
    pinnedToolchain(dir, tag).flatMap {
      case Some(p) if p == t.spec => IO.pure(tag)
      case _                      => searchHistory(dir, t)
    }

  /** The `lean-toolchain` a revision pins, or `None` if it has no such file. */
  private def pinnedToolchain(dir: Path, rev: String): IO[Option[String]] =
    // `git show <rev>:<path>` is avoided: `ls-tree` plus `cat-file` keeps the
    // revision and the path in separate arguments.
    Proc.run(Seq("git", "ls-tree", "--object-only", rev, "lean-toolchain"), cwd = Some(dir)).flatMap { ls =>
      val blob = ls.stdout.trim
      if !ls.ok || blob.isEmpty then IO.pure(None)
      else
        Proc
          .run(Seq("git", "cat-file", "blob", blob), cwd = Some(dir))
          .map(c => if c.ok then Some(c.stdout.trim) else None)
    }

  /** The newest commit touching `lean-toolchain` that pins exactly the target. */
  private def searchHistory(dir: Path, t: Toolchain): IO[String] =
    Proc
      .run(Seq("git", "log", "--all", "--format=%H", "--", "lean-toolchain"), cwd = Some(dir))
      .flatMap(_.orFail("git log lean-toolchain"))
      .flatMap { log =>
        log.stdout.linesIterator.toList
          .foldLeft(IO.pure(Option.empty[String])) { (acc, c) =>
            acc.flatMap {
              case found @ Some(_) => IO.pure(found)
              case None            => pinnedToolchain(dir, c).map(p => if p.contains(t.spec) then Some(c) else None)
            }
          }
          .flatMap {
            case Some(c) => IO.pure(c)
            case None =>
              IO.raiseError(new RuntimeException(s"${dir.getFileName} has no revision pinning ${t.spec}"))
          }
      }

  /** `lake build` in a tool directory.
    *
    * The checked-out revision already pins the target toolchain, so `lake`
    * follows the repository's own `lean-toolchain`; rewriting it is what would
    * produce the API mismatch `resolveRevision` exists to avoid.
    */
  def lakeBuild(t: Toolchain, dir: Path, name: String): IO[Unit] =
    once(Layout.toolchainCache(t), s"build-$name") {
      Proc
        .run(Seq("lake", "build"), cwd = Some(dir))
        .flatMap(_.orFail(s"lake build in $name"))
        .void
    }

  /** Everything one toolchain needs. `lean4checker` is optional: a toolchain
    * with no matching revision is still usable for kolla-only runs.
    */
  def provision(t: Toolchain, withChecker: Boolean = true, skip: Boolean = false): IO[Tools] =
    if skip then IO.pure(Tools(t, Layout.toolchainCache(t).resolve("lean4export"), None))
    else provisionNow(t, withChecker)

  private def provisionNow(t: Toolchain, withChecker: Boolean): IO[Tools] =
    for
      _        <- installToolchain(t)
      exporter <- cloneForToolchain(t, lean4exportRepo, "lean4export")
      _        <- lakeBuild(t, exporter, "lean4export")
      checker  <-
        if !withChecker then IO.pure(None)
        else
          cloneForToolchain(t, lean4checkerRepo, "lean4checker")
            .flatTap(d => lakeBuild(t, d, "lean4checker"))
            .map(Some(_))
            .handleErrorWith(e => IO.println(s"  lean4checker unavailable for ${t.spec}: ${e.getMessage}").as(None))
    yield Tools(t, exporter, checker)
