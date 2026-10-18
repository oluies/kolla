package kolla.cli

import cats.effect.IO
import fs2.Stream
import fs2.io.file.{Files, Flags, Path}
import kolla.leanexport.{Digest, ReplayCache}
import scala.collection.mutable

/** The accepted-digest cache, as a file of one hex digest per line.
  *
  * Reusing a digest is trusting it, so the file is part of what a verdict rests
  * on. It is opt-in for that reason and never consulted unless `--cache` names
  * it. See docs/semantics.md P15.
  *
  * New digests are appended rather than rewritten, so a run that dies partway
  * leaves the work it did finish behind — which is what makes a failure at 90%
  * cheap to retry rather than a full restart.
  */
final class CacheStore private (
    val path: Path,
    private val known: mutable.HashSet[Digest]
) extends ReplayCache:

  private val pending = mutable.ArrayBuffer.empty[Digest]

  def contains(d: Digest): Boolean = known.contains(d)

  def accepted(d: Digest): Unit =
    if known.add(d) then pending += d

  def loaded: Int = known.size

  /** Appends what has accumulated. Safe to call at any point and at the end. */
  def flush: IO[Unit] =
    IO(if pending.isEmpty then Vector.empty else { val v = pending.toVector; pending.clear(); v })
      .flatMap { batch =>
        if batch.isEmpty then IO.unit
        else
          Stream
            .emits(batch.map(_.hex))
            .intersperse("\n")
            .append(Stream.emit("\n"))
            .through(fs2.text.utf8.encode)
            .through(Files[IO].writeAll(path, Flags.Append))
            .compile
            .drain
      }

object CacheStore:

  /** Reads the digests already in the file, if it is there.
    *
    * A line that is not a digest is ignored rather than fatal: the file is a
    * cache, and the worst a bad line can cost is a re-check.
    */
  def load(file: String): IO[CacheStore] =
    val path = Path(file)
    Files[IO].exists(path).flatMap { there =>
      val read =
        if !there then IO.pure(Vector.empty[Digest])
        else
          Files[IO]
            .readUtf8Lines(path)
            .map(_.trim)
            .filter(_.nonEmpty)
            .map(Digest.parse)
            .collect { case Some(d) => d }
            .compile
            .toVector
      read.map(ds => new CacheStore(path, mutable.HashSet.from(ds)))
    }
