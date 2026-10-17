package kolla.difftest

import cats.effect.IO
import java.nio.file.Files

/** One timing observation, appended to a per-corpus TSV under
  * `difftest/history/`.
  *
  * The file is committed, so a regression shows up as a diff rather than
  * needing an external store. Columns are fixed and append-only.
  */
final case class HistoryRow(
    commit: String,
    at: String,
    checker: String,
    toolchain: String,
    corpus: String,
    platform: String,
    declarations: Int,
    accepted: Int,
    rejected: Int,
    wallNanos: Long,
    peakHeapBytes: Long
):
  def tsv: String =
    List(
      commit, at, checker, toolchain, corpus, platform,
      declarations.toString, accepted.toString, rejected.toString,
      wallNanos.toString, peakHeapBytes.toString
    ).mkString("\t")

object History:

  val header: String =
    List(
      "commit", "at", "checker", "toolchain", "corpus", "platform",
      "declarations", "accepted", "rejected", "wall_nanos", "peak_heap_bytes"
    ).mkString("\t")

  def row(commit: String, at: String, r: CheckerRun): HistoryRow =
    HistoryRow(
      commit, at, r.checker, r.toolchain, r.corpus, r.platform,
      r.results.length, r.accepted, r.rejected, r.wallNanos, r.peakHeapBytes
    )

  /** Appends a report's runs, one file per corpus. */
  def append(report: Report): IO[Unit] =
    IO.blocking {
      report.runs.groupBy(_.corpus).foreach { (corpus, runs) =>
        val file = Layout.historyDir.resolve(s"$corpus.tsv")
        Files.createDirectories(file.getParent)
        val sb = new StringBuilder
        if !Files.exists(file) then sb ++= header + "\n"
        runs.foreach(r => sb ++= row(report.commit, report.startedAt, r).tsv + "\n")
        Files.write(
          file,
          sb.result().getBytes("UTF-8"),
          java.nio.file.StandardOpenOption.CREATE,
          java.nio.file.StandardOpenOption.APPEND
        )
      }
    }

  /** Parses a history file, skipping the header. */
  def parse(contents: String): List[HistoryRow] =
    contents.linesIterator
      .filter(l => l.nonEmpty && !l.startsWith("commit\t"))
      .flatMap { l =>
        l.split('\t') match
          case Array(c, at, ch, tc, co, pl, d, a, rj, w, h) =>
            for
              di <- d.toIntOption
              ai <- a.toIntOption
              ri <- rj.toIntOption
              wl <- w.toLongOption
              hl <- h.toLongOption
            yield HistoryRow(c, at, ch, tc, co, pl, di, ai, ri, wl, hl)
          case _ => None
      }
      .toList
