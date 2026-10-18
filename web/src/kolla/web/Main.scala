package kolla.web

import kolla.kernel.KernelProfile
import kolla.leanexport.*
import scala.scalajs.js

/** kolla in the browser.
  *
  * A check runs in slices on the event loop rather than in `IO`: the page has
  * to stay responsive, and a browser has one thread to do it with. The slice
  * size is a time budget, not a declaration count, because declarations differ
  * in cost by orders of magnitude — one `String` theorem can outweigh a
  * thousand constructors.
  */
object Main:

  /** Milliseconds of checking per animation frame. */
  val sliceMillis: Long = 24L

  def main(args: Array[String]): Unit =
    document.title = "kolla"
    Dom.append(document.body, Layout.page())
    Dom.on(Dom.byId("check"), "click")(start())
    Dom.on(Dom.byId("clear"), "click")(reset())
    // The smoke test drives the page through this, so it does not have to
    // synthesise browser events or know the element ids.
    js.Dynamic.global.kolla = js.Dynamic.literal(
      check = (text: String, profile: String) => runToCompletion(text, profile),
      profiles = js.Array(KernelProfile.all.map(_.label)*)
    )

  private var running = false

  private def reset(): Unit =
    Dom.byId("source").value = ""
    show(Progress(ReplayTally(), 0, 0, 0L, done = false))
    Dom.setText("status", "ready")
    Dom.setHtmlClass("verdict", "idle")

  private def profileOf(label: String): KernelProfile =
    KernelProfile.all.find(_.label == label).getOrElse(KernelProfile.default)

  private def start(): Unit =
    if running then () else
      val text    = Dom.value("source")
      val profile = profileOf(Dom.value("profile"))
      parse(text) match
        case Left(message) =>
          Dom.setText("status", message)
          Dom.setHtmlClass("verdict", "error")
        case Right(items) =>
          running = true
          val replay = new Replay(items, profile)
          val t0     = js.Date.now()
          slice(replay, ReplayTally(), t0)

  private def parse(text: String): Either[String, Vector[ExportItem]] =
    if text.trim.isEmpty then Left("paste an export file first")
    else
      try Right(ExportReader.fromString(text).items)
      catch case e: Throwable => Left(s"could not read the export: ${e.getMessage}")

  /** One frame's worth of checking, then yield to the browser. */
  private def slice(replay: Replay, tally0: ReplayTally, startedAt: Double): Unit =
    var tally = tally0
    val until = js.Date.now() + sliceMillis.toDouble
    while replay.hasNext && js.Date.now() < until do tally = tally.add(replay.next())
    val elapsed = (js.Date.now() - startedAt).toLong
    val done    = !replay.hasNext
    show(Progress(tally, replay.position, replay.size, elapsed, done))
    if done then running = false
    else
      val next = tally
      window.requestAnimationFrame((_: Double) => slice(replay, next, startedAt))

  /** The whole check at once, for the smoke test; returns the counts. */
  private def runToCompletion(text: String, profile: String): js.Dynamic =
    parse(text) match
      case Left(message) => js.Dynamic.literal(error = message)
      case Right(items) =>
        val replay = new Replay(items, profileOf(profile))
        val t0     = js.Date.now()
        var tally  = ReplayTally()
        while replay.hasNext do tally = tally.add(replay.next())
        val p = Progress(tally, replay.position, replay.size, (js.Date.now() - t0).toLong, done = true)
        show(p)
        js.Dynamic.literal(
          accepted = tally.accepted,
          rejected = tally.rejected,
          carriedOver = tally.carriedOver,
          errored = tally.failed,
          total = tally.total,
          ok = tally.ok,
          verdictClass = p.verdictClass
        )

  private def show(p: Progress): Unit =
    Dom.setText("status", p.status)
    Dom.setText("counts", p.counts)
    Dom.setText("timing", p.timing)
    Dom.setText("rejection", p.firstRejection.getOrElse(""))
    Dom.setHtmlClass("verdict", p.verdictClass)
    val bar = Dom.byId("bar")
    if bar != null then bar.style.width = s"${p.percent}%"
