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
    // The same bundle runs in a browser and under Node, where there is no
    // document. Node is how the differential platform gets a JS run to compare
    // per declaration; the page is the part that needs a DOM.
    if hasDocument then
      document.title = "kolla"
      Dom.append(document.body, Layout.page())
      Dom.on(Dom.byId("check"), "click")(start())
      Dom.on(Dom.byId("clear"), "click")(reset())
    // The browser smoke test drives the page through this too, so it does not
    // have to synthesise events or know the element ids.
    // Assigned through `globalThis` rather than as a bare name: the bundle runs
    // in strict mode, where `kolla = ...` is a ReferenceError under Node's
    // module scope even though a browser would make it a global.
    js.Dynamic.global.globalThis.updateDynamic("kolla")(js.Dynamic.literal(
      check = (text: String, profile: String) => runToCompletion(text, profile),
      checkJson = (text: String, profile: String, source: String, platform: String) =>
        jsonLines(text, profile, source, platform),
      profiles = js.Array(KernelProfile.all.map(_.label)*)
    ))

  /** Whether there is a page to draw on.
    *
    * `js.isUndefined(global.document)` is not enough: the reference compiles to
    * a bare `document`, which under Node throws a ReferenceError rather than
    * yielding undefined. `js.typeOf` on a global-scope selection compiles to
    * `typeof document`, which is the one way to ask without evaluating.
    */
  private def hasDocument: Boolean =
    js.typeOf(js.Dynamic.global.document) != "undefined"

  /** The same lines the command line writes with `--json`.
    *
    * `difftest` parses these back into verdicts, so a JS run and a JVM run are
    * compared declaration by declaration rather than by a count.
    */
  private def jsonLines(text: String, profile: String, source: String, platform: String): js.Dynamic =
    parse(text) match
      case Left(message) => js.Dynamic.literal(error = message)
      case Right(items) =>
        // The caller names the platform: the same bundle is the `js` run under
        // Node and the `browser` run under Playwright, and a report that called
        // both `js` would be comparing a platform against itself.
        val label = if platform.isEmpty then "js" else platform
        val out   = ReplayJson.lines(items, profileOf(profile), source, label, () => js.Date.now())
        js.Dynamic.literal(lines = js.Array(out*))

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
    if hasDocument then
      Dom.setText("status", p.status)
      Dom.setText("counts", p.counts)
      Dom.setText("timing", p.timing)
      Dom.setText("rejection", p.firstRejection.getOrElse(""))
      Dom.setHtmlClass("verdict", p.verdictClass)
      val bar = Dom.byId("bar")
      if bar != null then bar.style.width = s"${p.percent}%"
