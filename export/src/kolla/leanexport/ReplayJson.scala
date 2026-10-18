package kolla.leanexport

import kolla.kernel.Name

/** The wire format between a kolla frontend and the differential platform.
  *
  * The command line writes it with `--json`, the browser bundle returns it, and
  * `difftest` parses it back into verdicts to compare one platform's run
  * against another's. One definition, so a JVM run and a native run cannot be
  * compared through two slightly different spellings of the same thing.
  *
  * The shape is one object per declaration, then one summary object. Both are
  * single lines, so a reader can take them a line at a time without buffering a
  * whole corpus.
  */
object ReplayJson:

  /** One declaration's verdict. */
  def declaration(name: Name, outcome: ReplayOutcome, nanos: Long): String =
    JsonWriter.obj(
      "name"    -> JsonWriter.str(name.toString),
      "verdict" -> JsonWriter.str(ReplayTally.label(outcome)),
      "detail"  -> ReplayTally.detail(outcome).fold("null")(JsonWriter.str),
      "nanos"   -> JsonWriter.num(nanos),
      "trace"   -> JsonWriter.arr(ReplayTally.trace(outcome).map(JsonWriter.str))
    )

  /** The run as a whole, which a reader uses to check it saw everything. */
  def summary(source: String, profile: String, platform: String, t: ReplayTally, wallNanos: Long): String =
    JsonWriter.obj(
      "summary"   -> JsonWriter.str(source),
      "profile"   -> JsonWriter.str(profile),
      "platform"  -> JsonWriter.str(platform),
      "ok"        -> JsonWriter.bool(t.ok),
      "wallNanos" -> JsonWriter.num(wallNanos),
      "counts" -> JsonWriter.obj(
        "accepted"    -> JsonWriter.num(t.accepted.toLong),
        "rejected"    -> JsonWriter.num(t.rejected.toLong),
        "carriedOver" -> JsonWriter.num(t.carriedOver.toLong),
        "cached"      -> JsonWriter.num(t.cached.toLong),
        "errored"     -> JsonWriter.num(t.failed.toLong),
        "notReached"  -> JsonWriter.num(t.notReached.toLong),
        "total"       -> JsonWriter.num(t.total.toLong)
      )
    )

  /** Replays a whole file and returns its lines: declarations, then a summary.
    *
    * The browser bundle uses this directly; the command line streams the same
    * lines as it goes rather than collecting them.
    */
  def lines(
      items: Vector[ExportItem],
      profile: kolla.kernel.KernelProfile,
      source: String,
      platform: String,
      nowMillis: () => Double
  ): Vector[String] =
    val replay = new Replay(items, profile)
    val out    = Vector.newBuilder[String]
    var tally  = ReplayTally()
    val t0     = nowMillis()
    while replay.hasNext do
      val before = nowMillis()
      val step   = replay.next()
      val took   = ((nowMillis() - before) * 1000000.0).toLong
      tally = tally.add(step)
      step.names.foreach(n => out += declaration(n, step.outcome, took))
    out += summary(source, profile.label, platform, tally, ((nowMillis() - t0) * 1000000.0).toLong)
    out.result()
