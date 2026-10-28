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

  /** One reduction, for `--eval --json`.
    *
    * Here rather than in `cli` for the reason the rest of this file is: the
    * wire format is one implementation, so a reader does not have to know
    * which frontend produced it. See docs/semantics.md F1.
    */
  def evaluation(term: String, value: String, tpe: String, profile: String): String =
    JsonWriter.obj(
      "eval"    -> JsonWriter.str(term),
      "value"   -> JsonWriter.str(value),
      "type"    -> JsonWriter.str(tpe),
      "profile" -> JsonWriter.str(profile)
    )

  /** One declaration's axiom closure, for `--axioms --json`. */
  def axioms(
      declaration: String,
      axioms: Vector[String],
      hasSorry: Boolean,
      unusual: Vector[String],
      profile: String,
      /** The set the caller named, and what fell outside it. Absent unless one
        * was named, since `unusual` is a different question: it reports what
        * is outside Lean's three, which is a judgement rather than a gate.
        */
      permitted: Option[Vector[String]] = None,
      notPermitted: Option[Vector[String]] = None
  ): String =
    val gate =
      permitted.toSeq.map(ps => "permitted" -> JsonWriter.arr(ps.map(JsonWriter.str))) ++
        notPermitted.toSeq.map(ns => "notPermitted" -> JsonWriter.arr(ns.map(JsonWriter.str)))
    JsonWriter.obj(
      Seq(
        "declaration" -> JsonWriter.str(declaration),
        "axioms"      -> JsonWriter.arr(axioms.map(JsonWriter.str)),
        "sorry"       -> JsonWriter.bool(hasSorry),
        "unusual"     -> JsonWriter.arr(unusual.map(JsonWriter.str)),
        "profile"     -> JsonWriter.str(profile)
      ) ++ gate*
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
