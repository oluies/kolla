package kolla.leanexport

import fs2.{Chunk, Pipe, Stream}
import scala.collection.mutable

/** Streaming reader for the lean4export formats.
  *
  * The NDJSON formats announce themselves with a `meta` header object. The two
  * text formats have no header, so their version is resolved from the first
  * declaration command that distinguishes them; declaration lines seen before
  * that are buffered. Index-prefixed lines are identical in both text formats
  * (apart from `#RR`, which exists only in v2) and are applied immediately.
  */
final class ExportReader(forced: Option[ExportFormat] = None, retainItems: Boolean = true):
  import ExportFormat.*
  import ExportReader.Kind

  private val tables = new ExportTables

  private val items   = mutable.ArrayBuffer.empty[ExportItem]
  private var drained = 0
  private var sink: ExportItem => Unit = items += _

  private val text   = new TextDialect(tables, i => sink(i))
  private val ndjson = new NdjsonDialect(tables, i => sink(i))

  private var kind: Option[Kind] = forced.map(f => if f.isText then Kind.Text else Kind.Json)
  private var textVersion: Option[ExportFormat] = forced.filter(_.isText)
  private var jsonVersion: Option[String] = forced.collect { case Ndjson(v) => v }
  private var meta: Option[ExportMeta] = None

  private val pending = mutable.ArrayBuffer.empty[(Int, String)]
  private var lineNo  = 0
  private var finished = false

  def format: ExportFormat = kind match
    case Some(Kind.Json) => Ndjson(jsonVersion.getOrElse(""))
    case Some(Kind.Text) => textVersion.getOrElse(TextV2)
    case None            => forced.getOrElse(TextV2)

  def exportMeta: Option[ExportMeta] = meta

  def feed(rawLine: String): Unit =
    lineNo += 1
    val line = trimLine(rawLine)
    if line.isEmpty then return
    tables.observeLine()
    try
      kind match
        case None =>
          val k = if line.charAt(0) == '{' then Kind.Json else Kind.Text
          kind = Some(k)
          dispatch(k, line)
        case Some(k) => dispatch(k, line)
    catch case e: ExportException => throw e.atLine(lineNo)

  def feedAll(lines: IterableOnce[String]): Unit = lines.iterator.foreach(feed)

  /** New items since the previous drain. */
  def drain(): Vector[ExportItem] =
    val out = items.view.slice(drained, items.length).toVector
    if retainItems then drained = items.length
    else { items.clear(); drained = 0 }
    out

  def finish(): Unit =
    if finished then return
    finished = true
    if kind.contains(Kind.Text) && textVersion.isEmpty && pending.nonEmpty then resolveAmbiguous()
    else flushPending(textVersion.getOrElse(TextV2))

  def result(): ExportEnv =
    finish()
    ExportEnv(format, meta, items.toVector)

  // ------------------------------------------------------------------ private

  private def trimLine(s: String): String =
    var end = s.length
    while end > 0 && (s.charAt(end - 1) == '\n' || s.charAt(end - 1) == '\r') do end -= 1
    var start = 0
    while start < end && s.charAt(start) == ' ' do start += 1
    if start == 0 && end == s.length then s else s.substring(start, end)

  private def dispatch(k: Kind, line: String): Unit = k match
    case Kind.Json => feedJson(line)
    case Kind.Text => feedText(line)

  private def feedJson(line: String): Unit =
    val root = Json.parse(line).asObj("export item")
    ndjson.line(root) match
      case Some(m) =>
        meta = Some(m)
        if jsonVersion.isEmpty then
          jsonVersion = Some(if m.formatVersion.nonEmpty then m.formatVersion else m.exporterVersion)
      case None => ()

  private def feedText(line: String): Unit =
    val tk    = new Tokens(line)
    val first = tk.next("index or command")
    if first.startsWith("#") then
      decisive(first, line) match
        case Some(v) =>
          setTextVersion(v)
          applyDeclaration(v, first, tk)
        case None =>
          textVersion match
            case Some(v) => applyDeclaration(v, first, tk)
            case None    => pending += ((lineNo, line))
    else
      val idx = first.toIntOption match
        case Some(i) if i >= 0 => i
        case _                 => throw ExportException(s"expected an index or a '#' command, got '$first'")
      val cmd    = tk.next("command")
      val v2Only = text.primitive(idx, cmd, tk)
      if v2Only then setTextVersion(TextV2)

  private def decisive(cmd: String, line: String): Option[ExportFormat] = cmd match
    case "#THM" | "#OPAQ" | "#CTOR" | "#REC" => Some(TextV2)
    case "#QUOT" =>
      val t = new Tokens(line)
      t.next("command")
      Some(if t.hasNext then TextV2 else TextV1)
    case "#DEF" =>
      val t = new Tokens(line)
      t.next("command"); t.next("name"); t.next("type"); t.next("value")
      t.peek match
        case Some("O") | Some("A") | Some("R") => Some(TextV2)
        case _                                 => Some(TextV1)
    case _ => None

  private def applyDeclaration(v: ExportFormat, cmd: String, tk: Tokens): Unit =
    if !text.sharedDeclaration(cmd, tk) then
      v match
        case TextV1 => text.declarationV1(cmd, tk)
        case _      => text.declarationV2(cmd, tk)

  private def setTextVersion(v: ExportFormat): Unit =
    textVersion match
      case Some(existing) =>
        if existing != v then
          throw ExportException(s"mixed text export formats: saw both $existing and $v")
      case None =>
        textVersion = Some(v)
        flushPending(v)

  private def flushPending(v: ExportFormat): Unit =
    if pending.isEmpty then return
    val buffered = pending.toVector
    pending.clear()
    buffered.foreach { (n, line) => replay(v, n, line) }

  private def replay(v: ExportFormat, n: Int, line: String): Unit =
    try
      val tk    = new Tokens(line)
      val first = tk.next("command")
      applyDeclaration(v, first, tk)
    catch case e: ExportException => throw e.atLine(n)

  /** Only `#AX` and `#IND` are version-ambiguous, and neither writes to the index
    * tables, so a failed attempt can be discarded.
    */
  private def resolveAmbiguous(): Unit =
    val buffered = pending.toVector
    pending.clear()
    val trial = Vector.newBuilder[ExportItem]
    sink = trial += _
    val v2 =
      try
        buffered.foreach { (n, line) => replay(TextV2, n, line) }
        true
      catch case _: ExportException => false
    if v2 then
      textVersion = Some(TextV2)
      sink = items += _
      items ++= trial.result()
    else
      val retry = Vector.newBuilder[ExportItem]
      sink = retry += _
      try buffered.foreach { (n, line) => replay(TextV1, n, line) }
      finally sink = items += _
      textVersion = Some(TextV1)
      items ++= retry.result()

object ExportReader:

  private enum Kind:
    case Text, Json

  def fromLines(lines: IterableOnce[String], format: Option[ExportFormat] = None): ExportEnv =
    val r = new ExportReader(format)
    r.feedAll(lines)
    r.result()

  def fromString(contents: String, format: Option[ExportFormat] = None): ExportEnv =
    fromLines(contents.linesIterator, format)

  /** Emits declarations as they are completed. Items are not retained, so memory
    * use is bounded by the index tables.
    */
  def pipe[F[_]](format: Option[ExportFormat] = None): Pipe[F, String, ExportItem] =
    in =>
      Stream.suspend {
        val r = new ExportReader(format, retainItems = false)
        in.mapChunks { chunk =>
          chunk.foreach(r.feed)
          Chunk.from(r.drain())
        } ++ Stream.suspend {
          r.finish()
          Stream.chunk(Chunk.from(r.drain()))
        }
      }
