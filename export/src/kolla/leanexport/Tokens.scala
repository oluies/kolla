package kolla.leanexport

/** Cursor over a space-separated export line. */
final class Tokens(private val line: String):
  private var pos: Int = 0

  private def skipSpaces(): Unit =
    while pos < line.length && line.charAt(pos) == ' ' do pos += 1

  def hasNext: Boolean =
    skipSpaces()
    pos < line.length

  def next(what: String): String =
    skipSpaces()
    if pos >= line.length then throw ExportException(s"missing $what")
    val start = pos
    while pos < line.length && line.charAt(pos) != ' ' do pos += 1
    line.substring(start, pos)

  def peek: Option[String] =
    val save = pos
    val r = if hasNext then Some(next("token")) else None
    pos = save
    r

  /** Remainder of the line verbatim, after a single separating space. */
  def rest(what: String): String =
    if pos < line.length && line.charAt(pos) == ' ' then pos += 1
    if pos > line.length then throw ExportException(s"missing $what")
    val r = line.substring(pos)
    pos = line.length
    r

  def int(what: String): Int =
    val t = next(what)
    t.toIntOption match
      case Some(i) if i >= 0 => i
      case _                 => throw ExportException(s"$what: expected a non-negative integer, got '$t'")

  def bigInt(what: String): BigInt =
    val t = next(what)
    try BigInt(t)
    catch case _: NumberFormatException => throw ExportException(s"$what: expected an integer, got '$t'")

  def remaining(what: String): List[Int] =
    val b = List.newBuilder[Int]
    while hasNext do b += int(what)
    b.result()

  def takeInts(n: Int, what: String): List[Int] =
    val b = List.newBuilder[Int]
    var i = 0
    while i < n do
      b += int(what)
      i += 1
    b.result()

  def end(what: String): Unit =
    if hasNext then throw ExportException(s"$what: unexpected trailing tokens '${line.substring(pos)}'")
