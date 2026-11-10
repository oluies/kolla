package kolla.kernel

/** A value in an `Expr.mdata` map, as lean4export prints it:
  * `Lean.DataValue.ofNat 971`, `Lean.DataValue.ofSyntax (...)`.
  *
  * The kernel never reads a value, but it compares them: `is_equal` compares an
  * `mdata` node's map, so two annotations on the same term are different keys
  * to the inference cache and the `is_def_eq` caches. Dropping the map merged
  * them and took kolla off Lean's path (docs/semantics.md K31). So the printed
  * value is kept, normalised by `DataValue.printed` so that two values are
  * equal exactly when Lean's `BEq DataValue` says so.
  */
final case class DataValue(printed: String)

object DataValue:

  private val sourceInfo = "(Lean.SourceInfo."

  /** The printed value with what `BEq DataValue` does not compare left out.
    *
    * `Syntax.structEq` ignores every `SourceInfo`, so each is replaced by `_`.
    * The printer breaks lines by width and a position's digits change the
    * width, so whitespace outside string literals is collapsed to one space.
    */
  def printed(s: String): DataValue =
    val sb    = new StringBuilder(s.length)
    var space = false
    var i     = 0
    def emit(from: Int, until: Int): Unit =
      if space && sb.nonEmpty then sb += ' '
      space = false
      sb.appendAll(s.substring(from, until))
    while i < s.length do
      val c = s.charAt(i)
      if c == '"' then
        val j = endOfString(s, i)
        emit(i, j)
        i = j
      else if c.isWhitespace then
        space = true
        i += 1
      else if s.startsWith(sourceInfo, i) then
        if space && sb.nonEmpty then sb += ' '
        space = false
        sb += '_'
        i = endOfParen(s, i)
      else
        emit(i, i + 1)
        i += 1
    DataValue(sb.result())

  /** The index after the string literal opening at `i`. */
  private def endOfString(s: String, i: Int): Int =
    var j = i + 1
    while j < s.length && s.charAt(j) != '"' do j += (if s.charAt(j) == '\\' then 2 else 1)
    math.min(j + 1, s.length)

  /** The index after the parenthesis closing the one at `i`. */
  private def endOfParen(s: String, i: Int): Int =
    var depth = 0
    var j     = i
    while j < s.length do
      s.charAt(j) match
        case '"' => j = endOfString(s, j) - 1
        case '(' => depth += 1
        case ')' =>
          depth -= 1
          if depth == 0 then return j + 1
        case _ => ()
      j += 1
    s.length

final case class KVMap(entries: List[(Name, DataValue)]):
  def isEmpty: Boolean = entries.isEmpty
  def get(n: Name): Option[DataValue] = entries.collectFirst { case (k, v) if k == n => v }

object KVMap:
  val empty: KVMap = KVMap(Nil)
