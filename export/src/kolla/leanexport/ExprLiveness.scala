package kolla.leanexport

/** PROTOTYPE: the last line of an NDJSON export that mentions each expression.
  *
  * A first pass over the file. After the reader has handled line `n`, every
  * expression whose last mention is at or before `n` can leave the index table:
  * whatever still needs it holds the object itself. Line numbers count raw
  * lines from 1, as `ExportReader.feed` does.
  */
final class ExprLiveness private (lastUse: Array[Int], order: Array[Int]):
  private var next = 0

  /** Calls `release` for every expression whose last mention is at or before `line`. */
  def advance(line: Int)(release: Int => Unit): Unit =
    while next < order.length && lastUse(order(next)) <= line do
      release(order(next))
      next += 1

object ExprLiveness:
  import Json.*

  private val exprFields = List(
    "app" -> List("fn", "arg"),
    "lam" -> List("type", "body"),
    "forallE" -> List("type", "body"),
    "letE" -> List("type", "value", "body"),
    "proj" -> List("struct"),
    "mdata" -> List("expr")
  )

  def of(lines: Iterator[String]): ExprLiveness =
    var last = new Array[Int](1 << 20)
    var count = 0
    def mention(i: Int, line: Int): Unit =
      if i >= last.length then
        var n = last.length
        while n <= i do n *= 2
        last = java.util.Arrays.copyOf(last, n)
      if line > last(i) then last(i) = line
      if i >= count then count = i + 1
    def ref(j: Json, line: Int): Unit = j match
      case Num(v) => mention(v.toInt, line)
      case _      => ()
    def group(j: Json): Vector[Map[String, Json]] = j match
      case Arr(vs) => vs.collect { case Obj(f) => f }
      case Obj(f)  => Vector(f)
      case _       => Vector.empty

    var n = 0
    lines.foreach { raw =>
      n += 1
      val s = raw.trim
      if s.nonEmpty && s.charAt(0) == '{' then
        val root = Json.parse(s) match
          case Obj(f) => f
          case _      => Map.empty[String, Json]
        root.get("ie") match
          case Some(Num(i)) =>
            mention(i.toInt, n)
            exprFields.find((k, _) => root.contains(k)).foreach { (k, fs) =>
              root(k) match
                case Obj(f) => fs.foreach(x => f.get(x).foreach(ref(_, n)))
                case _      => ()
            }
          case _ if root.contains("in") || root.contains("il") || root.contains("meta") => ()
          case _ =>
            for k <- List("axiom", "def", "thm", "opaque", "quot"); j <- root.get(k); d <- group(j) do
              d.get("type").foreach(ref(_, n)); d.get("value").foreach(ref(_, n))
            root.get("inductive").foreach {
              case Obj(ind) =>
                for (a, b) <- List("types" -> "inductiveVals", "ctors" -> "constructorVals", "recs" -> "recursorVals")
                    j <- ind.get(a).orElse(ind.get(b)); d <- group(j) do
                  d.get("type").foreach(ref(_, n))
                  d.get("rules").foreach(rs => group(rs).foreach(r => r.get("rhs").foreach(ref(_, n))))
              case _ => ()
            }
    }

    // Counting sort of the indices by last mention.
    val byLine = new Array[Int](n + 2)
    var i = 0
    while i < count do { byLine(last(i)) += 1; i += 1 }
    var acc = 0
    var l = 0
    while l < byLine.length do { val c = byLine(l); byLine(l) = acc; acc += c; l += 1 }
    val order = new Array[Int](count)
    i = 0
    while i < count do { order(byLine(last(i))) = i; byLine(last(i)) += 1; i += 1 }
    new ExprLiveness(java.util.Arrays.copyOf(last, count), order)
