package kolla.difftest

import scala.collection.mutable

/** A minimal unified diff, enough to store and replay a mutation. */
object Diff:

  /** A unified diff with no context lines.
    *
    * Context would be friendlier to read, but overlapping context windows make
    * hunks ambiguous to apply, and this exists to be replayed rather than read;
    * a mutation's `description` is what describes it to a person. Each hunk
    * covers one maximal run of changes, so hunks can never overlap.
    */
  def unified(a: Vector[String], b: Vector[String]): String =
    val ops = lcsOps(a, b)
    val sb  = new StringBuilder
    var i    = 0
    var aPos = 0
    var bPos = 0
    while i < ops.length do
      if ops(i)._1 == ' ' then
        aPos += 1; bPos += 1; i += 1
      else
        val start  = i
        val aStart = aPos
        val bStart = bPos
        var aLen   = 0
        var bLen   = 0
        while i < ops.length && ops(i)._1 != ' ' do
          if ops(i)._1 == '-' then { aLen += 1; aPos += 1 } else { bLen += 1; bPos += 1 }
          i += 1
        sb ++= s"@@ -${aStart + 1},$aLen +${bStart + 1},$bLen @@\n"
        // Deletions first, then insertions, so the hunk reads as a replacement.
        ops.slice(start, i).filter(_._1 == '-').foreach((_, l) => sb ++= s"-$l\n")
        ops.slice(start, i).filter(_._1 == '+').foreach((_, l) => sb ++= s"+$l\n")
    sb.result()

  /** Longest-common-subsequence edit script, as `(op, line)` pairs. */
  private def lcsOps(a: Vector[String], b: Vector[String]): Vector[(Char, String)] =
    val n = a.length
    val m = b.length
    // The exports differ in a handful of lines, so the full table is affordable
    // only for small inputs; fall back to a line-by-line diff otherwise.
    if n.toLong * m.toLong > 4_000_000L then
      val out = Vector.newBuilder[(Char, String)]
      var i   = 0
      while i < math.max(n, m) do
        val x = if i < n then Some(a(i)) else None
        val y = if i < m then Some(b(i)) else None
        (x, y) match
          case (Some(p), Some(q)) if p == q => out += ((' ', p))
          case (Some(p), Some(q))           => out += (('-', p)); out += (('+', q))
          case (Some(p), None)              => out += (('-', p))
          case (None, Some(q))              => out += (('+', q))
          case (None, None)                 => ()
        i += 1
      out.result()
    else
      val lcs = Array.ofDim[Int](n + 1, m + 1)
      var i = n - 1
      while i >= 0 do
        var j = m - 1
        while j >= 0 do
          lcs(i)(j) =
            if a(i) == b(j) then lcs(i + 1)(j + 1) + 1
            else math.max(lcs(i + 1)(j), lcs(i)(j + 1))
          j -= 1
        i -= 1
      val out = Vector.newBuilder[(Char, String)]
      var x = 0
      var y = 0
      while x < n && y < m do
        if a(x) == b(y) then { out += ((' ', a(x))); x += 1; y += 1 }
        else if lcs(x + 1)(y) >= lcs(x)(y + 1) then { out += (('-', a(x))); x += 1 }
        else { out += (('+', b(y))); y += 1 }
      while x < n do { out += (('-', a(x))); x += 1 }
      while y < m do { out += (('+', b(y))); y += 1 }
      out.result()

  /** Applies a unified diff produced by `unified`. */
  def apply(a: Vector[String], patch: String): Vector[String] =
    val out   = Vector.newBuilder[String]
    var aPos  = 0
    val lines = patch.linesIterator.toVector
    var i     = 0
    while i < lines.length do
      val l = lines(i)
      if l.startsWith("@@") then
        val m = """@@ -(\d+),(\d+) \+(\d+),(\d+) @@""".r.findFirstMatchIn(l)
        val aStart = m.map(_.group(1).toInt - 1).getOrElse(
          throw new IllegalArgumentException(s"bad hunk header: $l")
        )
        while aPos < aStart do { out += a(aPos); aPos += 1 }
        i += 1
        while i < lines.length && !lines(i).startsWith("@@") do
          val h = lines(i)
          h.headOption match
            case Some(' ') => out += h.drop(1); aPos += 1
            case Some('-') => aPos += 1
            case Some('+') => out += h.drop(1)
            case _         => ()
          i += 1
      else i += 1
    while aPos < a.length do { out += a(aPos); aPos += 1 }
    out.result()
