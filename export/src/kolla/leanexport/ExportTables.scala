package kolla.leanexport

import kolla.kernel.*
import scala.reflect.ClassTag

/** Index-addressed table with sparse assignment, matching the reference parser's
  * `HashMap Nat _` behaviour while staying array-backed for dense indices.
  *
  * The exporter assigns `idx = map.size` and emits one entry per line, so no
  * index in a well-formed file exceeds the number of lines read so far. `budget`
  * supplies that bound, which keeps a single malformed index from forcing a
  * multi-gigabyte array allocation.
  */
final class Table[A <: AnyRef: ClassTag](val what: String, initial: Seq[A], budget: () => Int):
  private var arr: Array[A] = Array.ofDim[A](math.max(initial.length, 16))
  private var limit: Int    = initial.length

  initial.zipWithIndex.foreach((a, i) => arr(i) = a)

  def size: Int = limit

  def set(i: Int, a: A): Unit =
    if i < 0 then throw ExportException(s"$what index out of range: $i")
    val cap = budget()
    if i > cap then
      throw ExportException(s"$what index out of range: $i (at most $cap after the lines read so far)")
    if i >= arr.length then
      var n = arr.length
      while n <= i do n = math.max(n * 2, i + 1)
      val next = Array.ofDim[A](n)
      System.arraycopy(arr, 0, next, 0, limit)
      arr = next
    arr(i) = a
    if i >= limit then limit = i + 1

  def get(i: Int): A =
    if i < 0 || i >= limit || arr(i) == null then throw ExportException(s"$what not found: $i")
    arr(i)

  def toVector: Vector[A] = Vector.tabulate(limit)(i => arr(i))

  /** PROTOTYPE: forgets entry `i`, so a later reference to it is an error. */
  def release(i: Int): Unit = if i >= 0 && i < arr.length then arr(i) = null.asInstanceOf[A]

final class ExportTables(maxIndex: Int = 1 << 28):
  private var lines = 0

  /** Raises the index bound by one; the reader calls this once per input line. */
  def observeLine(): Unit = if lines < maxIndex then lines += 1

  private def budget(): Int = lines

  val names: Table[Name]            = Table("name", Seq(Name.anonymous), budget)
  val levels: Table[Level]          = Table("level", Seq(Level.zero), budget)
  val exprs: Table[Expr]            = Table("expr", Seq.empty, budget)
  val recRules: Table[RecursorRule] = Table("recursor rule", Seq.empty, budget)

  def name(i: Int): Name      = names.get(i)
  def level(i: Int): Level    = levels.get(i)
  def expr(i: Int): Expr      = exprs.get(i)
  def rule(i: Int): RecursorRule = recRules.get(i)
