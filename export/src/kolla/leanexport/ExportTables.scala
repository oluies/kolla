package kolla.leanexport

import kolla.kernel.*
import scala.reflect.ClassTag

/** Index-addressed table with sparse assignment, matching the reference parser's
  * `HashMap Nat _` behaviour while staying array-backed for dense indices.
  */
final class Table[A <: AnyRef: ClassTag](val what: String, initial: Seq[A], maxIndex: Int):
  private var arr: Array[A] = Array.ofDim[A](math.max(initial.length, 16))
  private var limit: Int    = initial.length

  initial.zipWithIndex.foreach((a, i) => arr(i) = a)

  def size: Int = limit

  def set(i: Int, a: A): Unit =
    if i < 0 || i > maxIndex then throw ExportException(s"$what index out of range: $i")
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

final class ExportTables(maxIndex: Int = 1 << 28):
  val names: Table[Name]           = Table("name", Seq(Name.anonymous), maxIndex)
  val levels: Table[Level]         = Table("level", Seq(Level.zero), maxIndex)
  val exprs: Table[Expr]           = Table("expr", Seq.empty, maxIndex)
  val recRules: Table[RecursorRule] = Table("recursor rule", Seq.empty, maxIndex)

  def name(i: Int): Name      = names.get(i)
  def level(i: Int): Level    = levels.get(i)
  def expr(i: Int): Expr      = exprs.get(i)
  def rule(i: Int): RecursorRule = recRules.get(i)
