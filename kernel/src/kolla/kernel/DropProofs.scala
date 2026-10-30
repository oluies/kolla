package kolla.kernel

/** PROTOTYPE: drop a theorem's value once it has been checked.
  *
  * `-Dkolla.dropProofs=drop` drops every theorem value except those named, one
  * per line, in the file given by `-Dkolla.keepProofs`. The kernel may unfold a
  * theorem like a definition (`isDelta` accepts any constant with a value), so
  * the placeholder is not silent: unfolding one throws.
  *
  * `-Dkolla.dropProofs=count` drops nothing and prints, at exit, every theorem
  * the kernel unfolded and how often.
  */
object DropProofs:
  private val mode: String = Option(System.getProperty("kolla.dropProofs")).getOrElse("")

  val enabled: Boolean  = mode == "drop"
  val counting: Boolean = mode == "count"

  private val keep: Set[Name] =
    Option(System.getProperty("kolla.keepProofs")).fold(Set.empty[Name]) { p =>
      val src = scala.io.Source.fromFile(p)
      try src.getLines().map(_.trim).filter(_.nonEmpty).map(Name.parse).toSet
      finally src.close()
    }

  def drops(n: Name): Boolean = enabled && !keep.contains(n)

  val placeholder: Expr = Expr.Const(Name.parse("_kolla.droppedProof"), Nil)

  def isDropped(info: ConstantInfo): Boolean = info match
    case ConstantInfo.ThmInfo(v) => v.value eq placeholder
    case _                       => false

  private val unfolds = scala.collection.mutable.HashMap.empty[Name, Long]

  def noteUnfold(info: ConstantInfo): Unit =
    if counting && info.isTheorem then
      unfolds.synchronized(unfolds.update(info.name, unfolds.getOrElse(info.name, 0L) + 1L))

  if counting then
    Runtime.getRuntime.addShutdownHook(new Thread(() =>
      val all = unfolds.synchronized(unfolds.toVector).sortBy(-_._2)
      System.err.println(s"theorems unfolded: ${all.size} distinct, ${all.map(_._2).sum} times")
      all.foreach((n, c) => System.err.println(s"  unfolded $c $n"))
    ))
