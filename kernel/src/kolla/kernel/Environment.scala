package kolla.kernel

final class Environment private (
    private val constants: Map[Name, ConstantInfo],
    private val order: Vector[Name],
    val quotInitialized: Boolean
):

  def find(n: Name): Option[ConstantInfo] = constants.get(n)

  def get(n: Name): ConstantInfo =
    constants.get(n) match
      case Some(i) => i
      case None    => throw KernelException.unknownConstant(n)

  def contains(n: Name): Boolean = constants.contains(n)

  def size: Int = order.length

  def names: Vector[Name] = order

  /** Constants in the order they were added. */
  def declarations: Vector[ConstantInfo] = order.map(constants)

  def addCore(info: ConstantInfo): Environment =
    checkName(info.name)
    checkDuplicatedUnivParams(info.levelParams)
    new Environment(constants.updated(info.name, info), order :+ info.name, quotInitialized)

  def addCoreAll(infos: Iterable[ConstantInfo]): Environment =
    infos.foldLeft(this)((e, i) => e.addCore(i))

  def markQuotInitialized: Environment =
    new Environment(constants, order, true)

  def checkName(n: Name): Unit =
    if constants.contains(n) then throw KernelException.alreadyDeclared(n)

  def checkDuplicatedUnivParams(ls: List[Name]): Unit =
    var seen = List.empty[Name]
    var rest = ls
    while rest.nonEmpty do
      val p = rest.head
      if seen.contains(p) then
        throw KernelException(
          ExceptionKind.DuplicateUniverseParam,
          s"duplicate universe level parameter '${p}'"
        )
      seen = p :: seen
      rest = rest.tail

object Environment:
  val empty: Environment = new Environment(Map.empty, Vector.empty, false)
