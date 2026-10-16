package kolla.leanexport

import kolla.kernel.*

/** One top-level entry of an export file.
  *
  * The text v1 format carries kernel *inputs* for inductives and the quotient
  * package (the recursors and the constructor metadata are derived by the kernel),
  * while the text v2 and NDJSON formats carry the derived environment entries.
  */
enum ExportItem:
  case Decl(decl: Declaration)
  case Info(info: ConstantInfo)
  /** Text v1 `#DEF`, which carries no reducibility hint; the kernel computes the
    * definitional height when adding the declaration.
    */
  case DefnWithoutHints(name: Name, levelParams: List[Name], tpe: Expr, value: Expr)

  def names: List[Name] = this match
    case Decl(d)                       => d.declNames
    case Info(i)                       => List(i.name)
    case DefnWithoutHints(n, _, _, _)  => List(n)

final case class ExportMeta(
    exporterName: String,
    exporterVersion: String,
    formatVersion: String,
    leanVersion: String,
    leanGithash: String
)

final case class ExportEnv(
    format: ExportFormat,
    meta: Option[ExportMeta],
    items: Vector[ExportItem]
):
  def infos: Vector[ConstantInfo] = items.collect { case ExportItem.Info(i) => i }

  def declarations: Vector[Declaration] = items.collect { case ExportItem.Decl(d) => d }

  /** Folds the `Info` items into an `Environment`, preserving file order. `Decl`
    * items are kernel inputs and are not added here.
    */
  def infoEnvironment: Environment =
    infos.foldLeft(Environment.empty)((e, i) => e.addCore(i))

  def size: Int = items.length
