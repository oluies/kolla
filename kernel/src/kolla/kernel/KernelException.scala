package kolla.kernel

enum ExceptionKind:
  case UnknownConstant
  case AlreadyDeclared
  case DefinitionTypeMismatch
  case DeclarationHasMetavars
  case DeclarationHasFreeVars
  case TheoremTypeIsNotProp
  case FunctionExpected
  case TypeExpected
  case TypeMismatch
  case ExprTypeMismatch
  case AppTypeMismatch
  case InvalidProj
  case InvalidDeclaration
  case DuplicateUniverseParam
  case InvalidName
  case DeepRecursion
  case Other

final class KernelException(
    val kind: ExceptionKind,
    val declName: Option[Name],
    val detail: String,
    val trace: List[String]
) extends RuntimeException(KernelException.render(kind, declName, detail, trace)):

  def withDeclName(n: Name): KernelException =
    new KernelException(kind, Some(n), detail, trace)

  def withTrace(t: List[String]): KernelException =
    new KernelException(kind, declName, detail, t)

object KernelException:

  private[kernel] def render(
      kind: ExceptionKind,
      declName: Option[Name],
      detail: String,
      trace: List[String]
  ): String =
    val sb = new StringBuilder
    sb ++= kind.toString
    declName.foreach(n => sb ++= " in '" ++= n.toString ++= "'")
    if detail.nonEmpty then sb ++= ": " ++= detail
    if trace.nonEmpty then
      sb ++= "\ndefeq trace:"
      trace.foreach(t => sb ++= "\n  " ++= t)
    sb.result()

  def apply(kind: ExceptionKind, detail: String): KernelException =
    new KernelException(kind, None, detail, Nil)

  def apply(kind: ExceptionKind, declName: Name, detail: String): KernelException =
    new KernelException(kind, Some(declName), detail, Nil)

  def unknownConstant(n: Name): KernelException =
    new KernelException(ExceptionKind.UnknownConstant, None, n.toString, Nil)

  def alreadyDeclared(n: Name): KernelException =
    new KernelException(ExceptionKind.AlreadyDeclared, None, n.toString, Nil)

  object DeepRecursion:
    def apply(detail: String): KernelException =
      new KernelException(ExceptionKind.DeepRecursion, None, detail, Nil)
