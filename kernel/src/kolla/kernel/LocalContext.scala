package kolla.kernel

import scala.collection.immutable.ArraySeq

/** A local declaration: a free variable with a type, and a value when it came
  * from a `let`. Mirrors `lean::local_decl`.
  */
final case class LocalDecl(
    idx: Int,
    id: Name,
    userName: Name,
    tpe: Expr,
    value: Option[Expr],
    binderInfo: BinderInfo
):
  def ref: Expr = Expr.FVar(id)

/** `lean::local_ctx`. Free variable identifiers are globally unique within one
  * checker run, so a declaration's type never has to be looked up by position.
  */
final class LocalContext private (
    private val decls: Map[Name, LocalDecl],
    val size: Int
):

  def isEmpty: Boolean = decls.isEmpty

  def find(id: Name): Option[LocalDecl] = decls.get(id)

  def find(e: Expr): Option[LocalDecl] = e match
    case f: Expr.FVar => decls.get(f.id)
    case _            => None

  def get(id: Name): LocalDecl =
    decls.getOrElse(id, throw KernelException(ExceptionKind.Other, s"unknown free variable '$id'"))

  def isLetFVar(e: Expr): Boolean = find(e).exists(_.value.isDefined)

  def mkLocalDecl(ngen: NameGenerator, userName: Name, tpe: Expr, binderInfo: BinderInfo): (LocalContext, Expr) =
    val id = ngen.next()
    val d  = LocalDecl(size, id, userName, tpe, None, binderInfo)
    (new LocalContext(decls.updated(id, d), size + 1), d.ref)

  def mkLetDecl(ngen: NameGenerator, userName: Name, tpe: Expr, value: Expr): (LocalContext, Expr) =
    val id = ngen.next()
    val d  = LocalDecl(size, id, userName, tpe, Some(value), BinderInfo.Default)
    (new LocalContext(decls.updated(id, d), size + 1), d.ref)

  /** `lean::local_ctx::mk_binding`: abstracts `fvars` out of `e`, rebuilding the
    * binders they stand for. `removeDeadLet` drops a `let` whose variable does
    * not occur, as `mk_pi(fvars, r, true)` does for `infer_let`.
    */
  private def mkBinding(isLambda: Boolean, fvars: IndexedSeq[Expr], e: Expr, removeDeadLet: Boolean): Expr =
    var r = ExprOps.abstract_(e, fvars)
    var i = fvars.length
    while i > 0 do
      i -= 1
      val prefix = fvars.slice(0, i)
      val d      = get(fvars(i).asInstanceOf[Expr.FVar].id)
      d.value match
        case Some(v) =>
          if !removeDeadLet || ExprOps.hasLooseBVar(r, 0) then
            r = Expr.LetE(d.userName, ExprOps.abstract_(d.tpe, prefix), ExprOps.abstract_(v, prefix), r, false)
          else r = ExprOps.lowerLooseBVars(r, 1, 1)
        case None =>
          val t = ExprOps.abstract_(d.tpe, prefix)
          r = if isLambda then Expr.Lam(d.userName, t, r, d.binderInfo)
              else Expr.ForallE(d.userName, t, r, d.binderInfo)
    r

  def mkLambda(fvars: IndexedSeq[Expr], e: Expr, removeDeadLet: Boolean = false): Expr =
    mkBinding(true, fvars, e, removeDeadLet)

  def mkPi(fvars: IndexedSeq[Expr], e: Expr, removeDeadLet: Boolean = false): Expr =
    mkBinding(false, fvars, e, removeDeadLet)

object LocalContext:
  val empty: LocalContext = new LocalContext(Map.empty, 0)

/** `lean::name_generator`: fresh free variable identifiers. */
final class NameGenerator(prefix: Name = NameGenerator.kernelFresh):
  private var counter: Int = 0

  def next(): Name =
    val n = prefix.num(counter)
    counter += 1
    n

  def currentCount: Int = counter

object NameGenerator:
  val kernelFresh: Name = Name.mkSimple("_kernel_fresh")
