package kolla.dsl

import kolla.kernel.*
import java.util.concurrent.atomic.AtomicLong

/** A builder API for kernel terms.
  *
  * Binders are written as Scala functions, so a bound variable is an ordinary
  * Scala value and the de Bruijn index is computed on the way out. The variable
  * is a free variable with a fresh identifier while the body is built and is
  * abstracted immediately afterwards, which is the same construction
  * `local_ctx::mk_binding` performs.
  */
object LeanDsl:

  private val counter = new AtomicLong(0L)

  /** A fresh free variable, unique among the binders currently open. */
  private def freshVar(): Expr =
    Expr.FVar(LeanDsl.dslFresh.num(BigInt(counter.getAndIncrement())))

  val dslFresh: Name = Name.mkSimple("_dsl_fresh")

  // ------------------------------------------------------------------- names

  def name(s: String): Name = Name.parse(s)

  given Conversion[String, Name] = Name.parse(_)

  // ------------------------------------------------------------------ levels

  val zero: Level = Level.zero
  val one: Level  = Level.one

  def param(s: String): Level = Level.Param(Name.parse(s))
  def lvl(n: Int): Level      = Level.ofNat(n)
  def succ(l: Level): Level   = Level.Succ(l)
  def max(a: Level, b: Level): Level  = Level.max(a, b)
  def imax(a: Level, b: Level): Level = Level.imax(a, b)

  // ------------------------------------------------------------------- sorts

  def Sort(l: Level): Expr = Expr.Sort(l)
  val Prop: Expr           = Expr.Sort(Level.zero)
  def Type(n: Int): Expr   = Expr.Sort(Level.ofNat(n + 1))
  val Type0: Expr          = Type(0)

  // --------------------------------------------------------------- constants

  def Const(n: Name): Expr                  = Expr.Const(n, Nil)
  def Const(n: Name, ls: Level*): Expr      = Expr.Const(n, ls.toList)
  def Const(n: String): Expr                = Expr.Const(Name.parse(n), Nil)

  // ------------------------------------------------------------ applications

  def App(f: Expr, args: Expr*): Expr = Expr.mkAppN(f, args)

  // ------------------------------------------------------------------ binders

  /* Each binder abstracts its own variable out of the body, so building `k`
     nested binders costs O(k^2). That is intended for hand-written terms; a
     machine-generated telescope should use `LocalContext.mkPi`/`mkLambda`,
     which abstract every variable in one pass. */

  /** `fun (n : domain) => body(n)`. */
  def Lam(n: Name, domain: Expr, info: BinderInfo = BinderInfo.Default)(body: Expr => Expr): Expr =
    val v = freshVar()
    Expr.Lam(n, domain, ExprOps.abstract1(body(v), v), info)

  /** `(n : domain) -> body(n)`. */
  def Pi(n: Name, domain: Expr, info: BinderInfo = BinderInfo.Default)(body: Expr => Expr): Expr =
    val v = freshVar()
    Expr.ForallE(n, domain, ExprOps.abstract1(body(v), v), info)

  /** `let n : tpe := value; body(n)`. */
  def Let(n: Name, tpe: Expr, value: Expr, nondep: Boolean = false)(body: Expr => Expr): Expr =
    val v = freshVar()
    Expr.LetE(n, tpe, value, ExprOps.abstract1(body(v), v), nondep)

  /** A non-dependent arrow. */
  def arrow(domain: Expr, codomain: Expr): Expr =
    Expr.ForallE(Name.mkSimple("a"), domain, codomain, BinderInfo.Default)

  // ---------------------------------------------------------------- literals

  def natLit(v: BigInt): Expr  = Expr.natLit(v)
  def strLit(s: String): Expr  = Expr.strLit(s)
  def proj(struct: Name, idx: Int, e: Expr): Expr = Expr.Proj(struct, idx, e)
  def bvar(i: Int): Expr       = Expr.BVar(i)

  extension (f: Expr)
    /** Application, left associative. */
    def apply(args: Expr*): Expr = Expr.mkAppN(f, args)

  extension (domain: Expr)
    /** A non-dependent arrow. The name ends in `:` so that it is right
      * associative as in Lean; Scala binds the extension receiver to the left
      * operand, so `domain` is the left-hand side.
      */
    infix def ->:(codomain: Expr): Expr = arrow(domain, codomain)

  extension (s: String)
    def c: Expr  = Expr.Const(Name.parse(s), Nil)
    def n: Name  = Name.parse(s)
    def u: Level = Level.Param(Name.parse(s))
