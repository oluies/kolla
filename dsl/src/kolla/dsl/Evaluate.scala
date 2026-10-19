package kolla.dsl

import kolla.kernel.*

/** Reduces a closed term with the kernel and reports its type.
  *
  * This is `#eval` for the part of `#eval` the kernel can do: beta, delta,
  * iota, projection, `let`, and the `Nat` and `String` literal extensions. It
  * is reduction, not execution. A Lean program in the sense of
  * `main : IO Unit` cannot be run this way and never will be here: `IO`
  * bottoms out in `@[extern]` primitives that the kernel sees as constants with
  * no definition to unfold, and running them is the business of Lean's runtime
  * and compiler, neither of which kolla has. See docs/semantics.md D13.
  */
object Evaluate:

  /** What a term reduced to, and the type it was checked at. */
  final case class Result(tpe: Expr, value: Expr, reducedArgs: Int)

  /** How deep into an application spine to keep reducing.
    *
    * Reduction of arguments recurses, and a term's spine can nest, so this
    * bounds the stack rather than the work. The kernel's own `maxSteps`
    * bounds the work.
    */
  val maxDepth: Int = 64

  /** Type-checks `term` against `env` and reduces it.
    *
    * `Left` is the kernel's own reason, so an ill-typed term reads the same
    * way it would in a rejected declaration.
    */
  def apply(env: Environment, profile: KernelProfile, term: Expr): Either[String, Result] =
    val tc = new TypeChecker(env, profile)
    try
      val tpe = tc.check(term)
      var n    = 0
      def count(): Unit = n += 1
      val value = normalise(tc, term, maxDepth, count)
      Right(Result(tpe, value, n))
    catch
      case e: KernelException => Left(e.reason)

  /** Head-reduces, then reduces each argument of the resulting spine.
    *
    * Not under binders. A lambda's body has loose bound variables and the
    * kernel reduces closed terms, so `fun x => Nat.add 2 2` is returned as it
    * stands rather than with its body reduced. That is a real limit and the
    * reason `Result.value` can still contain redexes under a `fun`.
    */
  def normalise(tc: TypeChecker, e: Expr, depth: Int, onArg: () => Unit): Expr =
    val head = tc.whnf(e)
    if depth <= 0 then head
    else
      val (fn, args) = Expr.getAppFnArgs(head)
      if args.isEmpty then head
      else
        val reduced = args.map { a =>
          onArg()
          normalise(tc, a, depth - 1, onArg)
        }
        Expr.mkAppN(fn, reduced)
