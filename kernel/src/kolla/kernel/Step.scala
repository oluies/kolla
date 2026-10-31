package kolla.kernel

import cats.Eval

/** One step of the type checker's recursion: `Eval`'s stack safety without its
  * cost where the stack is shallow.
  *
  * `defer` and `flatMap` run their argument at once while the owning type
  * checker's `Depth` is under `Step.Limit`, and suspend it in an `Eval` from
  * there down, so a deep term is trampolined exactly as before. On the direct
  * path no `Eval` node is allocated and no trampoline runs; the closures passed
  * to `flatMap` and `map` remain, as they did with `Eval`. Evaluation order is the
  * order the code is written in, as it was with `Eval`. The depth counter only
  * ever overstates how deep the stack is: a `.value` reached while deep starts
  * from a high count and suspends at once. See docs/semantics.md K24.
  */
private[kernel] sealed abstract class Step[+A]:
  def value: A
  private[kernel] def toEval: Eval[A]

private[kernel] object Step:

  /** How many nested direct steps a type checker takes before suspending. The
    * type checker spends several frames per step, and Scala.js has the
    * smallest stacks of the three platforms.
    */
  final val Limit = 128

  /** Nesting of direct steps, one per type checker, which is single-threaded. */
  final class Depth:
    var current: Int = 0

  final class Done[+A](val a: A) extends Step[A]:
    def value: A                        = a
    private[kernel] def toEval: Eval[A] = Eval.now(a)

  final class Later[+A](val ev: Eval[A]) extends Step[A]:
    def value: A                        = ev.value
    private[kernel] def toEval: Eval[A] = ev

  def now[A](a: A): Step[A] = new Done(a)

  val True: Step[Boolean] = new Done(true)
  val False: Step[Boolean] = new Done(false)
  val Unit: Step[Unit]     = new Done(())

  /** Runs `thunk` now if the stack is shallow, else suspends it. `thunk` is a
    * by-name parameter rather than an inline one, so its code appears once:
    * inlining it into both branches doubled every nested body, and the type
    * checker's class outgrew the JVM's limit.
    */
  inline def defer[A](thunk: => Step[A])(using d: Depth): Step[A] =
    if d.current < Limit then
      d.current += 1
      try thunk
      finally d.current -= 1
    else new Later(Eval.defer(thunk.toEval))

  extension [A](s: Step[A])
    def flatMap[B](f: A => Step[B])(using d: Depth): Step[B] =
      s match
        case done: Done[A] @unchecked =>
          if d.current < Limit then
            d.current += 1
            try f(done.a)
            finally d.current -= 1
          else new Later(Eval.now(done.a).flatMap(a => f(a).toEval))
        case later: Later[A] @unchecked => new Later(later.ev.flatMap(a => f(a).toEval))

    def map[B](f: A => B): Step[B] =
      s match
        case done: Done[A] @unchecked   => new Done(f(done.a))
        case later: Later[A] @unchecked => new Later(later.ev.map(f))
