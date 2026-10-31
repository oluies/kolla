package kolla.kernel

import cats.Eval
import scala.annotation.tailrec
import scala.collection.mutable

/** Substitution and traversal primitives, mirroring `src/kernel/replace_fn.cpp`,
  * `instantiate.cpp` and `abstract.cpp`.
  *
  * Every traversal runs in `cats.Eval` with an explicit cache so that deep terms
  * do not grow the call stack on any platform.
  */
object ExprOps:

  private final class Key(val e: Expr, val offset: Int):
    override def hashCode: Int = System.identityHashCode(e) * 31 + offset
    override def equals(that: Any): Boolean = that match
      case k: Key => (k.e eq e) && k.offset == offset
      case _      => false

  /** How deep `replace` recurses on the call stack before it hands a subterm to
    * the trampolined traversal. On the v4.35 `init` export 99.9% of visits are
    * under 64 deep and the deepest is 319, so nearly all work stays direct while
    * a pathological term still cannot overflow the stack.
    */
  private final val DirectDepth = 256

  /** `lean::replace_fn`: `f` is applied to each subterm with its binder depth; a
    * `Some` result replaces the subterm and stops the descent.
    */
  def replace(e: Expr)(f: (Expr, Int) => Option[Expr]): Expr =
    replace(e, (_, _) => false)(f)

  /** As `replace`, with `keep` tested first: where it holds, the subterm is
    * returned as it is, without touching the cache or calling `f`. Callers pass
    * the O(1) test their `f` begins with (no loose bound variable in range, no
    * free variable, no level parameter), which on library corpora settles about
    * four visits in ten. An unchanged result needs no cache entry.
    */
  def replace(e: Expr, keep: (Expr, Int) => Boolean)(f: (Expr, Int) => Option[Expr]): Expr =
    // Created on the first store: a call whose visits all end at `keep` makes
    // no cache at all.
    var cache: mutable.HashMap[Key, Expr] = null
    def cached(k: Key): Expr = if cache == null then null else cache.getOrElse(k, null)
    def store(k: Key, r: Expr): Unit =
      if cache == null then cache = mutable.HashMap.empty
      cache(k) = r

    def visit(e: Expr, offset: Int, depth: Int): Expr =
      if depth >= DirectDepth then go(e, offset).value
      else if keep(e, offset) then e
      else
        val k   = new Key(e, offset)
        val hit = cached(k)
        if hit != null then hit
        else
          val r = f(e, offset) match
            case Some(r) => r
            case None    => children(e, offset, depth + 1)
          store(k, r)
          r

    def children(e: Expr, offset: Int, depth: Int): Expr = e match
      case a: Expr.App =>
        val fn  = visit(a.fn, offset, depth)
        val arg = visit(a.arg, offset, depth)
        if (fn eq a.fn) && (arg eq a.arg) then a else Expr.App(fn, arg)
      case l: Expr.Lam =>
        val t = visit(l.binderType, offset, depth)
        val b = visit(l.body, offset + 1, depth)
        if (t eq l.binderType) && (b eq l.body) then l else Expr.Lam(l.binderName, t, b, l.binderInfo)
      case p: Expr.ForallE =>
        val t = visit(p.binderType, offset, depth)
        val b = visit(p.body, offset + 1, depth)
        if (t eq p.binderType) && (b eq p.body) then p
        else Expr.ForallE(p.binderName, t, b, p.binderInfo)
      case l: Expr.LetE =>
        val t = visit(l.tpe, offset, depth)
        val v = visit(l.value, offset, depth)
        val b = visit(l.body, offset + 1, depth)
        if (t eq l.tpe) && (v eq l.value) && (b eq l.body) then l
        else Expr.LetE(l.declName, t, v, b, l.nondep)
      case p: Expr.Proj =>
        val s = visit(p.struct, offset, depth)
        if s eq p.struct then p else Expr.Proj(p.typeName, p.idx, s)
      case m: Expr.MData =>
        val x = visit(m.expr, offset, depth)
        if x eq m.expr then m else Expr.MData(m.kv, x)
      case other => other

    // The trampolined traversal, for subterms below `DirectDepth`.
    def go(e: Expr, offset: Int): Eval[Expr] =
      if keep(e, offset) then return Eval.now(e)
      val k   = new Key(e, offset)
      val hit = cached(k)
      if hit != null then Eval.now(hit)
      else
          f(e, offset) match
            case Some(r) =>
              store(k, r)
              Eval.now(r)
            case None =>
              val next: Eval[Expr] = e match
                case a: Expr.App =>
                  for
                    fn  <- Eval.defer(go(a.fn, offset))
                    arg <- Eval.defer(go(a.arg, offset))
                  yield if (fn eq a.fn) && (arg eq a.arg) then a else Expr.App(fn, arg)
                case l: Expr.Lam =>
                  for
                    t <- Eval.defer(go(l.binderType, offset))
                    b <- Eval.defer(go(l.body, offset + 1))
                  yield
                    if (t eq l.binderType) && (b eq l.body) then l
                    else Expr.Lam(l.binderName, t, b, l.binderInfo)
                case p: Expr.ForallE =>
                  for
                    t <- Eval.defer(go(p.binderType, offset))
                    b <- Eval.defer(go(p.body, offset + 1))
                  yield
                    if (t eq p.binderType) && (b eq p.body) then p
                    else Expr.ForallE(p.binderName, t, b, p.binderInfo)
                case l: Expr.LetE =>
                  for
                    t <- Eval.defer(go(l.tpe, offset))
                    v <- Eval.defer(go(l.value, offset))
                    b <- Eval.defer(go(l.body, offset + 1))
                  yield
                    if (t eq l.tpe) && (v eq l.value) && (b eq l.body) then l
                    else Expr.LetE(l.declName, t, v, b, l.nondep)
                case p: Expr.Proj =>
                  Eval.defer(go(p.struct, offset)).map { s =>
                    if s eq p.struct then p else Expr.Proj(p.typeName, p.idx, s)
                  }
                case m: Expr.MData =>
                  Eval.defer(go(m.expr, offset)).map { x =>
                    if x eq m.expr then m else Expr.MData(m.kv, x)
                  }
                case other => Eval.now(other)
              next.map { r =>
                store(k, r)
                r
              }
    visit(e, 0, 0)

  /** `lean::for_each_fn`, stopping the descent where `f` returns false.
    *
    * Children are visited in the order `for_each_fn::apply` recurses: `app_fn`
    * before `app_arg`, the binder domain before its body, and a `let`'s type and
    * value before its body. The stack is popped from the end, so children are
    * pushed in reverse.
    */
  def forEach(e: Expr)(f: (Expr, Int) => Boolean): Unit =
    val seen  = mutable.HashSet.empty[Key]
    val stack = mutable.ArrayDeque.empty[(Expr, Int)]
    stack.append((e, 0))
    while stack.nonEmpty do
      val (x, offset) = stack.removeLast()
      if seen.add(new Key(x, offset)) && f(x, offset) then
        x match
          case a: Expr.App     => stack.append((a.arg, offset)); stack.append((a.fn, offset))
          case l: Expr.Lam     => stack.append((l.body, offset + 1)); stack.append((l.binderType, offset))
          case p: Expr.ForallE => stack.append((p.body, offset + 1)); stack.append((p.binderType, offset))
          case l: Expr.LetE =>
            stack.append((l.body, offset + 1)); stack.append((l.value, offset)); stack.append((l.tpe, offset))
          case p: Expr.Proj  => stack.append((p.struct, offset))
          case m: Expr.MData => stack.append((m.expr, offset))
          case _             => ()

  // ------------------------------------------------------------ loose bvars

  /** `lean::has_loose_bvar`: is `#i` free in `e`? */
  def hasLooseBVar(e: Expr, i: Int): Boolean =
    if e.looseBVarRange <= i then false
    else
      var found = false
      forEach(e) { (m, offset) =>
        if found || m.looseBVarRange <= offset then false
        else
          m match
            case b: Expr.BVar =>
              if b.idx == offset + i then found = true
              false
            case _ => true
      }
      found

  /** `lean::lift_loose_bvars`: shift bound variables at or above `s` by `d`. */
  def liftLooseBVars(e: Expr, s: Int, d: Int): Expr =
    if d == 0 || e.looseBVarRange <= s then e
    else
      replace(e, (m, offset) => m.looseBVarRange <= offset + s) { (m, offset) =>
        if m.looseBVarRange <= offset + s then Some(m)
        else
          m match
            case b: Expr.BVar if b.idx >= offset + s => Some(Expr.BVar(b.idx + d))
            case _                                   => None
      }

  /** `lean::lower_loose_bvars`. */
  def lowerLooseBVars(e: Expr, s: Int, d: Int): Expr =
    if d == 0 || e.looseBVarRange == 0 then e
    else
      replace(e, (m, offset) => m.looseBVarRange <= offset + s) { (m, offset) =>
        if m.looseBVarRange <= offset + s then Some(m)
        else
          m match
            case b: Expr.BVar if b.idx >= offset + s =>
              if b.idx < offset + d then
                throw KernelException(ExceptionKind.Other, s"cannot lower bound variable #${b.idx}")
              Some(Expr.BVar(b.idx - d))
            case _ => None
      }

  // --------------------------------------------------------- instantiation

  /** `lean::instantiate(e, s, n, subst)`: replaces `#(s+i)` by `subst(i)` and
    * lowers the bound variables above the replaced window.
    */
  def instantiateRange(e: Expr, s: Int, subst: IndexedSeq[Expr]): Expr =
    val n = subst.length
    if s >= e.looseBVarRange || n == 0 then e
    else
      replace(e, (m, offset) => s + offset >= m.looseBVarRange) { (m, offset) =>
        val s1 = s + offset
        if s1 >= m.looseBVarRange then Some(m)
        else
          m match
            case b: Expr.BVar if b.idx >= s1 =>
              if b.idx < s1 + n then Some(liftLooseBVars(subst(b.idx - s1), 0, offset))
              else Some(Expr.BVar(b.idx - n))
            case _ => None
      }

  def instantiate(e: Expr, subst: IndexedSeq[Expr]): Expr = instantiateRange(e, 0, subst)

  /** `lean::instantiate(e, v)`: opens the outermost binder. */
  def instantiate1(e: Expr, v: Expr): Expr =
    if !e.hasLooseBVars then e else instantiateRange(e, 0, Vector(v))

  /** `lean::instantiate_rev`: `subst.last` replaces `#0`. */
  def instantiateRev(e: Expr, subst: IndexedSeq[Expr]): Expr =
    val n = subst.length
    if !e.hasLooseBVars || n == 0 then e
    else
      replace(e, (m, offset) => offset >= m.looseBVarRange) { (m, offset) =>
        if offset >= m.looseBVarRange then Some(m)
        else
          m match
            case b: Expr.BVar if b.idx >= offset =>
              if b.idx < offset + n then Some(liftLooseBVars(subst(n - (b.idx - offset) - 1), 0, offset))
              else Some(Expr.BVar(b.idx - n))
            case _ => None
      }

  /** `lean::abstract`: replaces the given free variables by bound variables,
    * `fvars.last` becoming `#0`.
    */
  def abstract_(e: Expr, fvars: IndexedSeq[Expr]): Expr =
    val n = fvars.length
    if n == 0 || !e.hasFVar then e
    else
      val ids = fvars.map {
        case f: Expr.FVar => f.id
        case other        => throw KernelException(ExceptionKind.Other, s"abstract expects free variables, got $other")
      }
      replace(e, (m, _) => !m.hasFVar) { (m, offset) =>
        if !m.hasFVar then Some(m)
        else
          m match
            case f: Expr.FVar =>
              var i = n
              var r: Option[Expr] = None
              while r.isEmpty && i > 0 do
                i -= 1
                if ids(i) == f.id then r = Some(Expr.BVar(offset + n - i - 1))
              r
            case _ => None
      }

  def abstract1(e: Expr, fvar: Expr): Expr = abstract_(e, Vector(fvar))

  // ------------------------------------------------------ level parameters

  /** `lean::instantiate_lparams`. */
  def instantiateLevelParams(e: Expr, ps: List[Name], ls: List[Level]): Expr =
    if !e.hasLevelParam || ps.isEmpty then e
    else
      replace(e, (m, _) => !m.hasLevelParam) { (m, _) =>
        if !m.hasLevelParam then Some(m)
        else
          m match
            case c: Expr.Const =>
              val us = c.levels.map(Level.instantiate(_, ps, ls))
              Some(if us.corresponds(c.levels)(_ eq _) then c else Expr.Const(c.name, us))
            case s: Expr.Sort =>
              val u = Level.instantiate(s.level, ps, ls)
              Some(if u eq s.level then s else Expr.Sort(u))
            case _ => None
      }

  def instantiateTypeLevelParams(info: ConstantInfo, ls: List[Level]): Expr =
    if info.numLevelParams != ls.length then
      throw KernelException(
        ExceptionKind.Other,
        info.name,
        s"universe parameter count mismatch: ${info.numLevelParams} expected, ${ls.length} given"
      )
    instantiateLevelParams(info.tpe, info.levelParams, ls)

  def instantiateValueLevelParams(info: ConstantInfo, ls: List[Level]): Expr =
    if info.numLevelParams != ls.length then
      throw KernelException(
        ExceptionKind.Other,
        info.name,
        s"universe parameter count mismatch: ${info.numLevelParams} expected, ${ls.length} given"
      )
    val v = info
      .value(allowOpaque = true)
      .getOrElse(
        throw KernelException(ExceptionKind.Other, info.name, "a definition or theorem was expected")
      )
    instantiateLevelParams(v, info.levelParams, ls)

  /** First level parameter of `e` not listed in `ps`. */
  def undefinedLevelParam(e: Expr, ps: List[Name]): Option[Name] =
    if !e.hasLevelParam then None
    else
      var r: Option[Name] = None
      forEach(e) { (m, _) =>
        if r.isDefined || !m.hasLevelParam then false
        else
          m match
            case c: Expr.Const =>
              c.levels.foreach(l => if r.isEmpty then r = Level.undefinedParam(l, ps))
              false
            case s: Expr.Sort =>
              r = Level.undefinedParam(s.level, ps)
              false
            case _ => true
      }
      r

  // --------------------------------------------------------------- beta

  def isHeadBeta(e: Expr): Boolean = e match
    case a: Expr.App => Expr.getAppFn(a).isInstanceOf[Expr.Lam]
    case _           => false

  /** `lean::cheap_beta_reduce`. */
  def cheapBetaReduce(e: Expr): Expr = e match
    case _: Expr.App =>
      var fn = Expr.getAppFn(e)
      if !fn.isInstanceOf[Expr.Lam] then e
      else
        val args = Expr.getAppArgs(e)
        var i    = 0
        while fn.isInstanceOf[Expr.Lam] && i < args.length do
          i += 1
          fn = fn.asInstanceOf[Expr.Lam].body
        if !fn.hasLooseBVars then Expr.mkAppRange(fn, args, i, args.length)
        else
          fn match
            case b: Expr.BVar if b.idx < i =>
              Expr.mkAppRange(args(i - b.idx - 1), args, i, args.length)
            case _ => e
    case _ => e

  /** `lean::apply_beta` restricted to what `whnf_core` needs: `f` applied to
    * `args` in application order, beta-reducing as many leading lambdas as there
    * are arguments.
    *
    * `whnf_core` passes the arguments to `instantiate` in reverse order, so the
    * innermost binder takes the last argument; `instantiateRev` is that mapping.
    */
  def betaReduce(f: Expr, args: IndexedSeq[Expr]): Expr =
    var fn = f
    var i  = 0
    while fn.isInstanceOf[Expr.Lam] && i < args.length do
      fn = fn.asInstanceOf[Expr.Lam].body
      i += 1
    Expr.mkAppRange(instantiateRev(fn, args.slice(0, i)), args, i, args.length)

  // ------------------------------------------------------- type annotations

  private def isAppOfArity(e: Expr, n: Name, arity: Int): Boolean =
    Expr.isConstOf(Expr.getAppFn(e), n) && Expr.getAppNumArgs(e) == arity

  /** `Expr.consumeTypeAnnotations`: strips `optParam`, `autoParam`, `outParam`
    * and `semiOutParam` wrappers. Nested annotations under a binder are left
    * alone, as in Lean.
    *
    * `add_inductive_fn::mk_local_decl_for` applies this to every binder domain,
    * so a parameter declared `(γ : outParam (Sort w))` enters the local context
    * as `Sort w` and the generated recursor's type carries no annotation.
    */
  @tailrec
  def consumeTypeAnnotations(e: Expr): Expr =
    if isAppOfArity(e, Names.optParam, 2) || isAppOfArity(e, Names.autoParam, 2) then
      consumeTypeAnnotations(e.asInstanceOf[Expr.App].fn.asInstanceOf[Expr.App].arg)
    else if isAppOfArity(e, Names.outParam, 1) || isAppOfArity(e, Names.semiOutParam, 1) then
      consumeTypeAnnotations(e.asInstanceOf[Expr.App].arg)
    else e

  // ------------------------------------------------- implicit argument inference

  /** `lean::has_loose_bvars_in_domain`.
    *
    * Kept in Lean's recursive form. An explicit stack would have to enqueue both
    * the `vidx + 1` continuation and the `vidx = 0` "transitivity" branch, losing
    * the short-circuit that makes the original cheap. Recursion depth is bounded
    * by the length of the forall spine; see the note on `inferImplicit`.
    */
  private def hasLooseBVarsInDomain(b: Expr, vidx: Int, strict: Boolean): Boolean =
    b match
      case pi: Expr.ForallE =>
        if hasLooseBVar(pi.binderType, vidx) then
          if pi.binderInfo.isExplicit then true
          else if hasLooseBVarsInDomain(pi.body, 0, strict) then true
          else hasLooseBVarsInDomain(pi.body, vidx + 1, strict)
        else hasLooseBVarsInDomain(pi.body, vidx + 1, strict)
      case other => if !strict then hasLooseBVar(other, vidx) else false

  /** `lean::infer_implicit`: marks a binder implicit when its variable occurs in
    * a later domain. The annotation it computes does not take part in `Expr.==`
    * and cannot be checked against an export file, which does not preserve it
    * (docs/semantics.md X14); it is still needed so the environment kolla builds
    * holds the same binder annotations Lean's does.
    *
    * Unlike the rest of this file, this pair is not stack-safe for an arbitrary
    * term: the spine walk below is iterative, but `hasLooseBVarsInDomain`
    * recurses, and the whole thing is quadratic in the spine length. Both are
    * only ever applied to a generated recursor type, whose spine is the
    * parameters, motives, minor premises and indices of one inductive block.
    */
  def inferImplicit(t: Expr, numParams: Int, strict: Boolean): Expr =
    // Collect the spine, then rebuild it from the inside out, so a forall chain
    // thousands deep does not grow the call stack.
    val spine = mutable.ArrayBuffer.empty[Expr.ForallE]
    var cur   = t
    var left  = numParams
    while left > 0 && cur.isInstanceOf[Expr.ForallE] do
      val pi = cur.asInstanceOf[Expr.ForallE]
      spine += pi
      cur = pi.body
      left -= 1
    var body = cur
    var i    = spine.length
    while i > 0 do
      i -= 1
      val pi = spine(i)
      val bi =
        if !pi.binderInfo.isExplicit then pi.binderInfo
        else if hasLooseBVarsInDomain(body, 0, strict) then BinderInfo.Implicit
        else pi.binderInfo
      body =
        if (body eq pi.body) && bi == pi.binderInfo then pi
        else Expr.ForallE(pi.binderName, pi.binderType, body, bi)
    body

  def inferImplicit(t: Expr, strict: Boolean): Expr = inferImplicit(t, Int.MaxValue, strict)

  // ------------------------------------------------------------- literals

  /** `lean::lit_type`. */
  def litType(l: Literal): Expr = l match
    case Literal.NatVal(_) => Expr.const(Names.nat)
    case Literal.StrVal(_) => Expr.const(Names.string)

  /** `lean::nat_lit_to_constructor`. */
  def natLitToConstructor(v: BigInt): Expr =
    if v == 0 then Expr.const(Names.natZero)
    else Expr.App(Expr.const(Names.natSucc), Expr.natLit(v - 1))

  /** `lean::string_lit_to_constructor`: the literal's code points as a
    * `List Char`, wrapped in the profile's string constructor.
    */
  def stringLitToConstructor(s: String, profile: KernelProfile): Expr =
    val consChar = Expr.App(Expr.Const(Names.listCons, List(Level.zero)), Expr.const(Names.char))
    val nilChar  = Expr.App(Expr.Const(Names.listNil, List(Level.zero)), Expr.const(Names.char))
    val cps      = codePoints(s)
    var r        = nilChar
    var i        = cps.length
    while i > 0 do
      i -= 1
      r = Expr.App(Expr.App(consChar, Expr.App(Expr.const(Names.charOfNat), Expr.natLit(cps(i)))), r)
    Expr.App(Expr.const(profile.stringLiteralCtor), r)

  /** Unicode code points of `s`, so that characters outside the basic
    * multilingual plane become one `Char.ofNat` each, as `utf8_decode` does.
    */
  private[kernel] def codePoints(s: String): Array[Int] =
    val out = new Array[Int](s.codePointCount(0, s.length))
    var i   = 0
    var j   = 0
    while i < s.length do
      val cp = s.codePointAt(i)
      out(j) = cp
      j += 1
      i += Character.charCount(cp)
    out
