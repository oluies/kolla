package kolla.dsl

import kolla.kernel.*
import scala.collection.mutable

/** A parser for a minimal kernel-level syntax.
  *
  * {{{
  * expr    ::= lam | pi | let | app
  * lam     ::= ('fun' | 'λ') binder+ '=>' expr
  * pi      ::= ('forall' | '∀') binder+ ',' expr
  *           | atom+ '->' expr
  * let     ::= 'let' ident ':' expr ':=' expr ';' expr
  * app     ::= atom+
  * atom    ::= '(' expr ')' | 'Sort' level | ident ('.{' level,* '}')?
  *           | nat | string | '#' nat | splice
  * binder  ::= ident | '(' ident+ ':' expr ')' | '{' ... '}' | '[' ... ']'
  *           | '⦃' ... '⦄'
  * level   ::= 'max' level level | 'imax' level level | 'succ' level
  *           | nat | ident | '(' level ')'
  * }}}
  *
  * There are no implicit arguments to insert and no unification: an identifier
  * is a bound variable if a binder introduced it and a constant otherwise, and
  * a bound variable becomes its de Bruijn index directly.
  */
object LeanParser:

  /** The nesting this parser accepts. Recursive descent is the clearest way to
    * write this grammar, so the depth is bounded explicitly and reported as a
    * parse error; the limit is well above anything hand-written, and Scala.js
    * has a much smaller stack than the JVM.
    */
  val maxDepth: Int = 200

  /** A `${...}` hole. The parser leaves a marker which the interpolator macro
    * replaces with the spliced term; at runtime the marker is substituted from
    * the supplied arguments.
    */
  val spliceMarker: Name = Name.mkSimple("_leanSplice")

  def spliceIndex(e: Expr): Option[Int] = e match
    case m: Expr.MVar =>
      m.id match
        case n: Name.Num if n.pre == spliceMarker && n.value.isValidInt => Some(n.value.toInt)
        case _                                                         => None
    case _ => None

  /** Splits a dotted identifier into components.
    *
    * `Name.parse` is the inverse of `Name.toString` (docs/semantics.md N4), so
    * it reads an all-digit component as a numeral, which is what this syntax
    * means by `Foo.3`. It also reads `«...»`, which the surface syntax has no
    * way to produce: the tokeniser only admits identifier characters, and a
    * guillemet is not one.
    */
  def parseName(s: String): Name = Name.parse(s)

  final case class ParseError(message: String, offset: Int):
    override def toString: String = s"$message at offset $offset"

  def parse(input: String): Either[ParseError, Expr] =
    val p = new Parser(input)
    try
      val e = p.expr(Nil)
      p.skipWs()
      if !p.atEnd then p.fail("unexpected trailing input")
      Right(e)
    catch case e: ParseException => Left(ParseError(e.detail, e.offset))

  def parseOrThrow(input: String): Expr = parse(input) match
    case Right(e) => e
    case Left(err) =>
      throw new IllegalArgumentException(s"lean syntax error: $err")

  private final class ParseException(val detail: String, val offset: Int) extends RuntimeException(detail)

  private val keywords = Set("fun", "forall", "let", "Sort", "max", "imax", "succ")

  final class Parser(private val s: String):
    private var i = 0
    private var depth = 0

    private inline def nested[A](body: => A): A =
      depth += 1
      if depth > maxDepth then fail(s"nesting deeper than $maxDepth")
      try body
      finally depth -= 1

    def atEnd: Boolean = i >= s.length

    def fail(msg: String): Nothing = throw new ParseException(msg, i)

    def skipWs(): Unit =
      while i < s.length && (s.charAt(i) == ' ' || s.charAt(i) == '\t' || s.charAt(i) == '\n' ||
          s.charAt(i) == '\r')
      do i += 1

    private def peekIs(t: String): Boolean =
      skipWs()
      s.startsWith(t, i)

    private def eat(t: String): Boolean =
      if peekIs(t) then { i += t.length; true } else false

    /** A keyword must not be the prefix of a longer identifier: `funext` is a
      * constant, not `fun` followed by `ext`.
      */
    private def peekKeyword(t: String): Boolean =
      peekIs(t) && {
        val j = i + t.length
        j >= s.length || !isIdentPart(s.charAt(j))
      }

    private def eatKeyword(t: String): Boolean =
      if peekKeyword(t) then { i += t.length; true } else false

    private def expect(t: String): Unit =
      if !eat(t) then fail(s"expected '$t'")

    /** A `:` that is not the start of `:=`, so `let x : T := v` parses and
      * `let x := v` reports the missing type rather than failing later.
      */
    private def expectTypeColon(): Unit =
      skipWs()
      val ok = i < s.length && s.charAt(i) == ':' && !(i + 1 < s.length && s.charAt(i + 1) == '=')
      if !ok then fail("expected ':'")
      i += 1

    private def isIdentStart(c: Char): Boolean = c.isLetter || c == '_'
    private def isIdentPart(c: Char): Boolean =
      c.isLetterOrDigit || c == '_' || c == '\'' || c == '!' || c == '?' || c == '.'

    /** An identifier, possibly dotted. A trailing `.{` is not consumed. */
    private def ident(): String =
      skipWs()
      if atEnd || !isIdentStart(s.charAt(i)) then fail("expected an identifier")
      val start = i
      i += 1
      while i < s.length && isIdentPart(s.charAt(i)) do
        // `.{` begins a universe argument list, not part of the name.
        if s.charAt(i) == '.' && i + 1 < s.length && s.charAt(i + 1) == '{' then
          return s.substring(start, i)
        i += 1
      s.substring(start, i)

    private def natLit(): BigInt =
      skipWs()
      val start = i
      while i < s.length && s.charAt(i).isDigit do i += 1
      if start == i then fail("expected a numeral")
      BigInt(s.substring(start, i))

    private def stringLit(): String =
      expect("\"")
      val sb = new StringBuilder
      while i < s.length && s.charAt(i) != '"' do
        if s.charAt(i) == '\\' && i + 1 < s.length then
          i += 1
          s.charAt(i) match
            case 'n'   => sb += '\n'
            case 't'   => sb += '\t'
            case 'r'   => sb += '\r'
            case '\\'  => sb += '\\'
            case '"'   => sb += '"'
            case other => fail(s"bad escape '\\$other'")
          i += 1
        else
          sb += s.charAt(i)
          i += 1
      if atEnd then fail("unterminated string literal")
      i += 1
      sb.result()

    // ------------------------------------------------------------- levels

    def level(): Level =
      skipWs()
      if eatKeyword("max") then
        val a = levelAtom(); val b = levelAtom(); Level.max(a, b)
      else if eatKeyword("imax") then
        val a = levelAtom(); val b = levelAtom(); Level.imax(a, b)
      else if eatKeyword("succ") then Level.Succ(levelAtom())
      else levelAtom()

    private def levelAtom(): Level = nested(levelAtomCore())

    private def levelAtomCore(): Level =
      skipWs()
      if atEnd then fail("expected a universe level")
      if eat("(") then
        val l = level()
        expect(")")
        l
      else if s.charAt(i).isDigit then Level.ofNat(natLit().toInt)
      else if peekKeyword("max") || peekKeyword("imax") || peekKeyword("succ") then level()
      else Level.Param(parseName(ident()))

    private def levelList(): List[Level] =
      expect(".{")
      val out = List.newBuilder[Level]
      skipWs()
      if !peekIs("}") then
        out += level()
        while eat(",") do out += level()
      expect("}")
      out.result()

    // -------------------------------------------------------------- binders

    private final case class Binder(name: String, tpe: Expr, info: BinderInfo)

    /** One binder group, which may introduce several names of the same type. */
    private def binderGroup(scope: List[String]): List[Binder] =
      skipWs()
      val (close, info) =
        if eat("(") then (")", BinderInfo.Default)
        else if eat("{") then ("}", BinderInfo.Implicit)
        else if eat("⦃") then ("⦄", BinderInfo.StrictImplicit)
        else if eat("[") then ("]", BinderInfo.InstImplicit)
        else
          // A bare identifier binder has no type annotation, which the kernel
          // cannot represent, so require the parenthesised form.
          fail("expected a binder group, for example '(x : Nat)'")
      val names = List.newBuilder[String]
      names += ident()
      skipWs()
      while !peekIs(":") do
        names += ident()
        skipWs()
        if atEnd then fail("expected ':'")
      expectTypeColon()
      val tpe = expr(scope)
      expect(close)
      // The type was read in the scope before the group, but the k-th name sits
      // under the k preceding names of the same group, so its loose bound
      // variables have to be shifted.
      names.result().zipWithIndex.map { (n, k) =>
        Binder(n, ExprOps.liftLooseBVars(tpe, 0, k), info)
      }

    private def binderGroups(scope: List[String]): List[Binder] =
      val out = mutable.ArrayBuffer.empty[Binder]
      var sc  = scope
      while peekIs("(") || peekIs("{") || peekIs("[") || peekIs("⦃") do
        // Each group's type is read in the scope established so far.
        val gs = binderGroup(sc)
        gs.foreach { b =>
          out += b
          sc = b.name :: sc
        }
      if out.isEmpty then fail("expected a binder group, for example '(x : Nat)'")
      out.toList

    // ----------------------------------------------------------------- exprs

    def expr(scope: List[String]): Expr = nested(exprCore(scope))

    private def exprCore(scope: List[String]): Expr =
      skipWs()
      if peekKeyword("fun") || peekIs("λ") then
        if !eatKeyword("fun") then expect("λ")
        val bs = binderGroupsIn(scope)
        expect("=>")
        buildBinders(bs, scope, isPi = false)
      else if peekKeyword("forall") || peekIs("∀") then
        if !eatKeyword("forall") then expect("∀")
        val bs = binderGroupsIn(scope)
        expect(",")
        buildBinders(bs, scope, isPi = true)
      else if peekKeyword("let") then
        if !eatKeyword("let") then fail("expected 'let'")
        val n = ident()
        expectTypeColon()
        val tpe = expr(scope)
        expect(":=")
        val value = expr(scope)
        expect(";")
        val body = expr(n :: scope)
        Expr.LetE(parseName(n), tpe, value, body, false)
      else
        val lhs = application(scope)
        if eat("->") || eat("→") then
          // A non-dependent arrow: the codomain is read under one more binder.
          val cod = expr("_" :: scope)
          Expr.ForallE(Name.mkSimple("a"), lhs, cod, BinderInfo.Default)
        else lhs

    /** Binder groups, each read in the scope the previous ones established. */
    private def binderGroupsIn(scope: List[String]): List[Binder] = binderGroups(scope)

    private def buildBinders(bs: List[Binder], scope: List[String], isPi: Boolean): Expr =
      val inner = expr(bs.reverse.map(_.name) ++ scope)
      bs.foldRight(inner) { (b, acc) =>
        if isPi then Expr.ForallE(parseName(b.name), b.tpe, acc, b.info)
        else Expr.Lam(parseName(b.name), b.tpe, acc, b.info)
      }

    private def startsAtom: Boolean =
      skipWs()
      if atEnd then false
      else
        val c = s.charAt(i)
        c == '(' || c == '#' || c == '"' || c == '$' || c.isDigit || isIdentStart(c)

    private def application(scope: List[String]): Expr =
      var r = atom(scope)
      while startsAtom && !peekIs("->") && !peekIs("→") do r = Expr.App(r, atom(scope))
      r

    private def atom(scope: List[String]): Expr = nested(atomCore(scope))

    private def atomCore(scope: List[String]): Expr =
      skipWs()
      if atEnd then fail("expected an expression")
      if eat("(") then
        val e = expr(scope)
        expect(")")
        e
      else if eat("#") then Expr.BVar(natLit().toInt)
      else if eat("$") then
        // A `${...}` hole, numbered by the interpolator.
        val idx = natLit().toInt
        Expr.MVar(spliceMarker.num(idx))
      else if peekIs("\"") then Expr.strLit(stringLit())
      else if s.charAt(i).isDigit then Expr.natLit(natLit())
      else if peekKeyword("Sort") then
        if !eatKeyword("Sort") then fail("expected 'Sort'")
        Expr.Sort(levelAtom())
      else
        val id = ident()
        if keywords.contains(id) then fail(s"'$id' cannot start an argument")
        scope.indexOf(id) match
          case -1 =>
            val ls = if peekIs(".{") then levelList() else Nil
            Expr.Const(parseName(id), ls)
          case k => Expr.BVar(k)
