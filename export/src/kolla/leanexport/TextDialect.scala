package kolla.leanexport

import kolla.kernel.*
import scala.collection.mutable

/** Line handlers for the two lean4export text formats. */
private[leanexport] final class TextDialect(tables: ExportTables, emit: ExportItem => Unit):

  private def binderInfo(t: String): BinderInfo = t match
    case "#BD" => BinderInfo.Default
    case "#BI" => BinderInfo.Implicit
    case "#BS" => BinderInfo.StrictImplicit
    case "#BC" => BinderInfo.InstImplicit
    case other => throw ExportException(s"unknown binder info '$other'")

  private def namesOf(idxs: List[Int]): List[Name] = idxs.map(tables.name)

  private def hexBytes(tk: Tokens): String =
    val b = mutable.ArrayBuilder.make[Byte]
    while tk.hasNext do
      val h = tk.next("string literal byte")
      if h.length != 2 then throw ExportException(s"string literal: expected a hex byte pair, got '$h'")
      val v =
        try Integer.parseInt(h, 16)
        catch case _: NumberFormatException => throw ExportException(s"string literal: bad hex byte '$h'")
      b += v.toByte
    new String(b.result(), java.nio.charset.StandardCharsets.UTF_8)

  /** Index-prefixed lines. Identical in both text formats except for `#RR`,
    * which only exists in v2.
    */
  def primitive(idx: Int, cmd: String, tk: Tokens): Boolean =
    cmd match
      case "#NS" =>
        val pre = tk.int("name prefix")
        tables.names.set(idx, tables.name(pre).str(tk.rest("name component")))
        false
      case "#NI" =>
        val pre = tk.int("name prefix")
        val i   = tk.bigInt("name numeral")
        tk.end(cmd)
        tables.names.set(idx, tables.name(pre).num(i))
        false
      case "#US" =>
        val l = tk.int("level"); tk.end(cmd)
        tables.levels.set(idx, Level.Succ(tables.level(l)))
        false
      case "#UM" =>
        val a = tk.int("level"); val b = tk.int("level"); tk.end(cmd)
        tables.levels.set(idx, Level.Max(tables.level(a), tables.level(b)))
        false
      case "#UIM" =>
        val a = tk.int("level"); val b = tk.int("level"); tk.end(cmd)
        tables.levels.set(idx, Level.IMax(tables.level(a), tables.level(b)))
        false
      case "#UP" =>
        val n = tk.int("name"); tk.end(cmd)
        tables.levels.set(idx, Level.Param(tables.name(n)))
        false
      case "#EV" =>
        val i = tk.int("bvar index"); tk.end(cmd)
        tables.exprs.set(idx, Expr.BVar(i))
        false
      case "#ES" =>
        val l = tk.int("level"); tk.end(cmd)
        tables.exprs.set(idx, Expr.Sort(tables.level(l)))
        false
      case "#EC" =>
        val n  = tk.int("name")
        val ls = tk.remaining("level").map(tables.level)
        tables.exprs.set(idx, Expr.Const(tables.name(n), ls))
        false
      case "#EA" =>
        val f = tk.int("expr"); val a = tk.int("expr"); tk.end(cmd)
        tables.exprs.set(idx, Expr.App(tables.expr(f), tables.expr(a)))
        false
      case "#EL" =>
        val bi = binderInfo(tk.next("binder info"))
        val n  = tk.int("name"); val d = tk.int("expr"); val b = tk.int("expr"); tk.end(cmd)
        tables.exprs.set(idx, Expr.Lam(tables.name(n), tables.expr(d), tables.expr(b), bi))
        false
      case "#EP" =>
        val bi = binderInfo(tk.next("binder info"))
        val n  = tk.int("name"); val d = tk.int("expr"); val b = tk.int("expr"); tk.end(cmd)
        tables.exprs.set(idx, Expr.ForallE(tables.name(n), tables.expr(d), tables.expr(b), bi))
        false
      case "#EZ" =>
        val n = tk.int("name"); val d = tk.int("expr"); val v = tk.int("expr"); val b = tk.int("expr")
        tk.end(cmd)
        tables.exprs.set(idx, Expr.LetE(tables.name(n), tables.expr(d), tables.expr(v), tables.expr(b), false))
        false
      case "#EJ" =>
        val s = tk.int("name"); val i = tk.int("projection index"); val e = tk.int("expr"); tk.end(cmd)
        tables.exprs.set(idx, Expr.Proj(tables.name(s), i, tables.expr(e)))
        false
      case "#ELN" =>
        val v = tk.bigInt("nat literal"); tk.end(cmd)
        tables.exprs.set(idx, Expr.natLit(v))
        false
      case "#ELS" =>
        tables.exprs.set(idx, Expr.strLit(hexBytes(tk)))
        false
      case "#RR" =>
        val c = tk.int("name"); val nf = tk.int("field count"); val r = tk.int("expr"); tk.end(cmd)
        tables.recRules.set(idx, RecursorRule(tables.name(c), nf, tables.expr(r)))
        true
      case other =>
        throw ExportException(s"unknown indexed command '$other'")

  /** Version-independent declaration commands. Returns false when `cmd` is not one. */
  def sharedDeclaration(cmd: String, tk: Tokens): Boolean = cmd match
    case "#AX" =>
      val n = tk.int("name"); val t = tk.int("expr")
      val lp = namesOf(tk.remaining("name"))
      emit(ExportItem.Info(ConstantInfo.AxiomInfo(
        AxiomVal(ConstantVal(tables.name(n), lp, tables.expr(t)), false)
      )))
      true
    case _ => false

  def declarationV1(cmd: String, tk: Tokens): Unit = cmd match
    case "#DEF" =>
      val n = tk.int("name"); val t = tk.int("expr"); val v = tk.int("expr")
      val lp = namesOf(tk.remaining("name"))
      emit(ExportItem.DefnWithoutHints(tables.name(n), lp, tables.expr(t), tables.expr(v)))
    case "#QUOT" =>
      tk.end(cmd)
      emit(ExportItem.Decl(Declaration.QuotDecl))
    case "#IND" =>
      val numParams = tk.int("parameter count")
      val n         = tk.int("name")
      val t         = tk.int("expr")
      val numCtors  = tk.int("constructor count")
      val ctors = List.fill(numCtors) {
        val cn = tk.int("name"); val ct = tk.int("expr")
        Constructor(tables.name(cn), tables.expr(ct))
      }
      val lp = namesOf(tk.remaining("name"))
      emit(ExportItem.Decl(Declaration.InductDecl(
        lp, numParams, List(InductiveType(tables.name(n), tables.expr(t), ctors)), false
      )))
    case other => throw ExportException(s"unknown text v1 declaration '$other'")

  def declarationV2(cmd: String, tk: Tokens): Unit = cmd match
    case "#DEF" =>
      val n = tk.int("name"); val t = tk.int("expr"); val v = tk.int("expr")
      val hints = tk.next("reducibility hint") match
        case "O" => ReducibilityHints.Opaque
        case "A" => ReducibilityHints.Abbrev
        case "R" => ReducibilityHints.Regular(tk.int("definitional height"))
        case o   => throw ExportException(s"unknown reducibility hint '$o'")
      val lp   = namesOf(tk.remaining("name"))
      val name = tables.name(n)
      emit(ExportItem.Info(ConstantInfo.DefnInfo(DefinitionVal(
        ConstantVal(name, lp, tables.expr(t)), tables.expr(v), hints, DefinitionSafety.Safe, List(name)
      ))))
    case "#THM" =>
      val n = tk.int("name"); val t = tk.int("expr"); val v = tk.int("expr")
      val lp   = namesOf(tk.remaining("name"))
      val name = tables.name(n)
      emit(ExportItem.Info(ConstantInfo.ThmInfo(TheoremVal(
        ConstantVal(name, lp, tables.expr(t)), tables.expr(v), List(name)
      ))))
    case "#OPAQ" =>
      val n = tk.int("name"); val t = tk.int("expr"); val v = tk.int("expr")
      val lp   = namesOf(tk.remaining("name"))
      val name = tables.name(n)
      emit(ExportItem.Info(ConstantInfo.OpaqueInfo(OpaqueVal(
        ConstantVal(name, lp, tables.expr(t)), tables.expr(v), false, List(name)
      ))))
    case "#QUOT" =>
      val n = tk.int("name"); val t = tk.int("expr")
      val lp   = namesOf(tk.remaining("name"))
      val name = tables.name(n)
      emit(ExportItem.Info(ConstantInfo.QuotInfo(QuotVal(
        ConstantVal(name, lp, tables.expr(t)), TextDialect.quotKindOf(name)
      ))))
    case "#IND" =>
      val n           = tk.int("name")
      val t           = tk.int("expr")
      val isReflexive = tk.int("isReflexive") != 0
      val isRec       = tk.int("isRec") != 0
      val numNested   = tk.int("numNested")
      val numParams   = tk.int("numParams")
      val numIndices  = tk.int("numIndices")
      val nInds       = tk.int("inductive count")
      val all         = namesOf(tk.takeInts(nInds, "name"))
      val numCtors    = tk.int("constructor count")
      val ctors       = namesOf(tk.takeInts(numCtors, "name"))
      val lp          = namesOf(tk.remaining("name"))
      emit(ExportItem.Info(ConstantInfo.InductInfo(InductiveVal(
        ConstantVal(tables.name(n), lp, tables.expr(t)),
        numParams, numIndices, all, ctors, numNested, isRec, false, isReflexive
      ))))
    case "#CTOR" =>
      val n         = tk.int("name")
      val t         = tk.int("expr")
      val induct    = tk.int("name")
      val cidx      = tk.int("cidx")
      val numParams = tk.int("numParams")
      val numFields = tk.int("numFields")
      val lp        = namesOf(tk.remaining("name"))
      emit(ExportItem.Info(ConstantInfo.CtorInfo(ConstructorVal(
        ConstantVal(tables.name(n), lp, tables.expr(t)),
        tables.name(induct), cidx, numParams, numFields, false
      ))))
    case "#REC" =>
      val n          = tk.int("name")
      val t          = tk.int("expr")
      val nInds      = tk.int("inductive count")
      val all        = namesOf(tk.takeInts(nInds, "name"))
      val numParams  = tk.int("numParams")
      val numIndices = tk.int("numIndices")
      val numMotives = tk.int("numMotives")
      val numMinors  = tk.int("numMinors")
      val nRules     = tk.int("rule count")
      val rules      = tk.takeInts(nRules, "recursor rule").map(tables.rule)
      val k          = tk.int("k") != 0
      val lp         = namesOf(tk.remaining("name"))
      emit(ExportItem.Info(ConstantInfo.RecInfo(RecursorVal(
        ConstantVal(tables.name(n), lp, tables.expr(t)),
        all, numParams, numIndices, numMotives, numMinors, rules, k, false
      ))))
    case other => throw ExportException(s"unknown text v2 declaration '$other'")

private[leanexport] object TextDialect:

  val quotNames: Map[Name, QuotKind] = Map(
    Name.parse("Quot")      -> QuotKind.Type,
    Name.parse("Quot.mk")   -> QuotKind.Ctor,
    Name.parse("Quot.lift") -> QuotKind.Lift,
    Name.parse("Quot.ind")  -> QuotKind.Ind
  )

  def quotKindOf(n: Name): QuotKind =
    quotNames.getOrElse(n, throw ExportException(s"not a quotient declaration: '$n'"))
