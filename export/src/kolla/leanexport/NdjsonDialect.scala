package kolla.leanexport

import kolla.kernel.*

/** Line handler for the lean4export NDJSON formats.
  *
  * 3.0.x groups the fields of an inductive declaration under
  * `inductiveVals`/`constructorVals`/`recursorVals` and wraps single
  * definitions, theorems and opaques in one-element arrays; 3.1.x uses
  * `types`/`ctors`/`recs` and bare objects. Both spellings are accepted.
  */
private[leanexport] final class NdjsonDialect(tables: ExportTables, emit: ExportItem => Unit):
  import Json.*

  private def name(j: Json, what: String): Name   = tables.name(j.asInt(what))
  private def level(j: Json, what: String): Level = tables.level(j.asInt(what))
  private def expr(j: Json, what: String): Expr   = tables.expr(j.asInt(what))

  private def nameList(j: Json, what: String): List[Name] =
    j.asArr(what).toList.map(name(_, what))

  private def binderInfo(s: String): BinderInfo = s match
    case "default"        => BinderInfo.Default
    case "implicit"       => BinderInfo.Implicit
    case "strictImplicit" => BinderInfo.StrictImplicit
    case "instImplicit"   => BinderInfo.InstImplicit
    case other            => throw ExportException(s"unknown binder info '$other'")

  private def constantVal(f: Map[String, Json], what: String): ConstantVal =
    ConstantVal(
      name(f.req("name", what), what),
      nameList(f.req("levelParams", what), what),
      expr(f.req("type", what), what)
    )

  def line(root: Map[String, Json]): Option[ExportMeta] =
    root.get("meta") match
      case Some(m) => return Some(meta(m))
      case None    => ()
    root.get("in") match
      case Some(i) => nameItem(i.asInt("name index"), root); return None
      case None    => ()
    root.get("il") match
      case Some(i) => levelItem(i.asInt("level index"), root); return None
      case None    => ()
    root.get("ie") match
      case Some(i) => exprItem(i.asInt("expr index"), root); return None
      case None    => ()
    declaration(root)
    None

  private def meta(j: Json): ExportMeta =
    val f  = j.asObj("meta")
    val ex = f.get("exporter").map(_.asObj("meta.exporter")).getOrElse(Map.empty)
    val ln = f.get("lean").map(_.asObj("meta.lean")).getOrElse(Map.empty)
    ExportMeta(
      ex.get("name").map(_.asStr("meta.exporter.name")).getOrElse(""),
      ex.get("version").map(_.asStr("meta.exporter.version")).getOrElse(""),
      ln.get("version").map(_.asStr("meta.lean.version")).getOrElse(""),
      ln.get("githash").map(_.asStr("meta.lean.githash")).getOrElse("")
    )

  private def nameItem(idx: Int, root: Map[String, Json]): Unit =
    root.get("str") match
      case Some(j) =>
        val f = j.asObj("Name.str")
        tables.names.set(idx, name(f.req("pre", "Name.str"), "Name.str").str(f.req("str", "Name.str").asStr("Name.str")))
      case None =>
        root.get("num") match
          case Some(j) =>
            val f = j.asObj("Name.num")
            tables.names.set(idx, name(f.req("pre", "Name.num"), "Name.num").num(f.req("i", "Name.num").asBigInt("Name.num")))
          case None => throw ExportException(s"name item ${root.keys.mkString(",")} has no 'str' or 'num'")

  private def levelItem(idx: Int, root: Map[String, Json]): Unit =
    val l =
      if root.contains("succ") then Level.Succ(level(root("succ"), "Level.succ"))
      else if root.contains("max") then
        val a = root("max").asArr("Level.max")
        if a.length != 2 then throw ExportException("Level.max: expected two operands")
        Level.Max(level(a(0), "Level.max"), level(a(1), "Level.max"))
      else if root.contains("imax") then
        val a = root("imax").asArr("Level.imax")
        if a.length != 2 then throw ExportException("Level.imax: expected two operands")
        Level.IMax(level(a(0), "Level.imax"), level(a(1), "Level.imax"))
      else if root.contains("param") then Level.Param(name(root("param"), "Level.param"))
      else throw ExportException(s"level item ${root.keys.mkString(",")} has no known constructor")
    tables.levels.set(idx, l)

  private def exprItem(idx: Int, root: Map[String, Json]): Unit =
    val e =
      if root.contains("bvar") then Expr.BVar(root("bvar").asInt("Expr.bvar"))
      else if root.contains("sort") then Expr.Sort(level(root("sort"), "Expr.sort"))
      else if root.contains("const") then
        val f = root("const").asObj("Expr.const")
        Expr.Const(
          name(f.req("name", "Expr.const"), "Expr.const"),
          f.req("us", "Expr.const").asArr("Expr.const").toList.map(level(_, "Expr.const"))
        )
      else if root.contains("app") then
        val f = root("app").asObj("Expr.app")
        Expr.App(expr(f.req("fn", "Expr.app"), "Expr.app"), expr(f.req("arg", "Expr.app"), "Expr.app"))
      else if root.contains("lam") then
        val f = root("lam").asObj("Expr.lam")
        Expr.Lam(
          name(f.req("name", "Expr.lam"), "Expr.lam"),
          expr(f.req("type", "Expr.lam"), "Expr.lam"),
          expr(f.req("body", "Expr.lam"), "Expr.lam"),
          binderInfo(f.req("binderInfo", "Expr.lam").asStr("Expr.lam"))
        )
      else if root.contains("forallE") then
        val f = root("forallE").asObj("Expr.forallE")
        Expr.ForallE(
          name(f.req("name", "Expr.forallE"), "Expr.forallE"),
          expr(f.req("type", "Expr.forallE"), "Expr.forallE"),
          expr(f.req("body", "Expr.forallE"), "Expr.forallE"),
          binderInfo(f.req("binderInfo", "Expr.forallE").asStr("Expr.forallE"))
        )
      else if root.contains("letE") then
        val f = root("letE").asObj("Expr.letE")
        Expr.LetE(
          name(f.req("name", "Expr.letE"), "Expr.letE"),
          expr(f.req("type", "Expr.letE"), "Expr.letE"),
          expr(f.req("value", "Expr.letE"), "Expr.letE"),
          expr(f.req("body", "Expr.letE"), "Expr.letE"),
          f.req("nondep", "Expr.letE").asBool("Expr.letE")
        )
      else if root.contains("proj") then
        val f = root("proj").asObj("Expr.proj")
        Expr.Proj(
          name(f.req("typeName", "Expr.proj"), "Expr.proj"),
          f.req("idx", "Expr.proj").asInt("Expr.proj"),
          expr(f.req("struct", "Expr.proj"), "Expr.proj")
        )
      else if root.contains("natVal") then
        root("natVal") match
          case Str(s) =>
            try Expr.natLit(BigInt(s))
            catch case _: NumberFormatException => throw ExportException(s"Expr.lit natVal: not an integer '$s'")
          case Num(v) => Expr.natLit(v)
          case other  => throw ExportException(s"Expr.lit natVal: expected string or integer, got ${other.kindName}")
      else if root.contains("strVal") then Expr.strLit(root("strVal").asStr("Expr.lit strVal"))
      else if root.contains("mdata") then
        val f = root("mdata").asObj("Expr.mdata")
        Expr.MData(KVMap.empty, expr(f.req("expr", "Expr.mdata"), "Expr.mdata"))
      else throw ExportException(s"expr item ${root.keys.mkString(",")} has no known constructor")
    tables.exprs.set(idx, e)

  private def group(j: Json, what: String): Vector[Map[String, Json]] = j match
    case Arr(vs) => vs.map(_.asObj(what))
    case Obj(f)  => Vector(f)
    case other   => throw ExportException(s"$what: expected object or array, got ${other.kindName}")

  private def declaration(root: Map[String, Json]): Unit =
    if root.contains("axiom") then group(root("axiom"), "axiom").foreach(axiom)
    else if root.contains("def") then group(root("def"), "def").foreach(defn)
    else if root.contains("thm") then group(root("thm"), "thm").foreach(thm)
    else if root.contains("opaque") then group(root("opaque"), "opaque").foreach(opaq)
    else if root.contains("quot") then group(root("quot"), "quot").foreach(quot)
    else if root.contains("inductive") then inductive(root("inductive").asObj("inductive"))
    else throw ExportException(s"unknown export object with keys ${root.keys.mkString(",")}")

  private def axiom(f: Map[String, Json]): Unit =
    emit(ExportItem.Info(ConstantInfo.AxiomInfo(AxiomVal(
      constantVal(f, "axiom"),
      f.get("isUnsafe").map(_.asBool("axiom.isUnsafe")).getOrElse(false)
    ))))

  private def defn(f: Map[String, Json]): Unit =
    val cv = constantVal(f, "def")
    val hints = f.req("hints", "def.hints") match
      case Str("opaque") => ReducibilityHints.Opaque
      case Str("abbrev") => ReducibilityHints.Abbrev
      case Obj(h)        => ReducibilityHints.Regular(h.req("regular", "def.hints").asInt("def.hints.regular"))
      case other         => throw ExportException(s"def.hints: unexpected ${other.kindName}")
    val safety = f.req("safety", "def.safety").asStr("def.safety") match
      case "unsafe"  => DefinitionSafety.Unsafe
      case "safe"    => DefinitionSafety.Safe
      case "partial" => DefinitionSafety.Partial
      case other     => throw ExportException(s"def.safety: unknown value '$other'")
    emit(ExportItem.Info(ConstantInfo.DefnInfo(DefinitionVal(
      cv, expr(f.req("value", "def"), "def"), hints, safety, allOf(f, cv.name, "def")
    ))))

  private def thm(f: Map[String, Json]): Unit =
    val cv = constantVal(f, "thm")
    emit(ExportItem.Info(ConstantInfo.ThmInfo(TheoremVal(
      cv, expr(f.req("value", "thm"), "thm"), allOf(f, cv.name, "thm")
    ))))

  private def opaq(f: Map[String, Json]): Unit =
    val cv = constantVal(f, "opaque")
    emit(ExportItem.Info(ConstantInfo.OpaqueInfo(OpaqueVal(
      cv,
      expr(f.req("value", "opaque"), "opaque"),
      f.get("isUnsafe").map(_.asBool("opaque.isUnsafe")).getOrElse(false),
      allOf(f, cv.name, "opaque")
    ))))

  private def quot(f: Map[String, Json]): Unit =
    val kind = f.req("kind", "quot.kind").asStr("quot.kind") match
      case "type" => QuotKind.Type
      case "ctor" => QuotKind.Ctor
      case "lift" => QuotKind.Lift
      case "ind"  => QuotKind.Ind
      case other  => throw ExportException(s"quot.kind: unknown value '$other'")
    emit(ExportItem.Info(ConstantInfo.QuotInfo(QuotVal(constantVal(f, "quot"), kind))))

  private def allOf(f: Map[String, Json], self: Name, what: String): List[Name] =
    f.get("all").map(nameList(_, s"$what.all")).getOrElse(List(self))

  private def inductive(f: Map[String, Json]): Unit =
    def pick(a: String, b: String): Vector[Map[String, Json]] =
      f.get(a).orElse(f.get(b)) match
        case Some(j) => j.asArr(s"inductive.$a").map(_.asObj(s"inductive.$a"))
        case None    => throw ExportException(s"inductive: missing field '$a'")
    pick("types", "inductiveVals").foreach(inductVal)
    pick("ctors", "constructorVals").foreach(ctorVal)
    pick("recs", "recursorVals").foreach(recVal)

  private def inductVal(f: Map[String, Json]): Unit =
    emit(ExportItem.Info(ConstantInfo.InductInfo(InductiveVal(
      constantVal(f, "inductive.types"),
      f.req("numParams", "inductive.types").asInt("numParams"),
      f.req("numIndices", "inductive.types").asInt("numIndices"),
      nameList(f.req("all", "inductive.types"), "inductive.types.all"),
      nameList(f.req("ctors", "inductive.types"), "inductive.types.ctors"),
      f.req("numNested", "inductive.types").asInt("numNested"),
      f.req("isRec", "inductive.types").asBool("isRec"),
      f.req("isUnsafe", "inductive.types").asBool("isUnsafe"),
      f.req("isReflexive", "inductive.types").asBool("isReflexive")
    ))))

  private def ctorVal(f: Map[String, Json]): Unit =
    emit(ExportItem.Info(ConstantInfo.CtorInfo(ConstructorVal(
      constantVal(f, "inductive.ctors"),
      name(f.req("induct", "inductive.ctors"), "induct"),
      f.req("cidx", "inductive.ctors").asInt("cidx"),
      f.req("numParams", "inductive.ctors").asInt("numParams"),
      f.req("numFields", "inductive.ctors").asInt("numFields"),
      f.req("isUnsafe", "inductive.ctors").asBool("isUnsafe")
    ))))

  private def recVal(f: Map[String, Json]): Unit =
    val rules = f.req("rules", "inductive.recs").asArr("inductive.recs.rules").toList.map { r =>
      val rf = r.asObj("recursor rule")
      RecursorRule(
        name(rf.req("ctor", "recursor rule"), "recursor rule"),
        rf.req("nfields", "recursor rule").asInt("nfields"),
        expr(rf.req("rhs", "recursor rule"), "recursor rule")
      )
    }
    emit(ExportItem.Info(ConstantInfo.RecInfo(RecursorVal(
      constantVal(f, "inductive.recs"),
      nameList(f.req("all", "inductive.recs"), "inductive.recs.all"),
      f.req("numParams", "inductive.recs").asInt("numParams"),
      f.req("numIndices", "inductive.recs").asInt("numIndices"),
      f.req("numMotives", "inductive.recs").asInt("numMotives"),
      f.req("numMinors", "inductive.recs").asInt("numMinors"),
      rules,
      f.req("k", "inductive.recs").asBool("k"),
      f.req("isUnsafe", "inductive.recs").asBool("isUnsafe")
    ))))
