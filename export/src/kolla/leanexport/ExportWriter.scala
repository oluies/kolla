package kolla.leanexport

import kolla.kernel.*
import scala.collection.mutable

/** Serializes an `ExportEnv` back into a lean4export format.
  *
  * Index assignment follows first use during a depth-first walk, as the exporter
  * does, but dependency ordering between declarations is taken from the item
  * order rather than recomputed, so the output is not byte-identical to
  * lean4export's.
  */
final class ExportWriter(format: ExportFormat, out: String => Unit):
  import ExportFormat.*

  private val nameIdx  = mutable.HashMap.empty[Name, Int]
  private val levelIdx = mutable.HashMap.empty[Level, Int]
  private val exprIdx  = mutable.HashMap.empty[Expr, Int]
  private val ruleIdx  = mutable.HashMap.empty[RecursorRule, Int]

  nameIdx(Name.anonymous) = 0
  levelIdx(Level.zero) = 0

  private val isJson = !format.isText

  def write(env: ExportEnv): Unit =
    if isJson then
      val m = env.meta.getOrElse(ExportMeta("lean4export", jsonVersion, "", ""))
      out(
        s"""{"meta":{"exporter":{"name":${Jsonw.str(m.exporterName)},"version":${Jsonw.str(m.exporterVersion)}},""" +
          s""""format":{"version":${Jsonw.str(jsonVersion)}},""" +
          s""""lean":{"githash":${Jsonw.str(m.leanGithash)},"version":${Jsonw.str(m.leanVersion)}}}}"""
      )
    env.items.foreach(item)

  private def jsonVersion: String = format match
    case Ndjson(v) if v.nonEmpty => v
    case _                       => "3.1.0"

  private def legacyJson: Boolean = format.ndjsonMajorMinor.exists((a, b) => a == 3 && b == 0)

  // ------------------------------------------------------------------- names

  private def name(n: Name): Int =
    nameIdx.get(n) match
      case Some(i) => i
      case None =>
        val pre = name(n.prefix)
        val i   = nameIdx.size
        n match
          case s: Name.Str =>
            if isJson then out(s"""{"in":$i,"str":{"pre":$pre,"str":${Jsonw.str(s.value)}}}""")
            else out(s"$i #NS $pre ${s.value}")
          case m: Name.Num =>
            if isJson then out(s"""{"in":$i,"num":{"pre":$pre,"i":${m.value}}}""")
            else out(s"$i #NI $pre ${m.value}")
          case _ => throw ExportException("cannot emit the anonymous name")
        nameIdx(n) = i
        i

  private def names(ns: List[Name]): List[Int] = ns.map(name)

  // ------------------------------------------------------------------ levels

  private def level(l: Level): Int =
    levelIdx.get(l) match
      case Some(i) => i
      case None =>
        val body = l match
          case s: Level.Succ =>
            val a = level(s.level)
            () => if isJson then s""""succ":$a""" else s"#US $a"
          case m: Level.Max =>
            val a = level(m.lhs); val b = level(m.rhs)
            () => if isJson then s""""max":[$a,$b]""" else s"#UM $a $b"
          case m: Level.IMax =>
            val a = level(m.lhs); val b = level(m.rhs)
            () => if isJson then s""""imax":[$a,$b]""" else s"#UIM $a $b"
          case p: Level.Param =>
            val a = name(p.name)
            () => if isJson then s""""param":$a""" else s"#UP $a"
          case p: Level.MVar => throw ExportException("cannot emit a level metavariable")
          case _             => throw ExportException("cannot emit level zero")
        val i = levelIdx.size
        if isJson then out(s"""{"il":$i,${body()}}""") else out(s"$i ${body()}")
        levelIdx(l) = i
        i

  // ------------------------------------------------------------------- exprs

  private def binderJson(bi: BinderInfo): String = bi match
    case BinderInfo.Default        => "default"
    case BinderInfo.Implicit       => "implicit"
    case BinderInfo.StrictImplicit => "strictImplicit"
    case BinderInfo.InstImplicit   => "instImplicit"

  private def binderText(bi: BinderInfo): String = bi match
    case BinderInfo.Default        => "#BD"
    case BinderInfo.Implicit       => "#BI"
    case BinderInfo.StrictImplicit => "#BS"
    case BinderInfo.InstImplicit   => "#BC"

  /** Children are emitted bottom-up with an explicit stack so that deep terms do
    * not grow the call stack.
    */
  private def expr(root: Expr): Int =
    val work = mutable.ArrayDeque.empty[(Expr, Boolean)]
    work.append((root, false))
    while work.nonEmpty do
      val (e, ready) = work.removeLast()
      if !exprIdx.contains(e) then
        if ready then emitExpr(e)
        else
          work.append((e, true))
          children(e).foreach(c => if !exprIdx.contains(c) then work.append((c, false)))
    exprIdx(root)

  private def children(e: Expr): List[Expr] = e match
    case a: Expr.App     => List(a.fn, a.arg)
    case l: Expr.Lam     => List(l.binderType, l.body)
    case f: Expr.ForallE => List(f.binderType, f.body)
    case l: Expr.LetE    => List(l.tpe, l.value, l.body)
    case p: Expr.Proj    => List(p.struct)
    case m: Expr.MData   => List(m.expr)
    case _               => Nil

  private def emitExpr(e: Expr): Unit =
    val body = e match
      case b: Expr.BVar => if isJson then s""""bvar":${b.idx}""" else s"#EV ${b.idx}"
      case s: Expr.Sort =>
        val l = level(s.level)
        if isJson then s""""sort":$l""" else s"#ES $l"
      case c: Expr.Const =>
        val n  = name(c.name)
        val ls = c.levels.map(level)
        if isJson then s""""const":{"name":$n,"us":[${ls.mkString(",")}]}"""
        else if ls.isEmpty then s"#EC $n"
        else s"#EC $n ${ls.mkString(" ")}"
      case a: Expr.App =>
        val f = exprIdx(a.fn); val x = exprIdx(a.arg)
        if isJson then s""""app":{"fn":$f,"arg":$x}""" else s"#EA $f $x"
      case l: Expr.Lam =>
        val n = name(l.binderName); val d = exprIdx(l.binderType); val b = exprIdx(l.body)
        if isJson then s""""lam":{"name":$n,"type":$d,"body":$b,"binderInfo":"${binderJson(l.binderInfo)}"}"""
        else s"#EL ${binderText(l.binderInfo)} $n $d $b"
      case f: Expr.ForallE =>
        val n = name(f.binderName); val d = exprIdx(f.binderType); val b = exprIdx(f.body)
        if isJson then s""""forallE":{"name":$n,"type":$d,"body":$b,"binderInfo":"${binderJson(f.binderInfo)}"}"""
        else s"#EP ${binderText(f.binderInfo)} $n $d $b"
      case l: Expr.LetE =>
        val n = name(l.declName); val d = exprIdx(l.tpe); val v = exprIdx(l.value); val b = exprIdx(l.body)
        if isJson then s""""letE":{"name":$n,"type":$d,"value":$v,"body":$b,"nondep":${l.nondep}}"""
        else s"#EZ $n $d $v $b"
      case p: Expr.Proj =>
        val s = name(p.typeName); val x = exprIdx(p.struct)
        if isJson then s""""proj":{"typeName":$s,"idx":${p.idx},"struct":$x}"""
        else s"#EJ $s ${p.idx} $x"
      case l: Expr.Lit =>
        l.value match
          case Literal.NatVal(v) => if isJson then s""""natVal":"$v"""" else s"#ELN $v"
          case Literal.StrVal(v) =>
            if isJson then s""""strVal":${Jsonw.str(v)}""" else s"#ELS ${ExportWriter.hex(v)}"
      case m: Expr.MData =>
        val x = exprIdx(m.expr)
        if isJson then s""""mdata":{"expr":$x,"data":{}}"""
        else throw ExportException("the text formats cannot represent Expr.mdata")
      case _: Expr.FVar => throw ExportException("cannot emit a free variable")
      case _: Expr.MVar => throw ExportException("cannot emit a metavariable")
    val i = exprIdx.size
    if isJson then out(s"""{"ie":$i,$body}""") else out(s"$i $body")
    exprIdx(e) = i

  private def rule(r: RecursorRule): Int =
    ruleIdx.get(r) match
      case Some(i) => i
      case None =>
        val c = name(r.ctor)
        val x = expr(r.rhs)
        val i = ruleIdx.size
        out(s"$i #RR $c ${r.nfields} $x")
        ruleIdx(r) = i
        i

  // -------------------------------------------------------------- declarations

  private def item(it: ExportItem): Unit = it match
    case ExportItem.Info(i) => info(i)
    case ExportItem.Decl(d) => decl(d)
    case ExportItem.DefnWithoutHints(n, lp, t, v) =>
      if format != TextV1 then
        throw ExportException(s"only the text v1 format can represent a definition without hints: $n")
      val ni = name(n); val ti = expr(t); val vi = expr(v); val ls = uparams(lp)
      out(s"#DEF $ni $ti $vi${tail(ls)}")

  private def uparams(lp: List[Name]): List[Int] =
    val idxs = names(lp)
    if format.isText then lp.foreach(p => level(Level.Param(p)))
    idxs

  private def tail(idxs: List[Int]): String =
    if idxs.isEmpty then "" else " " + idxs.mkString(" ")

  private def decl(d: Declaration): Unit = d match
    case Declaration.QuotDecl =>
      if format != TextV1 then throw ExportException("only the text v1 format has a bare #QUOT")
      out("#QUOT")
    case Declaration.InductDecl(lp, numParams, types, _) =>
      if format != TextV1 then
        throw ExportException("only the text v1 format carries inductive declarations as kernel inputs")
      types.foreach { t =>
        val n  = name(t.name)
        val ty = expr(t.tpe)
        val cs = t.ctors.flatMap(c => List(name(c.name), expr(c.tpe)))
        val ls = uparams(lp)
        out(s"#IND $numParams $n $ty ${t.ctors.length}${tail(cs)}${tail(ls)}")
      }
    case other => throw ExportException(s"cannot emit declaration ${other.getClass.getSimpleName}")

  private def info(i: ConstantInfo): Unit =
    import ConstantInfo.*
    i match
      case AxiomInfo(v)  => axiom(v)
      case DefnInfo(v)   => defn(v)
      case ThmInfo(v)    => thm(v)
      case OpaqueInfo(v) => opaq(v)
      case QuotInfo(v)   => quot(v)
      case InductInfo(v) => inductOnly(v)
      case CtorInfo(v)   => ctorOnly(v)
      case RecInfo(v)    => recOnly(v)

  private def jsonDecl(key: String, body: String): Unit =
    if legacyJson && key != "inductive" then out(s"""{"$key":[$body]}""")
    else out(s"""{"$key":$body}""")

  private def axiom(v: AxiomVal): Unit =
    val cv = v.toConstantVal
    val n  = name(cv.name); val t = expr(cv.tpe); val ls = uparams(cv.levelParams)
    if isJson then
      jsonDecl("axiom", s"""{"name":$n,"levelParams":[${ls.mkString(",")}],"type":$t,"isUnsafe":${v.isUnsafe}}""")
    else out(s"#AX $n $t${tail(ls)}")

  private def defn(v: DefinitionVal): Unit =
    val cv = v.toConstantVal
    val n = name(cv.name); val t = expr(cv.tpe); val x = expr(v.value)
    val ls = uparams(cv.levelParams); val all = names(v.all)
    if isJson then
      val h = v.hints match
        case ReducibilityHints.Opaque      => "\"opaque\""
        case ReducibilityHints.Abbrev      => "\"abbrev\""
        case ReducibilityHints.Regular(hh) => s"""{"regular":$hh}"""
      val s = v.safety match
        case DefinitionSafety.Unsafe  => "unsafe"
        case DefinitionSafety.Safe    => "safe"
        case DefinitionSafety.Partial => "partial"
      jsonDecl("def", s"""{"name":$n,"levelParams":[${ls.mkString(",")}],"type":$t,"value":$x,"hints":$h,"safety":"$s","all":[${all.mkString(",")}]}""")
    else
      if format == TextV1 then out(s"#DEF $n $t $x${tail(ls)}")
      else
        val h = v.hints match
          case ReducibilityHints.Opaque      => "O"
          case ReducibilityHints.Abbrev      => "A"
          case ReducibilityHints.Regular(hh) => s"R $hh"
        out(s"#DEF $n $t $x $h${tail(ls)}")

  private def thm(v: TheoremVal): Unit =
    val cv = v.toConstantVal
    val n = name(cv.name); val t = expr(cv.tpe); val x = expr(v.value)
    val ls = uparams(cv.levelParams); val all = names(v.all)
    if isJson then
      jsonDecl("thm", s"""{"name":$n,"levelParams":[${ls.mkString(",")}],"type":$t,"value":$x,"all":[${all.mkString(",")}]}""")
    else if format == TextV1 then out(s"#DEF $n $t $x${tail(ls)}")
    else out(s"#THM $n $t $x${tail(ls)}")

  private def opaq(v: OpaqueVal): Unit =
    val cv = v.toConstantVal
    val n = name(cv.name); val t = expr(cv.tpe); val x = expr(v.value)
    val ls = uparams(cv.levelParams); val all = names(v.all)
    if isJson then
      jsonDecl("opaque", s"""{"name":$n,"levelParams":[${ls.mkString(",")}],"type":$t,"value":$x,"isUnsafe":${v.isUnsafe},"all":[${all.mkString(",")}]}""")
    else if format == TextV1 then out(s"#DEF $n $t $x${tail(ls)}")
    else out(s"#OPAQ $n $t $x${tail(ls)}")

  private def quot(v: QuotVal): Unit =
    val cv = v.toConstantVal
    val n = name(cv.name); val t = expr(cv.tpe); val ls = uparams(cv.levelParams)
    if isJson then
      val k = v.kind match
        case QuotKind.Type => "type"
        case QuotKind.Ctor => "ctor"
        case QuotKind.Lift => "lift"
        case QuotKind.Ind  => "ind"
      jsonDecl("quot", s"""{"name":$n,"levelParams":[${ls.mkString(",")}],"type":$t,"kind":"$k"}""")
    else if format == TextV1 then throw ExportException("the text v1 format has no per-declaration #QUOT")
    else out(s"#QUOT $n $t${tail(ls)}")

  private def inductiveValJson(v: InductiveVal): String =
    val cv = v.toConstantVal
    val n = name(cv.name); val t = expr(cv.tpe)
    val ls = uparams(cv.levelParams); val all = names(v.all); val cs = names(v.ctors)
    s"""{"name":$n,"levelParams":[${ls.mkString(",")}],"type":$t,"numParams":${v.numParams},""" +
      s""""numIndices":${v.numIndices},"all":[${all.mkString(",")}],"ctors":[${cs.mkString(",")}],""" +
      s""""numNested":${v.numNested},"isRec":${v.isRec},"isUnsafe":${v.isUnsafe},"isReflexive":${v.isReflexive}}"""

  private def ctorValJson(v: ConstructorVal): String =
    val cv = v.toConstantVal
    val n = name(cv.name); val t = expr(cv.tpe); val ind = name(v.induct); val ls = uparams(cv.levelParams)
    s"""{"name":$n,"levelParams":[${ls.mkString(",")}],"type":$t,"induct":$ind,"cidx":${v.cidx},""" +
      s""""numParams":${v.numParams},"numFields":${v.numFields},"isUnsafe":${v.isUnsafe}}"""

  private def recValJson(v: RecursorVal): String =
    val cv = v.toConstantVal
    val n = name(cv.name); val t = expr(cv.tpe); val ls = uparams(cv.levelParams); val all = names(v.all)
    val rs = v.rules.map(r => s"""{"ctor":${name(r.ctor)},"nfields":${r.nfields},"rhs":${expr(r.rhs)}}""")
    s"""{"name":$n,"levelParams":[${ls.mkString(",")}],"type":$t,"all":[${all.mkString(",")}],""" +
      s""""numParams":${v.numParams},"numIndices":${v.numIndices},"numMotives":${v.numMotives},""" +
      s""""numMinors":${v.numMinors},"rules":[${rs.mkString(",")}],"k":${v.k},"isUnsafe":${v.isUnsafe}}"""

  private def requireNotV1(what: String): Unit =
    if format == TextV1 then
      throw ExportException(s"the text v1 format does not carry $what as an environment entry")

  private def inductOnly(v: InductiveVal): Unit =
    requireNotV1("inductive types")
    if isJson then
      val (tk, ck, rk) =
        if legacyJson then ("inductiveVals", "constructorVals", "recursorVals") else ("types", "ctors", "recs")
      out(s"""{"inductive":{"$tk":[${inductiveValJson(v)}],"$ck":[],"$rk":[]}}""")
    else
      val cv = v.toConstantVal
      val n = name(cv.name); val t = expr(cv.tpe)
      val all = names(v.all); val cs = names(v.ctors); val ls = uparams(cv.levelParams)
      val r = if v.isReflexive then 1 else 0
      val rec = if v.isRec then 1 else 0
      out(
        s"#IND $n $t $r $rec ${v.numNested} ${v.numParams} ${v.numIndices} ${all.length}" +
          s"${tail(all)} ${v.ctors.length}${tail(cs)}${tail(ls)}"
      )

  private def ctorOnly(v: ConstructorVal): Unit =
    requireNotV1("constructors")
    if isJson then
      val (tk, ck, rk) =
        if legacyJson then ("inductiveVals", "constructorVals", "recursorVals") else ("types", "ctors", "recs")
      out(s"""{"inductive":{"$tk":[],"$ck":[${ctorValJson(v)}],"$rk":[]}}""")
    else
      val cv = v.toConstantVal
      val n = name(cv.name); val t = expr(cv.tpe); val ind = name(v.induct); val ls = uparams(cv.levelParams)
      out(s"#CTOR $n $t $ind ${v.cidx} ${v.numParams} ${v.numFields}${tail(ls)}")

  private def recOnly(v: RecursorVal): Unit =
    requireNotV1("recursors")
    if isJson then
      val (tk, ck, rk) =
        if legacyJson then ("inductiveVals", "constructorVals", "recursorVals") else ("types", "ctors", "recs")
      out(s"""{"inductive":{"$tk":[],"$ck":[],"$rk":[${recValJson(v)}]}}""")
    else
      val cv = v.toConstantVal
      val n = name(cv.name); val t = expr(cv.tpe)
      val all = names(v.all); val rs = v.rules.map(rule); val ls = uparams(cv.levelParams)
      val k = if v.k then 1 else 0
      out(
        s"#REC $n $t ${all.length}${tail(all)} ${v.numParams} ${v.numIndices} ${v.numMotives} " +
          s"${v.numMinors} ${v.rules.length}${tail(rs)} $k${tail(ls)}"
      )

object ExportWriter:

  def toLines(env: ExportEnv, format: ExportFormat): Vector[String] =
    val b = Vector.newBuilder[String]
    new ExportWriter(format, b += _).write(env)
    b.result()

  def toString(env: ExportEnv, format: ExportFormat): String =
    toLines(env, format).mkString("\n")

  private[leanexport] def hex(s: String): String =
    s.getBytes(java.nio.charset.StandardCharsets.UTF_8)
      .map(b => String.format("%02X", Integer.valueOf(b & 0xff)))
      .mkString(" ")

private[leanexport] object Jsonw:
  def str(s: String): String =
    val sb = new StringBuilder(s.length + 2)
    sb += '"'
    var i = 0
    while i < s.length do
      val c = s.charAt(i)
      c match
        case '"'  => sb ++= "\\\""
        case '\\' => sb ++= "\\\\"
        case '\n' => sb ++= "\\n"
        case '\r' => sb ++= "\\r"
        case '\t' => sb ++= "\\t"
        case '\b' => sb ++= "\\b"
        case '\f' => sb ++= "\\f"
        case _ =>
          if c < 0x20 then sb ++= f"\\u${c.toInt}%04x"
          else sb += c
      i += 1
    sb += '"'
    sb.result()
