package kolla.dsl

import kolla.kernel.{BinderInfo, Expr as LExpr, KVMap, Level, Literal as LLit, Name}
import scala.quoted.*

/** The `lean"..."` interpolator.
  *
  * The string is parsed at compile time by `LeanParser`, so a syntax error is a
  * compile error, and the resulting term is emitted as `Expr` construction
  * code. `${...}` holes splice a Scala value of type `Expr`, `Level` or `Name`.
  *
  * {{{
  * val id = lean"fun (A : Sort u) (a : A) => a"
  * val ap = lean"Nat.add ${two} 3"
  * }}}
  *
  * A spliced `Expr` is inserted unchanged, so it must be closed: the
  * interpolator has no way to refer to an enclosing binder from Scala.
  */
object LeanInterpolator:

  extension (inline sc: StringContext)
    inline def lean(inline args: Any*): LExpr = ${ leanImpl('sc, 'args) }

  private def leanImpl(sc: Expr[StringContext], args: Expr[Seq[Any]])(using Quotes): Expr[LExpr] =
    import quotes.reflect.*
    val parts: Seq[String] = sc match
      case '{ StringContext.apply(${ Varargs(ps) }*) } =>
        ps.map {
          case '{ $s: String } =>
            s.value.getOrElse(report.errorAndAbort("lean\"\" needs literal string parts", s))
          case other => report.errorAndAbort("lean\"\" needs literal string parts", other)
        }
      case _ => report.errorAndAbort("lean\"\" must be applied to a literal string", sc)

    val argExprs: Seq[Expr[Any]] = args match
      case Varargs(as) => as
      case _ => report.errorAndAbort("lean\"\" arguments must be given directly", args)

    if parts.length != argExprs.length + 1 then
      report.errorAndAbort("lean\"\": mismatched parts and arguments", sc)

    // Each hole becomes `$i`, which the parser turns into a marker the lifter
    // replaces with the corresponding argument.
    val source = parts.head + parts.tail.zipWithIndex.map((p, i) => s"$$$i$p").mkString

    val parsed = LeanParser.parse(source) match
      case Right(e) => e
      case Left(err) =>
        report.errorAndAbort(s"lean\"\" syntax error: ${err.message} (offset ${err.offset}) in: $source", sc)

    new Lifter(argExprs).expr(parsed)

  /** Emits construction code for a parsed term, substituting the splices. */
  private final class Lifter(args: Seq[Expr[Any]])(using Quotes):
    import quotes.reflect.report

    def name(n: Name): Expr[Name] =
      val s = Expr(n.toString)
      if n.isAnonymous then '{ Name.anonymous }
      else
        // Rebuild from the components so a numeral component survives.
        n.components.foldLeft[Expr[Name]]('{ Name.anonymous }) { (acc, c) =>
          c match
            case st: Name.Str => '{ $acc.str(${ Expr(st.value) }) }
            case nu: Name.Num => '{ $acc.num(BigInt(${ Expr(nu.value.toString) })) }
            case _            => acc
        }

    def level(l: Level): Expr[Level] = l match
      case p: Level.Param => '{ Level.Param(${ name(p.name) }) }
      case p: Level.MVar  => '{ Level.MVar(${ name(p.name) }) }
      case s: Level.Succ  => '{ Level.Succ(${ level(s.level) }) }
      case m: Level.Max   => '{ Level.Max(${ level(m.lhs) }, ${ level(m.rhs) }) }
      case m: Level.IMax  => '{ Level.IMax(${ level(m.lhs) }, ${ level(m.rhs) }) }
      case _              => '{ Level.zero }

    private def binderInfo(bi: BinderInfo): Expr[BinderInfo] = bi match
      case BinderInfo.Default        => '{ BinderInfo.Default }
      case BinderInfo.Implicit       => '{ BinderInfo.Implicit }
      case BinderInfo.StrictImplicit => '{ BinderInfo.StrictImplicit }
      case BinderInfo.InstImplicit   => '{ BinderInfo.InstImplicit }

    private def splice(i: Int): Expr[LExpr] =
      if i >= args.length then
        report.errorAndAbort(s"lean\"\": splice $i has no argument")
      args(i) match
        case '{ $e: LExpr } => e
        case '{ $l: Level }             => '{ LExpr.Sort($l) }
        case '{ $n: Name }              => '{ LExpr.Const($n, Nil) }
        case other =>
          report.errorAndAbort(
            "lean\"\" splices must be an Expr, a Level or a Name",
            other
          )

    def expr(e: LExpr): Expr[LExpr] =
      LeanParser.spliceIndex(e) match
        case Some(i) => splice(i)
        case None =>
          e match
            case b: LExpr.BVar => '{ LExpr.BVar(${ Expr(b.idx) }) }
            case s: LExpr.Sort => '{ LExpr.Sort(${ level(s.level) }) }
            case c: LExpr.Const =>
              val ls = c.levels.map(level)
              '{ LExpr.Const(${ name(c.name) }, ${ Expr.ofList(ls) }) }
            case a: LExpr.App =>
              '{ LExpr.App(${ expr(a.fn) }, ${ expr(a.arg) }) }
            case l: LExpr.Lam =>
              '{
                LExpr.Lam(
                  ${ name(l.binderName) }, ${ expr(l.binderType) }, ${ expr(l.body) },
                  ${ binderInfo(l.binderInfo) }
                )
              }
            case f: LExpr.ForallE =>
              '{
                LExpr.ForallE(
                  ${ name(f.binderName) }, ${ expr(f.binderType) }, ${ expr(f.body) },
                  ${ binderInfo(f.binderInfo) }
                )
              }
            case l: LExpr.LetE =>
              '{
                LExpr.LetE(
                  ${ name(l.declName) }, ${ expr(l.tpe) }, ${ expr(l.value) }, ${ expr(l.body) },
                  ${ Expr(l.nondep) }
                )
              }
            case p: LExpr.Proj =>
              '{ LExpr.Proj(${ name(p.typeName) }, ${ Expr(p.idx) }, ${ expr(p.struct) }) }
            case l: LExpr.Lit =>
              l.value match
                case LLit.NatVal(v) =>
                  '{ LExpr.natLit(BigInt(${ Expr(v.toString) })) }
                case LLit.StrVal(v) => '{ LExpr.strLit(${ Expr(v) }) }
            case m: LExpr.MData =>
              '{ LExpr.MData(KVMap.empty, ${ expr(m.expr) }) }
            case other =>
              report.errorAndAbort(s"lean\"\" cannot emit ${other.getClass.getSimpleName}")
