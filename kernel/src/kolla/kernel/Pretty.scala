package kolla.kernel

import cats.Eval

object Pretty:

  val defaultMaxChars: Int = 2000

  def expr(e: Expr, maxChars: Int = defaultMaxChars): String =
    val sb = new StringBuilder
    go(e, 0, sb, maxChars).value
    if sb.length > maxChars then sb.take(maxChars).result() + "…" else sb.result()

  private def paren(prec: Int, at: Int, sb: StringBuilder, body: => Eval[Unit]): Eval[Unit] =
    if prec > at then
      sb += '('
      body.map { _ => sb += ')'; () }
    else body

  private def go(e: Expr, prec: Int, sb: StringBuilder, maxChars: Int): Eval[Unit] =
    if sb.length > maxChars then Eval.Unit
    else
      e match
        case b: Expr.BVar => sb ++= "#" ++= b.idx.toString; Eval.Unit
        case f: Expr.FVar => sb ++= "_f." ++= f.id.toString; Eval.Unit
        case m: Expr.MVar => sb ++= "?" ++= m.id.toString; Eval.Unit
        case s: Expr.Sort => sb ++= "Sort " ++= s.level.toString; Eval.Unit
        case c: Expr.Const =>
          sb ++= c.name.toString
          if c.levels.nonEmpty then sb ++= c.levels.mkString(".{", ", ", "}")
          Eval.Unit
        case l: Expr.Lit =>
          l.value match
            case Literal.NatVal(v) => sb ++= v.toString
            case Literal.StrVal(v) => sb += '"' ++= v ++= "\""
          Eval.Unit
        case a: Expr.App =>
          paren(prec, 1, sb,
            Eval.defer(go(a.fn, 1, sb, maxChars)).flatMap { _ =>
              sb += ' '
              Eval.defer(go(a.arg, 2, sb, maxChars))
            })
        case l: Expr.Lam =>
          paren(prec, 0, sb, {
            sb ++= "fun (" ++= l.binderName.toString ++= " : "
            Eval.defer(go(l.binderType, 0, sb, maxChars)).flatMap { _ =>
              sb ++= ") => "
              Eval.defer(go(l.body, 0, sb, maxChars))
            }
          })
        case f: Expr.ForallE =>
          paren(prec, 0, sb, {
            sb ++= "forall (" ++= f.binderName.toString ++= " : "
            Eval.defer(go(f.binderType, 0, sb, maxChars)).flatMap { _ =>
              sb ++= "), "
              Eval.defer(go(f.body, 0, sb, maxChars))
            }
          })
        case l: Expr.LetE =>
          paren(prec, 0, sb, {
            sb ++= "let " ++= l.declName.toString ++= " : "
            Eval.defer(go(l.tpe, 0, sb, maxChars)).flatMap { _ =>
              sb ++= " := "
              Eval.defer(go(l.value, 0, sb, maxChars)).flatMap { _ =>
                sb ++= "; "
                Eval.defer(go(l.body, 0, sb, maxChars))
              }
            }
          })
        case m: Expr.MData => Eval.defer(go(m.expr, prec, sb, maxChars))
        case p: Expr.Proj =>
          Eval.defer(go(p.struct, 2, sb, maxChars)).map { _ =>
            sb ++= "." ++= p.typeName.toString ++= "." ++= p.idx.toString
            ()
          }
