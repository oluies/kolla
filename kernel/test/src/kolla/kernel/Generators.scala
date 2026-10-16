package kolla.kernel

import org.scalacheck.{Arbitrary, Gen}

object Generators:

  val paramNames: Vector[Name] = Vector("u", "v", "w").map(Name.mkSimple)

  val genNameComponent: Gen[String] =
    Gen.oneOf("a", "b", "Nat", "foo", "List", "_x", "α", "mk")

  val genName: Gen[Name] =
    for
      n  <- Gen.choose(0, 3)
      cs <- Gen.listOfN(n, Gen.oneOf(genNameComponent.map(Left(_)), Gen.choose(0, 5).map(Right(_))))
    yield cs.foldLeft(Name.anonymous) {
      case (acc, Left(s))  => acc.str(s)
      case (acc, Right(i)) => acc.num(i)
    }

  def genLevel(size: Int): Gen[Level] =
    if size <= 0 then
      Gen.oneOf(
        Gen.const(Level.zero),
        Gen.choose(0, 3).map(Level.ofNat),
        Gen.oneOf(paramNames).map(Level.Param(_)),
        Gen.oneOf(paramNames).map(Level.MVar(_))
      ).flatMap(identity)
    else
      Gen.frequency(
        2 -> genLevel(0),
        2 -> genLevel(size - 1).map(Level.Succ(_)),
        2 -> Gen.zip(genLevel(size - 1), genLevel(size - 1)).map((a, b) => Level.Max(a, b)),
        2 -> Gen.zip(genLevel(size - 1), genLevel(size - 1)).map((a, b) => Level.IMax(a, b))
      )

  def genLevelNoIMax(size: Int): Gen[Level] =
    if size <= 0 then genLevel(0)
    else
      Gen.frequency(
        2 -> genLevelNoIMax(0),
        2 -> genLevelNoIMax(size - 1).map(Level.Succ(_)),
        3 -> Gen.zip(genLevelNoIMax(size - 1), genLevelNoIMax(size - 1)).map((a, b) => Level.Max(a, b))
      )

  /** Levels built without `imax`. */
  final case class NoIMax(level: Level)

  given Arbitrary[NoIMax] = Arbitrary(Gen.choose(0, 4).flatMap(genLevelNoIMax).map(NoIMax(_)))

  given Arbitrary[Level] = Arbitrary(Gen.choose(0, 4).flatMap(genLevel))
  given Arbitrary[Name]  = Arbitrary(genName)

  def genExpr(size: Int): Gen[Expr] =
    if size <= 0 then
      Gen.oneOf(
        Gen.choose(0, 3).map(Expr.BVar(_)),
        genName.map(Expr.FVar(_)),
        genName.map(Expr.MVar(_)),
        genLevel(1).map(Expr.Sort(_)),
        Gen.zip(genName, Gen.listOfN(1, genLevel(1))).map((n, ls) => Expr.Const(n, ls)),
        Gen.choose(0, 100).map(i => Expr.natLit(BigInt(i))),
        Gen.alphaStr.map(Expr.strLit)
      ).flatMap(identity)
    else
      Gen.frequency(
        3 -> genExpr(0),
        3 -> Gen.zip(genExpr(size - 1), genExpr(size - 1)).map((f, a) => Expr.App(f, a)),
        2 -> Gen.zip(genName, genExpr(size - 1), genExpr(size - 1)).map((n, t, b) => Expr.Lam(n, t, b, BinderInfo.Default)),
        2 -> Gen.zip(genName, genExpr(size - 1), genExpr(size - 1)).map((n, t, b) => Expr.ForallE(n, t, b, BinderInfo.Default)),
        1 -> Gen.zip(genName, genExpr(size - 1), genExpr(size - 1), genExpr(size - 1)).map((n, t, v, b) => Expr.LetE(n, t, v, b, false)),
        1 -> Gen.zip(genName, Gen.choose(0, 3), genExpr(size - 1)).map((n, i, e) => Expr.Proj(n, i, e))
      )

  given Arbitrary[Expr] = Arbitrary(Gen.choose(0, 3).flatMap(genExpr))
