package kolla.leanexport

import kolla.kernel.*

object Fixtures:

  val u: Name    = Name.mkSimple("u")
  val v: Name    = Name.mkSimple("v")
  val nat: Name  = Name.parse("Nat")
  val zero: Name = Name.parse("Nat.zero")
  val succ: Name = Name.parse("Nat.succ")
  val natRec: Name = Name.parse("Nat.rec")

  val lu: Level = Level.Param(u)
  val lv: Level = Level.Param(v)

  val natC: Expr   = Expr.Const(nat, Nil)
  val sortU: Expr  = Expr.Sort(lu)
  val prop: Expr   = Expr.Sort(Level.zero)

  /** Exercises every expression constructor the text formats can carry. */
  val kitchenSink: Expr =
    Expr.Lam(
      Name.mkSimple("x"),
      natC,
      Expr.LetE(
        Name.mkSimple("y"),
        Expr.Sort(Level.Max(lu, Level.Succ(lv))),
        Expr.App(Expr.Const(succ, Nil), Expr.natLit(BigInt("123456789012345678901234567890"))),
        Expr.App(
          Expr.App(
            Expr.ForallE(Name.anonymous.num(3), Expr.Sort(Level.IMax(lu, lv)), Expr.BVar(2), BinderInfo.InstImplicit),
            Expr.Proj(nat, 1, Expr.BVar(0))
          ),
          Expr.strLit("héllo wörld")
        ),
        false
      ),
      BinderInfo.StrictImplicit
    )

  val axiomItem: ExportItem = ExportItem.Info(ConstantInfo.AxiomInfo(
    AxiomVal(ConstantVal(Name.parse("Classical.choice"), List(u), Expr.Sort(lu)), false)
  ))

  def defnItem(hints: ReducibilityHints, name: String = "Nat.add"): ExportItem =
    val n = Name.parse(name)
    ExportItem.Info(ConstantInfo.DefnInfo(DefinitionVal(
      ConstantVal(n, Nil, Expr.ForallE(Name.mkSimple("a"), natC, natC, BinderInfo.Default)),
      kitchenSink, hints, DefinitionSafety.Safe, List(n)
    )))

  val thmItem: ExportItem =
    val n = Name.parse("Nat.add_comm")
    ExportItem.Info(ConstantInfo.ThmInfo(TheoremVal(
      ConstantVal(n, Nil, prop), Expr.Const(zero, Nil), List(n)
    )))

  val opaqueItem: ExportItem =
    val n = Name.parse("Foo.op")
    ExportItem.Info(ConstantInfo.OpaqueInfo(OpaqueVal(
      ConstantVal(n, List(u), Expr.Sort(lu)), Expr.Sort(lu), false, List(n)
    )))

  val quotItems: List[ExportItem] = List(
    QuotKind.Type -> "Quot",
    QuotKind.Ctor -> "Quot.mk",
    QuotKind.Lift -> "Quot.lift",
    QuotKind.Ind  -> "Quot.ind"
  ).map { (k, n) =>
    ExportItem.Info(ConstantInfo.QuotInfo(QuotVal(
      ConstantVal(Name.parse(n), List(u), Expr.Sort(lu)), k
    )))
  }

  val inductItem: ExportItem = ExportItem.Info(ConstantInfo.InductInfo(InductiveVal(
    ConstantVal(nat, Nil, Expr.Sort(Level.one)),
    numParams = 0, numIndices = 0, all = List(nat), ctors = List(zero, succ),
    numNested = 0, isRec = true, isUnsafe = false, isReflexive = false
  )))

  val ctorItems: List[ExportItem] = List(
    ExportItem.Info(ConstantInfo.CtorInfo(ConstructorVal(
      ConstantVal(zero, Nil, natC), nat, 0, 0, 0, false
    ))),
    ExportItem.Info(ConstantInfo.CtorInfo(ConstructorVal(
      ConstantVal(succ, Nil, Expr.ForallE(Name.mkSimple("n"), natC, natC, BinderInfo.Default)), nat, 1, 0, 1, false
    )))
  )

  val recItem: ExportItem = ExportItem.Info(ConstantInfo.RecInfo(RecursorVal(
    ConstantVal(natRec, List(u), Expr.Sort(lu)),
    all = List(nat), numParams = 0, numIndices = 0, numMotives = 1, numMinors = 2,
    rules = List(
      RecursorRule(zero, 0, Expr.BVar(1)),
      RecursorRule(succ, 1, Expr.App(Expr.BVar(0), Expr.BVar(1)))
    ),
    k = false, isUnsafe = false
  )))

  /** Every item kind the text v2 and NDJSON formats can carry. */
  val richItems: Vector[ExportItem] = Vector(
    inductItem
  ) ++ ctorItems ++ Vector(
    recItem,
    axiomItem,
    defnItem(ReducibilityHints.Regular(7)),
    defnItem(ReducibilityHints.Abbrev, "Nat.abbrev"),
    defnItem(ReducibilityHints.Opaque, "Nat.opaqueDef"),
    thmItem,
    opaqueItem
  ) ++ quotItems

  val richEnv: ExportEnv = ExportEnv(ExportFormat.TextV2, None, richItems)

  /** Items the text v1 format can carry. */
  val v1Items: Vector[ExportItem] = Vector(
    ExportItem.Decl(Declaration.InductDecl(
      Nil, 0,
      List(InductiveType(nat, Expr.Sort(Level.one), List(
        Constructor(zero, natC),
        Constructor(succ, Expr.ForallE(Name.mkSimple("n"), natC, natC, BinderInfo.Default))
      ))),
      false
    )),
    ExportItem.Decl(Declaration.QuotDecl),
    axiomItem,
    ExportItem.DefnWithoutHints(Name.parse("Nat.add"), Nil, Expr.ForallE(Name.mkSimple("a"), natC, natC, BinderInfo.Default), kitchenSink)
  )

  val v1Env: ExportEnv = ExportEnv(ExportFormat.TextV1, None, v1Items)

  // ----------------------------------------------- hand-written literal files

  /** Text v1, written against `dumpConstant` in lean4export at the Lean v4.12.0
    * commit, including the trailing space the exporter leaves after `#EC`.
    */
  val textV1Literal: String =
    """1 #NS 0 Nat
      |2 #NS 0 x
      |3 #NS 1 add
      |4 #NS 1 zero
      |1 #US 0
      |0 #EC 1 
      |1 #EV 0
      |2 #EP #BD 2 0 1
      |3 #ES 1
      |#AX 1 0
      |#DEF 3 2 1
      |#QUOT
      |#IND 0 1 3 1 4 0""".stripMargin

  /** Text v2, written against `dumpConstant` in lean4export at commit 3245035. */
  val textV2Literal: String =
    """1 #NS 0 Nat
      |2 #NS 0 u
      |3 #NS 1 zero
      |4 #NS 1 succ
      |5 #NS 1 rec
      |6 #NS 0 Quot
      |7 #NS 1 add
      |8 #NS 0 n
      |9 #NS 0 ax
      |10 #NS 0 thm1
      |11 #NS 0 opq
      |1 #UP 2
      |2 #US 0
      |0 #EC 1
      |1 #ES 1
      |2 #EV 0
      |3 #ES 2
      |4 #EP #BD 8 0 0
      |#IND 1 3 0 1 0 0 0 1 1 2 3 4
      |#CTOR 3 0 1 0 0 0
      |#CTOR 4 4 1 1 0 1
      |0 #RR 3 0 2
      |1 #RR 4 1 2
      |#REC 5 1 1 1 0 0 1 2 2 0 1 0 2
      |#AX 9 1 2
      |#DEF 7 4 2 R 3
      |#THM 10 0 2
      |#OPAQ 11 1 2 2
      |#QUOT 6 1 2""".stripMargin

  val ndjson310Literal: String =
    """{"meta":{"exporter":{"name":"lean4export","version":"3.1.0"},"format":{"version":"3.1.0"},"lean":{"githash":"abc","version":"4.35.0"}}}
      |{"in":1,"str":{"pre":0,"str":"Nat"}}
      |{"ie":0,"const":{"name":1,"us":[]}}
      |{"in":2,"str":{"pre":0,"str":"u"}}
      |{"il":1,"param":2}
      |{"il":2,"succ":1}
      |{"il":3,"max":[1,2]}
      |{"il":4,"imax":[1,2]}
      |{"ie":1,"sort":3}
      |{"ie":2,"bvar":0}
      |{"ie":3,"natVal":"123456789012345678901234567890"}
      |{"ie":4,"strVal":"héllo"}
      |{"ie":5,"app":{"fn":0,"arg":3}}
      |{"ie":6,"lam":{"name":2,"type":0,"body":2,"binderInfo":"strictImplicit"}}
      |{"ie":7,"forallE":{"name":2,"type":0,"body":2,"binderInfo":"instImplicit"}}
      |{"ie":8,"letE":{"name":2,"type":0,"value":3,"body":2,"nondep":true}}
      |{"ie":9,"proj":{"typeName":1,"idx":2,"struct":0}}
      |{"ie":10,"mdata":{"expr":0,"data":{"x":1}}}
      |{"in":3,"num":{"pre":1,"i":7}}
      |{"axiom":{"name":1,"levelParams":[2],"type":1,"isUnsafe":false}}
      |{"def":{"name":3,"levelParams":[],"type":0,"value":5,"hints":{"regular":4},"safety":"safe","all":[3]}}
      |{"thm":{"name":3,"levelParams":[],"type":0,"value":5,"all":[3]}}
      |{"opaque":{"name":3,"levelParams":[],"type":0,"value":5,"isUnsafe":true,"all":[3]}}
      |{"quot":{"name":1,"levelParams":[2],"type":1,"kind":"lift"}}""".stripMargin

  val ndjson300Literal: String =
    """{"meta":{"exporter":{"name":"lean4export","version":"3.0.0"},"format":{"version":"3.0.0"},"lean":{"githash":"abc","version":"4.27.0-rc1"}}}
      |{"in":1,"str":{"pre":0,"str":"Nat"}}
      |{"il":1,"succ":0}
      |{"ie":0,"sort":1}
      |{"ie":1,"const":{"name":1,"us":[]}}
      |{"in":2,"str":{"pre":1,"str":"zero"}}
      |{"in":3,"str":{"pre":1,"str":"succ"}}
      |{"in":4,"str":{"pre":1,"str":"rec"}}
      |{"in":5,"str":{"pre":0,"str":"u"}}
      |{"ie":2,"bvar":0}
      |{"ie":3,"forallE":{"name":2,"type":1,"body":1,"binderInfo":"default"}}
      |{"inductive":{"inductiveVals":[{"name":1,"levelParams":[],"type":0,"numParams":0,"numIndices":0,"all":[1],"ctors":[2,3],"numNested":0,"isRec":true,"isUnsafe":false,"isReflexive":false}],"constructorVals":[{"name":2,"levelParams":[],"type":1,"induct":1,"cidx":0,"numParams":0,"numFields":0,"isUnsafe":false},{"name":3,"levelParams":[],"type":3,"induct":1,"cidx":1,"numParams":0,"numFields":1,"isUnsafe":false}],"recursorVals":[{"name":4,"levelParams":[5],"type":0,"all":[1],"numParams":0,"numIndices":0,"numMotives":1,"numMinors":2,"rules":[{"ctor":2,"nfields":0,"rhs":2},{"ctor":3,"nfields":1,"rhs":2}],"k":false,"isUnsafe":false}]}}
      |{"def":[{"name":5,"levelParams":[],"type":1,"value":2,"hints":"abbrev","safety":"safe","all":[5]}]}
      |{"thm":[{"name":5,"levelParams":[],"type":1,"value":2,"all":[5]}]}""".stripMargin
