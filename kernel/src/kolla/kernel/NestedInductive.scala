package kolla.kernel

import scala.collection.mutable

/** The outcome of eliminating nested inductive occurrences, mirroring
  * `elim_nested_inductive_result` in `src/kernel/inductive.cpp`.
  */
final class ElimNestedResult(
    val ngen: NameGenerator,
    val params: Vector[Expr],
    val paramsLctx: LocalContext,
    /** auxiliary type name to the nested occurrence `I Ds` it stands for. */
    val aux2nested: Map[Name, Expr],
    val auxDecl: Declaration.InductDecl
):

  def numNested: Int = aux2nested.size

  private def fail(detail: String): Nothing =
    throw KernelException(ExceptionKind.InvalidDeclaration, s"failed to restore nested inductive types, $detail")

  /** `get_nested_if_aux_constructor`. */
  def nestedIfAuxConstructor(auxEnv: Environment, c: Name): Option[(Expr, Name)] =
    auxEnv.find(c) match
      case Some(ConstantInfo.CtorInfo(cv)) => aux2nested.get(cv.induct).map(n => (n, cv.induct))
      case _                               => None

  /** `restore_constructor_name`. */
  def restoreConstructorName(auxEnv: Environment, cnstrName: Name): Name =
    nestedIfAuxConstructor(auxEnv, cnstrName) match
      case None => fail(s"'$cnstrName' is not a constructor of an auxiliary type")
      case Some((nested, auxIName)) =>
        Expr.getAppFn(nested) match
          case i: Expr.Const => Name.replacePrefix(cnstrName, auxIName, i.name)
          case _             => fail("the nested occurrence is not an inductive type application")

  /** `restore_nested`: rewrites auxiliary types and their constructors back to
    * the nested occurrences they stand for, and renames auxiliary recursors.
    */
  def restoreNested(e0: Expr, auxEnv: Environment, auxRecNameMap: Map[Name, Name] = Map.empty): Expr =
    var lctx = LocalContext.empty
    val as   = mutable.ArrayBuffer.empty[Expr]
    val isPi = e0.isInstanceOf[Expr.ForallE]
    var e    = e0
    var i    = 0
    while i < params.length do
      val (bn, bt, bi, body) = e match
        case p: Expr.ForallE => (p.binderName, p.binderType, p.binderInfo, p.body)
        case l: Expr.Lam     => (l.binderName, l.binderType, l.binderInfo, l.body)
        case _               => fail("fewer binders than parameters")
      val (next, fvar) = lctx.mkLocalDecl(ngen, bn, bt, bi)
      lctx = next
      as += fvar
      e = ExprOps.instantiate1(body, fvar)
      i += 1

    /** Substitutes the declaration's parameters by the freshly made binders. */
    def toAs(x: Expr): Expr = ExprOps.instantiateRev(ExprOps.abstract_(x, params), as.toIndexedSeq)

    val rewritten = ExprOps.replace(e) { (t, _) =>
      t match
        case c: Expr.Const if auxRecNameMap.contains(c.name) =>
          Some(Expr.Const(auxRecNameMap(c.name), c.levels))
        case _ =>
          Expr.getAppFn(t) match
            case fn: Expr.Const =>
              aux2nested.get(fn.name) match
                case Some(nested) =>
                  val args = Expr.getAppArgs(t)
                  if args.length < params.length then
                    fail("an auxiliary type is not applied to all parameters")
                  Some(Expr.mkAppRange(toAs(nested), args, params.length, args.length))
                case None =>
                  nestedIfAuxConstructor(auxEnv, fn.name) match
                    case Some((nested, auxIName)) =>
                      val args = Expr.getAppArgs(t)
                      if args.length < params.length then
                        fail("an auxiliary constructor is not applied to all parameters")
                      val newNested = toAs(nested)
                      val iArgs     = Expr.getAppArgs(newNested)
                      Expr.getAppFn(newNested) match
                        case iConst: Expr.Const =>
                          val newFnName = Name.replacePrefix(fn.name, auxIName, iConst.name)
                          val newFn     = Expr.Const(newFnName, iConst.levels)
                          Some(
                            Expr.mkAppRange(Expr.mkAppN(newFn, iArgs), args, params.length, args.length)
                          )
                        case _ => fail("the nested occurrence is not an inductive type application")
                    case None => None
            case _ => None
    }
    if isPi then lctx.mkPi(as.toIndexedSeq, rewritten) else lctx.mkLambda(as.toIndexedSeq, rewritten)

/** `elim_nested_inductive_fn`.
  *
  * For each nested occurrence `I Ds is`, where `I` is an already declared
  * inductive whose parametric arguments mention a type being declared, an
  * auxiliary type `Iaux` is added to the mutual block and the occurrence is
  * replaced by `Iaux As is`, where `As` are the block's own parameters. Every
  * type in `I`'s mutual block is copied, not just `I`.
  */
final class ElimNestedInductive(env: Environment, decl: Declaration.InductDecl):

  private val ngen       = new NameGenerator(Name.mkSimple("_nested_fresh"))
  private val lvls       = Level.paramsToLevels(decl.levelParams)
  private val newTypes   = mutable.ArrayBuffer.from(decl.types)
  private val nestedAux  = mutable.ArrayBuffer.empty[(Expr, Name)]
  private var nextIdx    = 1
  private var paramsLctx = LocalContext.empty
  private val params     = mutable.ArrayBuffer.empty[Expr]

  private def illFormed: Nothing =
    throw KernelException(ExceptionKind.InvalidDeclaration, "invalid nested inductive datatype, ill-formed declaration")

  private def mkUniqueName(n: Name): Name =
    var r = Name.appendIndexAfter(n, nextIdx)
    nextIdx += 1
    while env.contains(r) do
      r = Name.appendIndexAfter(n, nextIdx)
      nextIdx += 1
    r

  /** `replace_params`: substitutes `as` by the declaration's parameters. */
  private def replaceParams(e: Expr, as: IndexedSeq[Expr]): Expr =
    ExprOps.instantiateRev(ExprOps.abstract_(e, as), params.toIndexedSeq)

  /** `is_nested_inductive_app`. */
  private def isNestedInductiveApp(e: Expr): Option[InductiveVal] =
    if !e.isInstanceOf[Expr.App] then None
    else
      Expr.getAppFn(e) match
        case fn: Expr.Const =>
          env.find(fn.name) match
            case Some(ConstantInfo.InductInfo(iv)) =>
              val args = Expr.getAppArgs(e)
              if iv.numParams > args.length then None
              else
                var isNested   = false
                var looseBVars = false
                (0 until iv.numParams).foreach { i =>
                  val a = args(i)
                  if a.hasLooseBVars then looseBVars = true
                  var hit = false
                  ExprOps.forEach(a) { (t, _) =>
                    if hit then false
                    else
                      t match
                        case c: Expr.Const if newTypes.exists(_.name == c.name) => hit = true; false
                        case _                                                  => true
                  }
                  if hit then isNested = true
                }
                if !isNested then None
                else if looseBVars then
                  throw KernelException(
                    ExceptionKind.InvalidDeclaration,
                    fn.name,
                    "invalid nested inductive datatype, the parameters of a nested inductive datatype cannot contain local variables"
                  )
                else Some(iv)
            case _ => None
        case _ => None

  /** `instantiate_pi_params`: drops `nparams` binders and substitutes them. */
  private def instantiatePiParams(e0: Expr, nparams: Int, args: IndexedSeq[Expr]): Expr =
    var e = e0
    var i = 0
    while i < nparams do
      e = e match
        case p: Expr.ForallE => p.body
        case _               => illFormed
      i += 1
    ExprOps.instantiateRev(e, args.slice(0, nparams))

  /** `replace_if_nested`. */
  private def replaceIfNested(lctx: LocalContext, as: IndexedSeq[Expr], e: Expr): Option[Expr] =
    isNestedInductiveApp(e).flatMap { iVal =>
      val args     = Expr.getAppArgs(e)
      val fn       = Expr.getAppFn(e).asInstanceOf[Expr.Const]
      val iName    = fn.name
      val iLvls    = fn.levels
      val iNparams = iVal.numParams
      val iAs      = Expr.mkAppRange(fn, args, 0, iNparams)
      // The parameters are rebuilt per constructor to preserve binder info, so
      // the lookup key is stated in terms of the declaration's parameters.
      val iParams  = replaceParams(iAs, as)
      nestedAux.find((k, _) => k == iParams).map(_._2) match
        case Some(auxIName) =>
          val auxI = Expr.mkAppN(Expr.Const(auxIName, lvls), as)
          Some(Expr.mkAppRange(auxI, args, iNparams, args.length))
        case None =>
          var result: Option[Expr] = None
          // Every type of `I`'s mutual block is copied, not only `I`.
          iVal.all.foreach { jName =>
            val jInfo    = env.get(jName)
            val j        = Expr.Const(jName, iLvls)
            val jAs      = Expr.mkAppRange(j, args, 0, iNparams)
            val auxJName = mkUniqueName(Name.append(Names.nested, jName))
            var auxJType = ExprOps.instantiateLevelParams(jInfo.tpe, jInfo.levelParams, iLvls)
            auxJType = instantiatePiParams(auxJType, iNparams, args)
            auxJType = lctx.mkPi(as, auxJType)
            nestedAux += ((replaceParams(jAs, as), auxJName))
            if jName == iName then
              val auxI = Expr.mkAppN(Expr.Const(auxJName, lvls), as)
              result = Some(Expr.mkAppRange(auxI, args, iNparams, args.length))
            val jVal = jInfo.asInstanceOf[ConstantInfo.InductInfo].value
            val auxCtors = jVal.ctors.map { jCtorName =>
              val jCtorInfo    = env.get(jCtorName)
              val auxJCtorName = Name.replacePrefix(jCtorName, jName, auxJName)
              // The type still mentions `J`; that occurrence is rewritten when
              // this auxiliary type is processed by the main loop.
              var auxJCtorType =
                ExprOps.instantiateLevelParams(jCtorInfo.tpe, jCtorInfo.levelParams, iLvls)
              auxJCtorType = instantiatePiParams(auxJCtorType, iNparams, args)
              auxJCtorType = lctx.mkPi(as, auxJCtorType)
              Constructor(auxJCtorName, auxJCtorType)
            }
            newTypes += InductiveType(auxJName, auxJType, auxCtors)
          }
          if result.isEmpty then illFormed
          result
    }

  private def replaceAllNested(lctx: LocalContext, as: IndexedSeq[Expr], e: Expr): Expr =
    ExprOps.replace(e)((t, _) => replaceIfNested(lctx, as, t))

  /** `get_params`. */
  private def getParams(type0: Expr, nparams: Int, lctx0: LocalContext): (Expr, LocalContext, Vector[Expr]) =
    var lctx = lctx0
    val out  = mutable.ArrayBuffer.empty[Expr]
    var t    = type0
    var i    = 0
    while i < nparams do
      t match
        case p: Expr.ForallE =>
          val (next, fvar) = lctx.mkLocalDecl(ngen, p.binderName, p.binderType, p.binderInfo)
          lctx = next
          out += fvar
          t = ExprOps.instantiate1(p.body, fvar)
        case _ =>
          throw KernelException(
            ExceptionKind.InvalidDeclaration,
            "invalid inductive datatype declaration, incorrect number of parameters"
          )
      i += 1
    (t, lctx, out.toVector)

  def apply(): ElimNestedResult =
    val dNparams = decl.numParams
    if newTypes.isEmpty then
      throw KernelException(
        ExceptionKind.InvalidDeclaration,
        "invalid empty (mutual) inductive datatype declaration, it must contain at least one inductive type"
      )
    val (_, pLctx, ps) = getParams(newTypes(0).tpe, dNparams, paramsLctx)
    paramsLctx = pLctx
    params ++= ps

    var qhead = 0
    while qhead < newTypes.length do
      val indType = newTypes(qhead)
      val newCtors = indType.ctors.map { ctor =>
        // The parameters are re-made per constructor so that each one keeps its
        // own binder info.
        val (ctorType, lctx, as) = getParams(ctor.tpe, dNparams, LocalContext.empty)
        val replaced = replaceAllNested(lctx, as, ctorType)
        Constructor(ctor.name, lctx.mkPi(as, replaced))
      }
      newTypes(qhead) = InductiveType(indType.name, indType.tpe, newCtors)
      qhead += 1

    new ElimNestedResult(
      ngen,
      params.toVector,
      paramsLctx,
      nestedAux.map((nested, aux) => aux -> nested).toMap,
      Declaration.InductDecl(decl.levelParams, decl.numParams, newTypes.toList, decl.isUnsafe)
    )

object ElimNestedInductive:

  /** `mk_aux_rec_name_map`: the auxiliary recursors are renamed
    * `<main type>.rec_1`, `<main type>.rec_2`, ...
    */
  def auxRecNameMap(auxEnv: Environment, decl: Declaration.InductDecl): (List[Name], Map[Name, Name]) =
    val ntypes   = decl.types.length
    val mainName = decl.types.head.name
    val allNames = auxEnv.get(mainName) match
      case ConstantInfo.InductInfo(v) => v.all
      case _ =>
        throw KernelException(ExceptionKind.InvalidDeclaration, mainName, "expected an inductive type")
    val oldRecNames = List.newBuilder[Name]
    val recMap      = Map.newBuilder[Name, Name]
    var nextIdx     = 1
    allNames.zipWithIndex.foreach { (indName, i) =>
      if i >= ntypes then
        val old = Names.recName(indName)
        val nw  = Name.appendIndexAfter(Names.recName(mainName), nextIdx)
        nextIdx += 1
        oldRecNames += old
        recMap += (old -> nw)
    }
    (oldRecNames.result(), recMap.result())
