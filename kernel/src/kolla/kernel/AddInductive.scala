package kolla.kernel

import scala.collection.mutable

/** The result of adding one inductive declaration: the extended environment and
  * the entries the kernel derived, with nested occurrences restored.
  */
final case class AddInductiveResult(
    env: Environment,
    inductives: List[InductiveVal],
    constructors: List[ConstructorVal],
    recursors: List[RecursorVal],
    numNested: Int
)

/** `environment::add_inductive` (`src/kernel/inductive.cpp`).
  *
  * Nested occurrences are eliminated into auxiliary types, the resulting
  * nested-free block is checked by `InductiveChecker`, and the auxiliary types
  * are then restored in the constructor and recursor types that mention them.
  */
object AddInductive:

  def add(
      env: Environment,
      decl: Declaration.InductDecl,
      profile: KernelProfile = KernelProfile.default,
      /** The reduction budget, forwarded so `--max-steps` applies to an
        * inductive block as it does to any other declaration (K21).
        */
      maxSteps: Long = TypeChecker.defaultMaxSteps
  ): AddInductiveResult =
    // Reject metavariables, free variables and references to auxiliary types.
    decl.types.foreach { t =>
      checkNoMetavarNoFvar(t.name, t.tpe)
      t.ctors.foreach(c => checkNoMetavarNoFvar(c.name, c.tpe))
    }
    InductiveChecker.checkNoNestedAux(decl)
    if profile.checkUniformIndOccs then InductiveChecker.checkUniformIndOccs(decl)

    val res      = new ElimNestedInductive(env, decl).apply()
    val nnested  = res.numNested
    val auxCheck = new InductiveChecker(env, res.auxDecl, profile, nnested, maxSteps).run()

    if nnested == 0 then
      AddInductiveResult(auxCheck.env, auxCheck.inductives, auxCheck.constructors, auxCheck.recursors, 0)
    else restore(env, decl, profile, res, auxCheck.env, maxSteps)

  private def checkNoMetavarNoFvar(n: Name, e: Expr): Unit =
    if e.hasExprMVar then
      throw KernelException(ExceptionKind.DeclarationHasMetavars, n, "the declaration contains metavariables")
    if e.hasFVar then
      throw KernelException(ExceptionKind.DeclarationHasFreeVars, n, "the declaration contains free variables")

  private def restore(
      env0: Environment,
      decl: Declaration.InductDecl,
      profile: KernelProfile,
      res: ElimNestedResult,
      auxEnv: Environment,
      maxSteps: Long
  ): AddInductiveResult =
    val safety     = if decl.isUnsafe then DefinitionSafety.Unsafe else DefinitionSafety.Safe
    val allIndNames = decl.types.map(_.name)
    val (auxRecNames, recMap) = ElimNestedInductive.auxRecNameMap(auxEnv, decl)

    // The restored declarations go into the original environment, not the
    // auxiliary one, so no auxiliary type can leak out.
    var newEnv      = env0
    val inductives  = mutable.ArrayBuffer.empty[InductiveVal]
    val constructors = mutable.ArrayBuffer.empty[ConstructorVal]
    val recursors   = mutable.ArrayBuffer.empty[RecursorVal]
    val newRecNames = mutable.ArrayBuffer.empty[Name]

    def processRec(recName: Name): Unit =
      val newRecName = recMap.getOrElse(recName, recName)
      val recInfo = auxEnv.get(recName) match
        case ConstantInfo.RecInfo(v) => v
        case _ =>
          throw KernelException(ExceptionKind.InvalidDeclaration, recName, "expected a recursor")
      val cv          = recInfo.toConstantVal
      val newRecType  = res.restoreNested(cv.tpe, auxEnv, recMap)
      val newRules = recInfo.rules.map { rule =>
        val newRhs = res.restoreNested(rule.rhs, auxEnv, recMap)
        val newCtor =
          if newRecName != recName then res.restoreConstructorName(auxEnv, rule.ctor) else rule.ctor
        RecursorRule(newCtor, rule.nfields, newRhs)
      }
      newEnv.checkName(newRecName)
      val rv = RecursorVal(
        ConstantVal(newRecName, cv.levelParams, newRecType),
        allIndNames,
        recInfo.numParams,
        recInfo.numIndices,
        recInfo.numMotives,
        recInfo.numMinors,
        newRules,
        recInfo.k,
        recInfo.isUnsafe
      )
      newEnv = newEnv.addCore(ConstantInfo.RecInfo(rv))
      recursors += rv
      newRecNames += newRecName

    decl.types.foreach { indType =>
      val indVal = auxEnv.get(indType.name) match
        case ConstantInfo.InductInfo(v) => v
        case _ =>
          throw KernelException(ExceptionKind.InvalidDeclaration, indType.name, "expected an inductive type")
      // Only `all` needs fixing: the auxiliary block listed the auxiliary types.
      val fixed = indVal.copy(all = allIndNames)
      newEnv.checkName(indType.name)
      newEnv = newEnv.addCore(ConstantInfo.InductInfo(fixed))
      inductives += fixed
      indVal.ctors.foreach { ctorName =>
        val ctorVal = auxEnv.get(ctorName) match
          case ConstantInfo.CtorInfo(v) => v
          case _ =>
            throw KernelException(ExceptionKind.InvalidDeclaration, ctorName, "expected a constructor")
        val newType = res.restoreNested(ctorVal.toConstantVal.tpe, auxEnv)
        val fixedCtor =
          ctorVal.copy(toConstantVal = ctorVal.toConstantVal.copy(tpe = newType))
        newEnv.checkName(ctorName)
        newEnv = newEnv.addCore(ConstantInfo.CtorInfo(fixedCtor))
        constructors += fixedCtor
      }
      processRec(Names.recName(indType.name))
    }
    auxRecNames.foreach(processRec)

    // The parametric arguments `Ds` of a nested occurrence `I Ds` do not appear
    // in the auxiliary declaration, so they would otherwise never be checked.
    // They are checked last, in the restored environment.
    val paramTc = new TypeChecker(newEnv, profile, safety, res.paramsLctx, maxSteps)
    res.aux2nested.values.foreach(nested => paramTc.check(nested, decl.levelParams))

    // Re-check what `restoreNested` rewrote. The checks above are expected to
    // make this redundant; it keeps a mistake in the restoration from reaching
    // the environment.
    val tc = new TypeChecker(newEnv, profile, safety, LocalContext.empty, maxSteps)
    constructors.foreach(c => tc.check(c.toConstantVal.tpe, decl.levelParams))
    newRecNames.foreach { recName =>
      val info = newEnv.get(recName)
      tc.check(info.tpe, info.levelParams)
      info match
        case ConstantInfo.RecInfo(v) => v.rules.foreach(r => tc.check(r.rhs, info.levelParams))
        case _                       => ()
    }

    AddInductiveResult(newEnv, inductives.toList, constructors.toList, recursors.toList, res.numNested)
