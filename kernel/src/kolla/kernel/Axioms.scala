package kolla.kernel

import scala.collection.mutable

/** The axioms a declaration transitively rests on, as `#print axioms` reports.
  *
  * Type-checking answers whether a declaration follows from what the file
  * declared. It does not answer what the file declared, and the difference
  * matters: a `sorry` elaborates to the `sorryAx` axiom, so a theorem with no
  * proof at all type-checks exactly like one with a proof. Reading the source
  * catches that only when the `sorry` is in the declaration being read — not
  * when it is in a dependency, and not when all you have is an export.
  *
  * See docs/semantics.md A1.
  */
object Axioms:

  /** What `sorry` becomes. A closure containing it is not a proof. */
  val sorry: Name = Name.parse("sorryAx")

  /** Lean's ordinary trust base, which almost every real development uses.
    *
    * `propext`, `Classical.choice` and `Quot.sound` are the three axioms Lean
    * itself ships; depending on them is unremarkable. Anything else is worth a
    * reader's attention, which is why they are reported apart.
    */
  val standard: Set[Name] =
    Set(Name.parse("propext"), Name.parse("Classical.choice"), Name.parse("Quot.sound"))

  /** Whether `closure` rests on nothing outside `permitted`.
    *
    * The gate a caller actually wants, and the criterion a comparator
    * challenge states: `permitted_axioms` there is the three Lean ships, and a
    * candidate resting on anything else — `sorryAx` first among them — does
    * not count. Stating the set is the point: "no unusual axioms" is a
    * judgement about which axioms are ordinary, and a caller may not share it.
    */
  def within(closure: Closure, permitted: Set[Name]): Vector[Name] =
    closure.axioms.filterNot(permitted.contains)

  /** What `name` rests on. `axioms` is sorted, so two runs compare. */
  final case class Closure(declaration: Name, axioms: Vector[Name], constants: Int):
    /** The declaration has no proof: some part of it was left as `sorry`. */
    def hasSorry: Boolean = axioms.contains(Axioms.sorry)

    /** Axioms outside Lean's trust base, `sorryAx` aside. */
    def unusual: Vector[Name] = axioms.filterNot(a => standard.contains(a) || a == Axioms.sorry)

    def render: String =
      val sb = new StringBuilder
      sb ++= s"$declaration rests on "
      if axioms.isEmpty then sb ++= "no axioms"
      else sb ++= s"${axioms.length} axiom(s)"
      sb ++= s", reached through ${constants} constant(s)\n"
      axioms.foreach { a =>
        val note =
          if a == Axioms.sorry then "  <- NOT A PROOF: left as sorry"
          else if standard.contains(a) then "  (Lean's trust base)"
          else "  <- outside Lean's trust base"
        sb ++= s"  $a$note\n"
      }
      sb.result()

  /** Walks the dependency graph from `name`, collecting axioms.
    *
    * Both the type and the value are followed: a statement's meaning rests on
    * the constants in its type as much as its proof rests on those in its
    * value. Iterative rather than recursive, because a real environment nests
    * deeper than the stack allows.
    */
  def of(env: Environment, name: Name): Either[String, Closure] =
    if !env.contains(name) then Left(s"unknown constant '$name'")
    else
      val seen  = mutable.HashSet.empty[Name]
      val found = mutable.HashSet.empty[Name]
      val stack = mutable.ArrayDeque.empty[Name]
      stack.append(name)
      while stack.nonEmpty do
        val n = stack.removeLast()
        if seen.add(n) then
          env.find(n).foreach { info =>
            if info.isInstanceOf[ConstantInfo.AxiomInfo] then found += n
            references(info).foreach(r => if !seen.contains(r) then stack.append(r))
          }
      Right(Closure(name, found.toVector.sortBy(_.toString), seen.size))

  /** Every constant an declaration's type and value mention. */
  /** What `info` names: every constant its type, value and rules reach.
    *
    * Public because premise selection asks the same question the axiom walk
    * does, one declaration deep rather than transitively.
    */
  def referencesOf(info: ConstantInfo): Set[Name] = references(info)

  private def references(info: ConstantInfo): Set[Name] =
    val out = mutable.HashSet.empty[Name]
    def walk(e: Expr): Unit =
      ExprOps.forEach(e) { (x, _) =>
        x match
          case c: Expr.Const => out += c.name
          case p: Expr.Proj  => out += p.typeName
          case _             => ()
        true
      }
    walk(info.tpe)
    info.value(allowOpaque = true).foreach(walk)
    // A recursor's rules carry terms that nothing else reaches.
    info match
      case ConstantInfo.RecInfo(v)    => v.rules.foreach(r => walk(r.rhs))
      case ConstantInfo.InductInfo(v) => out ++= v.all; out ++= v.ctors
      case ConstantInfo.CtorInfo(v)   => out += v.induct
      case _                          => ()
    out.toSet
