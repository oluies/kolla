package kolla.kernel

/** Constants the kernel refers to by name. */
object Names:
  val nat: Name       = Name.parse("Nat")
  val natZero: Name   = Name.parse("Nat.zero")
  val natSucc: Name   = Name.parse("Nat.succ")
  val natAdd: Name    = Name.parse("Nat.add")
  val natSub: Name    = Name.parse("Nat.sub")
  val natMul: Name    = Name.parse("Nat.mul")
  val natPow: Name    = Name.parse("Nat.pow")
  val natGcd: Name    = Name.parse("Nat.gcd")
  val natDiv: Name    = Name.parse("Nat.div")
  val natMod: Name    = Name.parse("Nat.mod")
  val natBeq: Name    = Name.parse("Nat.beq")
  val natBle: Name    = Name.parse("Nat.ble")
  val natLand: Name   = Name.parse("Nat.land")
  val natLor: Name    = Name.parse("Nat.lor")
  val natXor: Name    = Name.parse("Nat.xor")
  val natShiftLeft: Name  = Name.parse("Nat.shiftLeft")
  val natShiftRight: Name = Name.parse("Nat.shiftRight")
  val natLog2: Name   = Name.parse("Nat.log2")

  val string: Name    = Name.parse("String")
  val char: Name      = Name.parse("Char")
  val charOfNat: Name = Name.parse("Char.ofNat")
  val listCons: Name  = Name.parse("List.cons")
  val listNil: Name   = Name.parse("List.nil")

  val boolTrue: Name  = Name.parse("Bool.true")
  val boolFalse: Name = Name.parse("Bool.false")

  val eq: Name        = Name.parse("Eq")
  val quot: Name      = Name.parse("Quot")
  val quotMk: Name    = Name.parse("Quot.mk")
  val quotLift: Name  = Name.parse("Quot.lift")
  val quotInd: Name   = Name.parse("Quot.ind")

  val eagerReduce: Name = Name.parse("eagerReduce")

  val optParam: Name     = Name.parse("optParam")
  val autoParam: Name    = Name.parse("autoParam")
  val outParam: Name     = Name.parse("outParam")
  val semiOutParam: Name = Name.parse("semiOutParam")

  val quotNames: Set[Name] = Set(quot, quotMk, quotLift, quotInd)

  def isQuotRecursor(n: Name): Boolean = n == quotLift || n == quotInd

  def recName(ind: Name): Name = ind.str("rec")

  def stringOfListFor(p: KernelProfile): Name = p.stringLiteralCtor
