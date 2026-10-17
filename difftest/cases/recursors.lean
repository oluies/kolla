/-- Recursor rules fire on each constructor (iota). -/
inductive Color where
  | red | green | blue

def Color.index : Color → Nat
  | .red => 0
  | .green => 1
  | .blue => 2

theorem iotaRed : Color.red.index = 0 := rfl
theorem iotaBlue : Color.blue.index = 2 := rfl

/-- An indexed family: the recursor takes the indices as majors. -/
inductive Vec (α : Type) : Nat → Type where
  | nil : Vec α 0
  | cons : α → {n : Nat} → Vec α n → Vec α (n + 1)

def Vec.length {α : Type} {n : Nat} (_ : Vec α n) : Nat := n

def Vec.toList {α : Type} : {n : Nat} → Vec α n → List α
  | _, .nil => []
  | _, .cons a v => a :: v.toList

theorem vecToList : (Vec.cons 1 (Vec.cons 2 Vec.nil)).toList = [1, 2] := rfl

/-- A large-eliminating proposition: `And` eliminates into any sort. -/
theorem andLeft (p q : Prop) (h : p ∧ q) : p := h.left

/-- `Eq` recursion, which has a single rule and a reflexivity major. -/
theorem eqRec {α : Type} {a b : α} (h : a = b) (m : α → Prop) (x : m a) : m b := h ▸ x
