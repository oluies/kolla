/-- A nested inductive: the recursive occurrence sits under `List`. -/
inductive Tree where
  | leaf : Nat → Tree
  | node : List Tree → Tree

def Tree.size : Tree → Nat
  | .leaf _ => 1
  | .node ts => ts.foldl (fun acc t => acc + t.size) 1

/-- Nesting through a parameterised type. -/
inductive RoseTree (α : Type) where
  | mk : α → List (RoseTree α) → RoseTree α

-- A mutual block.
mutual
inductive EvenList where
  | nil : EvenList
  | cons : Nat → OddList → EvenList
inductive OddList where
  | cons : Nat → EvenList → OddList
end

mutual
def EvenList.length : EvenList → Nat
  | .nil => 0
  | .cons _ t => 1 + t.length
def OddList.length : OddList → Nat
  | .cons _ t => 1 + t.length
end
