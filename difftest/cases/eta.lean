/-- Function eta: `fun x => f x` and `f` are definitionally equal. -/
theorem fnEta (f : Nat → Nat) : (fun x => f x) = f := rfl

/-- Eta for a structure: a value and its reassembled form agree. -/
structure Pair where
  fst : Nat
  snd : Nat

theorem structEta (p : Pair) : ⟨p.fst, p.snd⟩ = p := rfl

/-- A unit-like structure: every value is definitionally the constructor. -/
structure Wrap (α : Type) where
  unwrap : α

theorem wrapEta (α : Type) (w : Wrap α) : Wrap.mk w.unwrap = w := rfl
