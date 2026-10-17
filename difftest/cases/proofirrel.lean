/-- Proof irrelevance: any two proofs of a proposition are equal. -/
theorem irrel (p : Prop) (h1 h2 : p) : h1 = h2 := rfl

/-- Irrelevance under a dependent type. -/
def dep (p : Prop) (h : p) : (fun _ : p => Nat) h := 0

theorem depIrrel (p : Prop) (h1 h2 : p) : dep p h1 = dep p h2 := rfl
