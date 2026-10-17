/-- Projection reduction on a literal structure value. -/
structure Point where
  x : Nat
  y : Nat
  z : Nat

theorem projFst : (Point.mk 1 2 3).x = 1 := rfl
theorem projSnd : (Point.mk 1 2 3).y = 2 := rfl
theorem projThd : (Point.mk 1 2 3).z = 3 := rfl

/-- A structure with a dependent field. -/
structure Sigma' where
  fst : Type
  snd : fst

def d : Sigma' := ⟨Nat, 0⟩

theorem projDep : d.snd = (0 : Nat) := rfl

/-- Projections through a class, which the elaborator compiles to `proj`. -/
class Monoid' (α : Type) where
  one : α
  mul : α → α → α

instance : Monoid' Nat := ⟨1, (· * ·)⟩

theorem classProj : Monoid'.one (α := Nat) = 1 := rfl
