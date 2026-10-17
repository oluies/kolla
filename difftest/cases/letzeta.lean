/-- `let` is reduced by zeta. -/
theorem zetaReduce : (let x := 3; x + x) = 6 := rfl

def nestedLet (n : Nat) : Nat :=
  let a := n + 1
  let b := a + a
  let c := b * b
  c

theorem nestedLetValue : nestedLet 2 = 36 := rfl

/-- A `let` whose body does not use the bound variable. -/
theorem nondepLet : (let _x := 3; 7) = 7 := rfl
