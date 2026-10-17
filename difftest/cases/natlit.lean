/-- Literal arithmetic is reduced by the kernel's `Nat` extension. -/
theorem addLit : 2 + 3 = 5 := rfl
theorem mulLit : 7 * 6 = 42 := rfl
theorem bigLit : 1000000000000 + 1 = 1000000000001 := rfl
theorem powLit : 2 ^ 10 = 1024 := rfl
theorem modLit : 17 % 5 = 2 := rfl
theorem divLit : 17 / 5 = 3 := rfl
theorem subLit : 3 - 7 = 0 := rfl
theorem decEqLit : (4 = 4) = True := by simp
theorem bleLit : Nat.ble 3 4 = true := rfl
theorem gcdLit : Nat.gcd 12 18 = 6 := by decide

/-- Offset defeq: `n + 2` and `Nat.succ (Nat.succ n)` agree. -/
theorem offset (n : Nat) : n + 2 = n.succ.succ := rfl
