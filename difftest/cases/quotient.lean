/-- The quotient package: `Quot.lift` on a representative reduces. -/
def R (a b : Nat) : Prop := a % 2 = b % 2

def parity (n : Nat) : Quot R := Quot.mk R n

def readBack (q : Quot R) : Nat := Quot.lift (fun n => n % 2) (fun _ _ h => h) q

theorem liftMk (n : Nat) : readBack (parity n) = n % 2 := rfl

theorem soundUsed (a b : Nat) (h : R a b) : parity a = parity b := Quot.sound h

/-- `Quot.ind` is the eliminator into `Prop`. -/
theorem indUsed (q : Quot R) : readBack q = readBack q :=
  Quot.ind (β := fun x => readBack x = readBack x) (fun _ => rfl) q
