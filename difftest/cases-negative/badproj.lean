/-
A projection whose index is past the structure's field count. The elaborator
cannot produce this, so it is built directly and inserted without a check.
-/
-- toolchains: v4.25.0 v4.27.0 v4.28.0
import Lean.Elab.Term

open Lean in
run_elab
  modifyEnv fun env => Id.run do
    let ty := Expr.const ``Nat []
    let val := Expr.proj ``Prod 7 (mkApp4 (.const ``Prod.mk [levelZero, levelZero])
      (.const ``Nat []) (.const ``Nat []) (.lit (.natVal 1)) (.lit (.natVal 2)))
    let decl := .defnDecl {
      name := `kollaBadProj, levelParams := [], type := ty, value := val,
      hints := .abbrev, safety := .safe }
    let .ok env := env.addDeclCore (doCheck := false) 0 decl none |
      let _ : Inhabited Environment := ⟨env⟩
      unreachable!
    env
