/-
A definition whose stated type is `Sort 0` while its value inhabits `Sort 1`.
Inserted without a check, so only the kernel can catch it.
-/
-- toolchains: v4.25.0 v4.27.0 v4.28.0
import Lean.Elab.Term

open Lean in
run_elab
  modifyEnv fun env => Id.run do
    let decl := .defnDecl {
      name := `kollaBadSort, levelParams := [],
      type := .sort levelZero, value := .sort levelZero,
      hints := .abbrev, safety := .safe }
    let .ok env := env.addDeclCore (doCheck := false) 0 decl none |
      let _ : Inhabited Environment := ⟨env⟩
      unreachable!
    env
