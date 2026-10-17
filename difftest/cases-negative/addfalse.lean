/-
A declaration the elaborator puts into the environment without the kernel's
consent: `false : False := False` has the right shape but `False` is not a proof
of `False`. The kernel has to reject it.

Adapted from lean4checker's own `Lean4CheckerTests/AddFalse.lean`, which is the
case `lake test` there expects a rejection for.
-/
-- toolchains: v4.25.0 v4.27.0 v4.28.0
import Lean.Elab.Term

open Lean in
run_elab
  modifyEnv fun env => Id.run do
    let decl := .thmDecl { name := `kollaFalse, levelParams := [], type := .const ``False [], value := .const ``False [] }
    let .ok env := env.addDeclCore (doCheck := false) 0 decl none |
      let _ : Inhabited Environment := ⟨env⟩
      unreachable!
    env
