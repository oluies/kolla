/-
Reports which of the given names the environment actually declares.

`difftest/mathlib-sample.txt` names declarations to export. A name that is not
a declaration — a module name, a renamed lemma, a typo — would be dropped by
`lean4export` or abort it, and either way the corpus would quietly not be what
the file says it is. This prints a verdict per name so the list can be checked
rather than assumed.

  lake env lean --run CheckNames.lean <module> -- <name>...
-/
import Lean

open Lean

def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let (mods, rest) := args.span (· != "--")
  let names := rest.tail?.getD []
  if mods.isEmpty || names.isEmpty then
    throw <| IO.userError "usage: CheckNames.lean <module>... -- <name>..."
  let env ← importModules (mods.toArray.map fun m => { module := m.toName }) {}
  let mut missing := 0
  for arg in names do
    let n := arg.toName
    if env.contains n then
      let kind := match env.find? n with
        | some (.axiomInfo _)  => "axiom"
        | some (.defnInfo _)   => "def"
        | some (.thmInfo _)    => "theorem"
        | some (.opaqueInfo _) => "opaque"
        | some (.quotInfo _)   => "quot"
        | some (.inductInfo _) => "inductive"
        | some (.ctorInfo _)   => "constructor"
        | some (.recInfo _)    => "recursor"
        | none                 => "?"
      IO.println s!"ok      {arg} ({kind})"
    else
      IO.println s!"MISSING {arg}"
      missing := missing + 1
  IO.println s!"{names.length - missing}/{names.length} present"
  return (if missing == 0 then 0 else 1)
