/-
Prints the names a module declares itself, one per line.

`lean4export` exports either a whole environment or a given list of constants
with their dependencies. A handwritten case wants the latter, so the driver
needs the module's own declaration names; they are in the olean's `constNames`.
-/
import Lean

open Lean

def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  for arg in args do
    let mFile ← findOLean arg.toName
    unless (← mFile.pathExists) do
      throw <| IO.userError s!"no olean for {arg} at {mFile}"
    let (mod, _) ← readModuleData mFile
    for n in mod.constNames do
      unless n.isInternal do IO.println n
  return 0
