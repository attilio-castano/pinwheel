import Lean
import Pinwheel

open Lean Elab Command

/-- Audit the compiled environment, including private declarations and definitions
whose fields contain proofs. Source-text theorem discovery is insufficient here. -/
elab "#audit_pinwheel" : command => do
  let env ← getEnv
  let mut declarations : Nat := 0
  let mut theorems : Nat := 0
  for (name, info) in env.constants.toList do
    let text := name.toString
    if text.startsWith "Pinwheel." || text.startsWith "_private.Pinwheel." then
      declarations := declarations + 1
      if info.isTheorem then theorems := theorems + 1
      let axioms ← collectAxioms name
      let unexpected := axioms.filter fun ax =>
        ax != ``propext && ax != ``Classical.choice && ax != ``Quot.sound
      unless unexpected.isEmpty do
        throwError "Unapproved axioms in {name}: {unexpected}"
  if declarations == 0 || theorems == 0 then
    throwError "Empty Pinwheel proof audit"
  logInfo m!"Pinwheel audit: {declarations} declarations, {theorems} theorems; standard axioms only."

#audit_pinwheel
