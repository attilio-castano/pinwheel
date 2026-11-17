import Lean
import Pinwheel.Hardware.Memory.CommandFlopsProofs

open Lean Elab Command

/-- Audit every imported memory declaration, including private helpers and
unused declarations, rather than only the exported refinement theorem. -/
elab "#audit_memory_command" : command => do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    if name.toString.startsWith "Pinwheel.Hardware.Memory." ||
        name.toString.startsWith "_private.Pinwheel.Hardware.Memory." then
      count := count + 1
      let axioms ← collectAxioms name
      let bad := axioms.filter fun a => a != ``propext && a != ``Classical.choice && a != ``Quot.sound
      unless bad.isEmpty do throwError "Unapproved axioms in {name}: {bad}"
  if count == 0 then throwError "Empty command memory audit"
  logInfo m!"Command memory audit: {count} declarations, standard axioms only."

#audit_memory_command
