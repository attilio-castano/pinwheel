import Lean
import Pinwheel.Hardware.Memory.TransferCircuitProofs

open Lean Elab Command

/-- Audit all imported memory declarations, including private helpers. -/
elab "#audit_memory_transfer" : command => do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    if name.toString.startsWith "Pinwheel.Hardware.Memory." ||
        name.toString.startsWith "_private.Pinwheel.Hardware.Memory." then
      count := count + 1
      let axioms ← collectAxioms name
      let bad := axioms.filter fun a => a != ``propext && a != ``Classical.choice && a != ``Quot.sound
      unless bad.isEmpty do throwError "Unapproved axioms in {name}: {bad}"
  if count == 0 then throwError "Empty memory transfer audit"
  logInfo m!"Memory transfer audit: {count} declarations, standard axioms only."

#audit_memory_transfer
