import Lean
import Pinwheel.Hardware.Switch.Contract

open Lean Elab Command

elab "#audit_switch" : command => do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    if ["Pinwheel.Hardware.Switch.", "Pinwheel.Hardware.Stream.Multiport.",
        "Pinwheel.Hardware.Arbitration.RoundRobin."].any (name.toString.startsWith ·) then
      count := count + 1
      let axioms ← collectAxioms name
      let bad := axioms.filter fun a => a != ``propext && a != ``Classical.choice && a != ``Quot.sound
      unless bad.isEmpty do throwError "Unapproved axioms in {name}: {bad}"
  if count == 0 then throwError "Empty switch proof audit"
  logInfo m!"Switch audit: {count} declarations, standard axioms only."

#audit_switch
