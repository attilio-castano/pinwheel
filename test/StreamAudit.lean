import Lean
import Pinwheel.Hardware.Stream.Timing
import Pinwheel.Hardware.Stream.Bundle

open Lean Elab Command

elab "#audit_stream" : command => do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    if name.toString.startsWith "Pinwheel.Hardware.Stream." ||
        name.toString.startsWith "_private.Pinwheel.Hardware.Stream." then
      count := count + 1
      let axioms ← collectAxioms name
      let bad := axioms.filter fun a => a != ``propext && a != ``Classical.choice && a != ``Quot.sound
      unless bad.isEmpty do throwError "Unapproved axioms in {name}: {bad}"
  if count == 0 then throwError "Empty stream proof audit"
  logInfo m!"Stream audit: {count} declarations, standard axioms only."

#audit_stream
