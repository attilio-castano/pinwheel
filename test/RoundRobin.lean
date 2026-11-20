import Lean
import Pinwheel.Hardware.Arbitration.RoundRobin

open Pinwheel.Hardware.Arbitration.RoundRobin
open Lean Elab Command

elab "#audit_round_robin" : command => do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    if name.toString.startsWith "Pinwheel.Hardware.Arbitration.RoundRobin." then
      count := count + 1
      let axioms ← collectAxioms name
      let bad := axioms.filter fun a => a != ``propext && a != ``Classical.choice && a != ``Quot.sound
      unless bad.isEmpty do throwError "Unapproved axioms in {name}: {bad}"
  if count == 0 then throwError "Empty round-robin proof audit"
  logInfo m!"Round-robin audit: {count} declarations, standard axioms only."

#audit_round_robin

example : grant (2 : Fin 3) (fun i => decide (i.val = 0 ∨ i.val = 1)) = some 0 := by decide +kernel
example : grant (2 : Fin 3) (fun _ => true) = some 2 := by decide +kernel
example : next (2 : Fin 3) = 0 := rfl
example : grant (0 : Fin 1) (fun _ => true) = some 0 := rfl

def main : IO Unit := do
  let mut selections := 0
  let mut fairnessTraces := 0
  for extra in [0, 1, 2, 3, 4, 7] do
    let count := extra + 1
    for mask in [:2^count] do
      for cursor in List.finRange count do
        let c := cursor.val
        let request : Fin (extra + 1) → Bool := fun i => (mask / 2^i.val) % 2 == 1
        -- Independent modulo-based cyclic scan; the implementation uses one
        -- bounded subtraction, so wraparound errors do not share an oracle.
        let expected := (List.range count).findSome? fun offset =>
          let index := (c + offset) % count
          if (mask / 2^index) % 2 == 1 then some index else none
        unless (grant cursor request).map Fin.val == expected do
          throw (IO.userError s!"Selector mismatch: inputs={count}, cursor={c}, mask={mask}")
        selections := selections + 1
    for cursor in List.finRange count do
      for target in List.finRange count do
        let c := cursor.val
        let t := target.val
        for seed in [:32] do
          let requests : List (Fin (extra + 1) → Bool) := (List.range count).map fun step i =>
            i == target || (seed + step * 17 + i.val * 13) % 7 < 4
          unless target ∈ services cursor requests do
            throw (IO.userError s!"Fairness mismatch: inputs={count}, cursor={c}, target={t}, seed={seed}")
          fairnessTraces := fairnessTraces + 1
  IO.println s!"Round-robin: {selections} exhaustive selections and {fairnessTraces} changing-request fairness traces passed."
