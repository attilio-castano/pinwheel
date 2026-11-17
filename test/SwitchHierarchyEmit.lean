import Lean
import Pinwheel.Hardware.Switch.Export

open Lean Elab Command Pinwheel.Hardware Pinwheel.Hardware.Switch

elab "#audit_switch_export" : command => do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    if name.toString.startsWith "Pinwheel.Hardware.Switch.Export." then
      count := count + 1
      let axioms ← collectAxioms name
      let bad := axioms.filter fun a => a != ``propext && a != ``Classical.choice && a != ``Quot.sound
      unless bad.isEmpty do throwError "Unapproved axioms in {name}: {bad}"
  if count == 0 then throwError "Empty switch export audit"
  logInfo m!"Switch export audit: {count} declarations, standard axioms only."

#audit_switch_export

namespace SwitchHierarchyEmit

private def number (s : String) : IO Nat :=
  match s.toNat? with
  | some n => pure n
  | none => throw (IO.userError s!"Expected natural number: {s}")

def encoding (extraOutputs : Nat) : Physical.DestinationEncoding (extraOutputs + 1) :=
  ⟨extraOutputs.log2 + 1, by omega, Nat.succ_le_of_lt Nat.lt_log2_self⟩

example : (encoding 0).width = 1 := rfl
example : (encoding 2).width = 2 := rfl

-- No reachable-state hypothesis: raw cursor and FIFO/slot bits are arbitrary.
example (wire : Structural.Wire n m dw w depth b)
    (i : Values (Physical.In n m dw w)) (s : Values (Structural.Register n m dw w depth)) :
    (Export.controlWire wire).eval (Export.controlValues i s) (Export.cursorValues s) = wire.eval i s :=
  Export.controlWire_eval wire i s

end SwitchHierarchyEmit

def main (args : List String) : IO Unit := do
  let [ni, no, d, w, out] := args
    | throw (IO.userError "Usage: switch_hierarchy_emit INPUTS OUTPUTS DEPTH WIDTH outdir")
  let count ← SwitchHierarchyEmit.number ni
  let outputs ← SwitchHierarchyEmit.number no
  let depth ← SwitchHierarchyEmit.number d
  let width ← SwitchHierarchyEmit.number w
  unless count > 0 && outputs > 0 && depth > 0 && width > 0 do
    throw (IO.userError "All parameters must be positive")
  let e := SwitchHierarchyEmit.encoding (outputs - 1)
  let name := s!"packet_switch_{count}x{outputs}_d{depth}_w{width}_hierarchical"
  Export.exportHierarchy e (count - 1) width depth out name
  IO.println s!"Hierarchical switch {count}/{outputs}/{depth}/{width}: shared FIFO and slot leaves, one typed control module; emitted to {out}."
