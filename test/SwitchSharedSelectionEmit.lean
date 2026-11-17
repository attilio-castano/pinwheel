import Lean
import Pinwheel.Hardware.Switch.SharedSelectionCandidate
import Pinwheel.Hardware.Emit
import Lean.Data.Json

open Lean Elab Command Pinwheel.Hardware Pinwheel.Hardware.Switch

elab "#audit_shared_switch" : command => do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    if name.toString.startsWith "Pinwheel.Hardware.Switch.SharedSelectionCandidate." then
      count := count + 1
      let axioms ← collectAxioms name
      let bad := axioms.filter fun a => a != ``propext && a != ``Classical.choice && a != ``Quot.sound
      unless bad.isEmpty do throwError "Unapproved axioms in {name}: {bad}"
  if count == 0 then throwError "Empty shared switch audit"
  logInfo m!"Shared switch audit: {count} declarations, standard axioms only."

#audit_shared_switch

namespace SwitchSharedSelectionEmit

set_option backward.isDefEq.respectTransparency false

private def number (s : String) : IO Nat :=
  match s.toNat? with
  | some n => pure n
  | none => throw (IO.userError s!"Expected natural number: {s}")

/-- ceil(log2(outputs)), with one physical bit even for a single output. -/
def encoding (extraOutputs : Nat) : Physical.DestinationEncoding (extraOutputs + 1) :=
  ⟨extraOutputs.log2 + 1, by omega, Nat.succ_le_of_lt Nat.lt_log2_self⟩

private def portsJson (d : Interface P) : Json :=
  toJson (d.ports.map fun ⟨w, p⟩ => Json.mkObj
    [("name", toJson (d.label p)), ("width", toJson w)])

def emit (extraInputs extraOutputs depth width : Nat) (out : String) : IO Unit := do
  let e := encoding extraOutputs
  let ii := Physical.inputInterface extraInputs extraOutputs e.width width
  let oi := Physical.outputInterface extraInputs extraOutputs width
  let ri := Structural.registers extraInputs extraOutputs e.width width depth
  let c := SharedSelectionCandidate.circuit e extraInputs width depth
  let initial : Values (Structural.Register extraInputs extraOutputs e.width width depth) :=
    Structural.encode e Switch.initial
  let registerName := fun {b : Nat} (r : Structural.Register extraInputs extraOutputs e.width width depth b) =>
    "r_" ++ ri.label r
  let moduleName := s!"shared_packet_switch_{extraInputs+1}x{extraOutputs+1}_d{depth}_w{width}"
  IO.FS.createDirAll out
  IO.FS.writeFile (out ++ "/switch.mlir") (← IO.ofExcept
    (Emit.moduleText moduleName c ii.ports ri.ports oi.ports ii.label ri.label oi.label))
  let regs := toJson (ri.ports.map fun ⟨b, r⟩ => Json.mkObj
    [("name", toJson (registerName r)), ("reference", toJson (registerName r)),
     ("width", toJson b), ("initial", toJson ((initial r).toNat)),
     ("reset", toJson ((initial r).toNat))])
  let roles := Json.mkObj
    [("reset", toJson (ii.label Physical.reset)),
     ("in_valid", toJson (Array.ofFn (fun k : Fin (extraInputs+1) => ii.label (Physical.inValid k)))),
     ("in_destination", toJson (Array.ofFn (fun k : Fin (extraInputs+1) => ii.label (Physical.inDestination k)))),
     ("in_payload", toJson (Array.ofFn (fun k : Fin (extraInputs+1) => ii.label (Physical.inPayload k)))),
     ("out_ready", toJson (Array.ofFn (fun o : Fin (extraOutputs+1) => ii.label (Physical.outReady o)))),
     ("in_ready", toJson (Array.ofFn (fun k : Fin (extraInputs+1) => oi.label (Physical.inReady k)))),
     ("out_valid", toJson (Array.ofFn (fun o : Fin (extraOutputs+1) => oi.label (Physical.outValid o)))),
     ("out_payload", toJson (Array.ofFn (fun o : Fin (extraOutputs+1) => oi.label (Physical.outPayload o))))]
  let registerRoles := Json.mkObj
    [("fifo_valid", toJson (Array.ofFn (fun k : Fin (extraInputs+1) =>
        Array.ofFn (fun cell : Fin depth => registerName (Structural.fifoReg k (.valid cell)))))),
     ("fifo_data", toJson (Array.ofFn (fun k : Fin (extraInputs+1) =>
        Array.ofFn (fun cell : Fin depth => registerName (Structural.fifoReg k (.data cell)))))),
     ("slot_valid", toJson (Array.ofFn (fun o : Fin (extraOutputs+1) => registerName (Structural.slotReg o (.valid 0))))),
     ("slot_payload", toJson (Array.ofFn (fun o : Fin (extraOutputs+1) => registerName (Structural.slotReg o (.data 0))))),
     ("cursor", toJson (Array.ofFn (fun o : Fin (extraOutputs+1) =>
        Array.ofFn (fun k : Fin (extraInputs+1) => registerName (Structural.cursorReg o k)))))]
  let descriptor := Json.mkObj
    [("schema", toJson (1 : Nat)), ("module", toJson moduleName),
     ("input_count", toJson (extraInputs+1)), ("output_count", toJson (extraOutputs+1)),
     ("depth", toJson depth), ("payload_width", toJson width), ("destination_width", toJson e.width),
     ("clock", toJson "clk"), ("reset_synchronous", toJson true),
     ("inputs", portsJson ii), ("outputs", portsJson oi), ("registers", regs),
     ("roles", roles), ("register_roles", registerRoles),
     ("startup", toJson "encoded_initial; hardware requires a reset edge before use")]
  IO.FS.writeFile (out ++ "/interface.json") (descriptor.pretty ++ "\n")
  IO.println s!"Switch {extraInputs+1}/{extraOutputs+1}/{depth}/{width}: destination width {e.width}; {ii.size} inputs, {oi.size} outputs, {ri.size} registers emitted to {out}."

end SwitchSharedSelectionEmit

def main (args : List String) : IO Unit := do
  let [ni, no, d, w, out] := args
    | throw (IO.userError "Usage: switch_shared_selection_emit INPUTS OUTPUTS DEPTH WIDTH outdir")
  let count ← SwitchSharedSelectionEmit.number ni
  let outputs ← SwitchSharedSelectionEmit.number no
  let depth ← SwitchSharedSelectionEmit.number d
  let width ← SwitchSharedSelectionEmit.number w
  unless count > 0 && outputs > 0 && depth > 0 && width > 0 do
    throw (IO.userError "All parameters must be positive")
  SwitchSharedSelectionEmit.emit (count - 1) (outputs - 1) depth width out
