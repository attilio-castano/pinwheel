import Pinwheel.Hardware.Storage.PairedStream
import Lean

/-! Untrusted names of shared values in the stream emission. The readback
certificate must prove every named value's equation against the typed graph. -/
open Pinwheel.Hardware Pinwheel.Hardware.Storage

deriving instance Repr for PairedController.Computation

private def labels (rn : {w : Nat} → R w → String) :
    {I : Nat → Type} → Netlist R O I → ({w : Nat} → I w → String) → Emit.M (Array String)
  | _, .finish _, _ => pure #[]
  | _, .letWire e body, names => do
    let value ← Emit.expression names rn e
    let rest ← labels rn body (fun p => match p with
      | .input p => names p | .wire => value)
    return #[value] ++ rest

private def cuts (n : Netlist R O I) (rn : {w : Nat} → R w → String)
    (ins : {w : Nat} → I w → String) : Except String Lean.Json := do
  let (values, _) ← (labels (fun r => "%r_" ++ rn r) n (fun p => "%" ++ ins p)).run {}
  unless values.size == PairedValidation.bindings.length do throw "Changed binding count"
  return Lean.toJson (PairedValidation.bindings.toArray.zip values |>.map fun ((name, _), value) =>
    Lean.Json.mkObj [("node", Lean.toJson (reprStr name)), ("label", Lean.toJson value)])

def main (args : List String) : IO Unit := do
  let out := args.headD "build/validation/paired-readback-hints"
  IO.FS.createDirAll out
  let .ok n := PairedStream.core | throw (IO.userError "Invalid stream graph")
  for (kind, result) in [
    ("core", cuts n PairedStream.label (SramAssembly.inputLabel Loader.Machine.inputLabel)),
    ("chip", cuts (PairedStream.package n) PairedStream.fullLabel
      (SramAssembly.inputLabel Backend.Policy.chipInputLabel))] do
    let .ok json := result | throw (IO.userError "Unable to produce shared-value hints")
    IO.FS.writeFile (out ++ "/" ++ kind ++ "-cuts.json") (json.pretty ++ "\n")
