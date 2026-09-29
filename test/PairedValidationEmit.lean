import Pinwheel.Hardware.Storage.PairedValidation
import Lean

open Pinwheel.Hardware Pinwheel.Hardware.Storage

open Lean Elab Command in
elab "#audit_paired_controller" : command => do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    if name.toString.startsWith "Pinwheel.Hardware.Storage.PairedController." ||
        name.toString.startsWith "Pinwheel.Hardware.Storage.PairedValidation." then
      count := count + 1
      let axioms ← collectAxioms name
      let unexpected := axioms.filter fun ax =>
        ax != ``propext && ax != ``Classical.choice && ax != ``Quot.sound
      unless unexpected.isEmpty do
        throwError "Unapproved paired controller axioms: {unexpected}"
  logInfo m!"Paired validation: {count} declarations; standard axioms only."

#audit_paired_controller

private def portJson (ps : Array (Sigma P)) (label : {w : Nat} → P w → String) : Lean.Json :=
  Lean.toJson (ps.map fun ⟨w,p⟩ => Lean.Json.mkObj
    [("name",Lean.toJson (label p)),("width",Lean.toJson w)])

private def registersJson (rs : Array (Sigma R)) (label : {w : Nat} → R w → String) : Lean.Json :=
  Lean.toJson (rs.map fun ⟨w,r⟩ => Lean.Json.mkObj
    [("name",Lean.toJson ("r_" ++ label r)),("reference",Lean.toJson ("r_" ++ label r)),
     ("width",Lean.toJson w)])

def main (args : List String) : IO Unit := do
  let out := args.headD "build/storage/paired-validation"
  IO.FS.createDirAll out
  for (name,text) in [("core",PairedValidation.coreText),("chip",PairedValidation.chipText)] do
    match text with
    | .error e => throw (IO.userError e)
    | .ok s => IO.FS.writeFile (out ++ "/" ++ name ++ ".mlir") s
  let core := Lean.Json.mkObj [
    ("inputs",portJson (PairedController.inputs Loader.Machine.inputs)
      (SramAssembly.inputLabel Loader.Machine.inputLabel)),
    ("outputs",portJson (PairedController.outputs Loader.Machine.outputs)
      (SramAssembly.outputLabel Loader.Machine.outputLabel)),
    ("registers",registersJson PairedController.registers PairedController.label)]
  let chip := Lean.Json.mkObj [
    ("inputs",portJson (PairedController.inputs Backend.Policy.chipInputs)
      (SramAssembly.inputLabel Backend.Policy.chipInputLabel)),
    ("outputs",portJson (PairedController.outputs Backend.Policy.chipOutputs)
      (SramAssembly.outputLabel Backend.Policy.chipOutputLabel)),
    ("registers",registersJson PairedController.fullRegisters PairedController.fullLabel)]
  IO.FS.writeFile (out ++ "/assembly.json") ((Lean.Json.mkObj
    [("schema",Lean.toJson (1 : Nat)),("core",core),("chip",chip)]).pretty ++ "\n")
