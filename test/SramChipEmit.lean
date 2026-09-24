import Pinwheel.Hardware.Storage.SramAssembly
import Lean.Data.Json

/-! Serialize the shared SRAM chip assembly without changing its circuit. -/

open Pinwheel.Hardware.Storage.SramAssembly

private def assemblyJson (direct : Bool) : Except String Lean.Json := do
  let probes ← computationNames direct
  return Lean.Json.mkObj [
  ("schema", Lean.toJson (1 : Nat)),
  ("variant", Lean.toJson (if direct then "direct" else "hybrid")),
  ("owners", Lean.toJson (physicalOwners.map Owner.label)),
  ("owner_regions", Lean.Json.mkObj (physicalOwners.toList.map fun o => (o.label, Lean.toJson o.region))),
  ("computations", Lean.Json.arr (probes.map fun (name, width, value) => Lean.Json.mkObj [
    ("name", Lean.toJson name), ("width", Lean.toJson width), ("mlir_value", Lean.toJson value)])),
  ("registers", Lean.Json.arr ((stateSlots direct).map fun slot => Lean.Json.mkObj [
    ("name", Lean.toJson slot.name), ("width", Lean.toJson slot.width),
    ("owner", Lean.toJson slot.owner.label),
    ("index_location", match slot.indexLocation with
      | none => Lean.Json.null
      | some (bank, word) => Lean.Json.mkObj [
          ("bank", Lean.toJson (if bank then (1 : Nat) else 0)),
          ("word", Lean.toJson word.toNat)])])),
  ("crossings", Lean.Json.arr ((crossings direct).map fun c => Lean.Json.mkObj [
    ("name", Lean.toJson c.name), ("width", Lean.toJson c.width),
    ("producer", Lean.toJson c.producer), ("consumers", Lean.toJson c.consumers),
    ("phase", Lean.toJson c.phase.label), ("macro_port", Lean.toJson c.macroPort),
    ("physical_width", Lean.toJson c.physicalWidth)]))]

def main (args : List String) : IO Unit := do
  let out := args.headD "build/storage/sram-chip"
  IO.FS.createDirAll out
  for (direct, name) in [(true, "direct"), (false, "hybrid")] do
    for (kind, result) in [("chip", Pinwheel.Hardware.Storage.SramAssembly.chipText direct), ("core", Pinwheel.Hardware.Storage.SramAssembly.coreText direct)] do
      match result with
      | .ok text => IO.FS.writeFile (out ++ s!"/{name}-{kind}.mlir") text
      | .error e => throw (IO.userError e)
    let bits := (Pinwheel.Hardware.Storage.SramAssembly.chipRegisters direct).foldl (fun n p => n + p.1) 35
    match assemblyJson direct with
    | .ok manifest => IO.FS.writeFile (out ++ s!"/{name}-assembly.json") (manifest.pretty ++ "\n")
    | .error e => throw (IO.userError e)
    IO.println s!"{name}: {bits} controller register bits, two external synchronous SRAM responses"
