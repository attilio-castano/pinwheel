import Pinwheel.Hardware.Storage.TiledController
import Lean.Data.Json

open Pinwheel.Hardware Pinwheel.Hardware.Storage

private def portsJson (ps : Array (Sigma P)) (label : {w : Nat} → P w → String) : Lean.Json :=
  TiledMap.portsJson ps label

private def slotJson (name : String) (w : Nat) (reference : String) : Lean.Json :=
  Lean.Json.mkObj [("name", Lean.toJson name), ("width", Lean.toJson w),
    ("reference", Lean.toJson reference)]

def main (args : List String) : IO Unit := do
  let out := args.headD "build/storage/tiled-chip"
  IO.FS.createDirAll out
  for (name, emission) in [("chip-logic", TiledController.chipText),
      ("core-logic", TiledController.coreText), ("baseline-chip", SramAssembly.chipText false),
      ("baseline-core", SramAssembly.coreText false)] do
    match emission with
    | .ok text => IO.FS.writeFile (out ++ "/" ++ name ++ ".mlir") text
    | .error e => throw (IO.userError e)
  let chipSlots := TiledController.chipRegisters.map fun ⟨w, r⟩ =>
    slotJson ("engine.r_" ++ SramAssembly.registerLabel r) w
      ("r_" ++ SramAssembly.registerLabel r)
  let coreLabel : {w : Nat} → SramController.Register w → String :=
    Backend.Policy.registerLabel SramAssembly.extraLabel
  let coreSlots := TiledController.coreRegisters.map fun ⟨w, r⟩ =>
    slotJson ("engine.r_" ++ coreLabel r) w ("r_" ++ coreLabel r)
  let mapSlots := (#[false, true]).flatMap fun b =>
    TiledMap.lows.flatMap fun low => TiledMap.lows.map fun high =>
      let word := MapTile.wordAddress low high
      slotJson ("map." ++ TiledMap.tileName b low ++ s!".r_word{high.toNat}") 5
        ("r_" ++ SramAssembly.registerLabel (.inner (.inner (.inner (.inner (.inner (.index b word)))))))
  let coreMapSlots := (#[false, true]).flatMap fun b =>
    TiledMap.lows.flatMap fun low => TiledMap.lows.map fun high =>
      let word := MapTile.wordAddress low high
      slotJson ("map." ++ TiledMap.tileName b low ++ s!".r_word{high.toNat}") 5
        ("r_" ++ coreLabel (.inner (.index b word)))
  let part (ins outs regs : Lean.Json) := Lean.Json.mkObj
    [("inputs", ins), ("outputs", outs), ("registers", regs)]
  let manifest := Lean.Json.mkObj [
    ("schema", Lean.toJson (1 : Nat)),
    ("chip", part
      (portsJson (SramAssembly.inputs Backend.Policy.chipInputs)
        (SramAssembly.inputLabel Backend.Policy.chipInputLabel))
      (portsJson (SramAssembly.outputs Backend.Policy.chipOutputs)
        (SramAssembly.outputLabel Backend.Policy.chipOutputLabel))
      (Lean.toJson (chipSlots ++ mapSlots))),
    ("core", part
      (portsJson (SramAssembly.inputs Loader.Machine.inputs)
        (SramAssembly.inputLabel Loader.Machine.inputLabel))
      (portsJson (SramAssembly.outputs Loader.Machine.outputs)
        (SramAssembly.outputLabel Loader.Machine.outputLabel))
      (Lean.toJson (coreSlots ++ coreMapSlots)))]
  IO.FS.writeFile (out ++ "/assembly.json") (manifest.pretty ++ "\n")
