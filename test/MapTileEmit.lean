import Pinwheel.Hardware.Storage.TiledMap
import Pinwheel.Hardware.Emit

open Pinwheel.Hardware Pinwheel.Hardware.Storage

open TiledMap

def main (args : List String) : IO Unit := do
  let out := args.headD "build/storage/map-tile"
  IO.FS.createDirAll out
  for (name, result) in #[
      ("tile", Emit.moduleText "pinwheel_map_tile" MapTile.circuit tileInputs tileRegisters outputs
        tileInputLabel tileRegisterLabel outputLabel),
      ("flat", Emit.moduleText "pinwheel_map_flat" flat inputs registers outputs
        inputLabel registerLabel outputLabel),
      ("glue", Emit.moduleText "pinwheel_map_glue" glue glueInputs #[] glueOutputs
        glueInputLabel (fun r => nomatch r) glueOutputLabel)] do
    match result with
    | .ok text => IO.FS.writeFile (out ++ "/" ++ name ++ ".mlir") text
    | .error e => throw (IO.userError e)
  let manifest := Lean.Json.mkObj [
    ("inputs", portsJson inputs inputLabel), ("outputs", portsJson outputs outputLabel),
    ("tile_inputs", portsJson tileInputs tileInputLabel),
    ("glue_inputs", portsJson glueInputs glueInputLabel),
    ("glue_outputs", portsJson glueOutputs glueOutputLabel),
    ("tiles", Lean.toJson ((#[false, true]).flatMap fun bank => lows.map fun low =>
      Lean.Json.mkObj [("name", Lean.toJson (tileName bank low)),
        ("bank", Lean.toJson (if bank then 1 else 0)), ("low", Lean.toJson low.toNat),
        ("words", Lean.toJson (lows.map fun high => (MapTile.wordAddress low high).toNat))]))]
  IO.FS.writeFile (out ++ "/manifest.json") (manifest.pretty ++ "\n")
