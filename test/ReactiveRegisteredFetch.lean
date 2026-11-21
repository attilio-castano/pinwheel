import Pinwheel.Compile.I2CRead
import Pinwheel.Hardware.Reactive.RegisteredFetch

open Pinwheel Pinwheel.Hardware Reactive

def main (args : List String) : IO Unit := do
  let out ← match args with
    | [out] => pure out
    | _ => throw (IO.userError "usage: ReactiveRegisteredFetch.lean <out-directory>")
  IO.FS.createDirAll out
  let variants := [
    ("baseline", Core.directModule),
    ("low", RegisteredFetch.moduleText "pinwheel_reactive_registered_low" 37),
    ("late", RegisteredFetch.moduleText "pinwheel_reactive_registered_late" 36)]
  for (name, result) in variants do
    match result with
    | .ok mlir => IO.FS.writeFile s!"{out}/{name}.mlir" mlir
    | .error message => throw (IO.userError message)
  let program := Compile.I2CRead.program ⟨3, 7⟩ ⟨0x53, 0xa6⟩
  let numbers := [program.last.val, program.idle.levels.toNat, program.idle.enabled.toNat] ++
    (Execution.imageWords program).toList.map BitVec.toNat
  IO.FS.writeFile s!"{out}/images.txt" ("i2c-read " ++ String.intercalate " " (numbers.map toString) ++ "\n")
