import Pinwheel.Hardware.Storage.RepetitionEmit

open Pinwheel Pinwheel.Hardware

def main : IO Unit := do
  IO.FS.createDirAll "build/storage/repetition"
  match Loader.Machine.RepetitionEmit.moduleText with
  | .ok text => IO.FS.writeFile "build/storage/repetition.mlir" text
  | .error e => throw (IO.userError e)
  for (name, request) in [("image", (⟨0x53, 0xa6⟩ : I2C.Request)), ("changed", ⟨0x12, 0x5a⟩)] do
    let some image := Storage.Repetition.lower ⟨3, 7⟩ request
      | throw (IO.userError "uncertified repetition image")
    let stream := image.val.templates.toList ++ image.val.bytes.toList.map (fun x => BitVec.ofNat 64 x.toNat) ++
      image.val.descriptors.toList.map (fun x => BitVec.ofNat 64 x.toNat) ++ List.replicate 299 (4#64) ++ [0, 78]
    let text (xs : List (BitVec 64)) := String.intercalate " " (xs.map (toString ∘ BitVec.toNat)) ++ "\n"
    IO.FS.writeFile s!"build/storage/repetition/{name}.txt" (text stream)
    IO.FS.writeFile s!"build/storage/repetition/{name}-explicit.txt"
      (text (Execution.imageWords (Execution.widenProgram (Compile.I2C.program ⟨3, 7⟩ request))).toList)
