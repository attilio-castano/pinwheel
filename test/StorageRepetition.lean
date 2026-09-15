import Pinwheel.Hardware.Storage.RepetitionCircuit

open Pinwheel Pinwheel.Hardware
open Pinwheel.Hardware.Storage.Repetition

def main : IO Unit := do
  IO.FS.createDirAll "build/storage/repetition"
  let mut checked := 0
  for a in [:128] do
    for d in [:256] do
      let some image := lower ⟨3, 7⟩ ⟨Fin.ofNat 128 a, BitVec.ofNat 8 d⟩
        | throw (IO.userError s!"repetition lookup mismatch at {a},{d}")
      if a == 0x53 && d == 0xa6 then
        let stream := image.val.templates.toList ++ image.val.bytes.toList.map (fun x => BitVec.ofNat 64 x.toNat) ++
          image.val.descriptors.toList.map (fun x => BitVec.ofNat 64 x.toNat) ++ List.replicate 299 (4#64) ++ [0, 78]
        IO.FS.writeFile "build/storage/repetition/image.txt" (String.intercalate " " (stream.map (toString ∘ BitVec.toNat)) ++ "\n")
      checked := checked+1
    if a % 32 == 31 then IO.println s!"Repetition: {checked} certified address/data pairs."
  for duration in [0, 1, 255] do
    for budget in [0, 1, 255] do
      let some _ := lower ⟨Fin.ofNat 256 duration, Fin.ofNat 256 budget⟩ ⟨0x53, 0xa6⟩
        | throw (IO.userError "repetition timer boundary mismatch")
      checked := checked+1
  IO.FS.writeFile "build/storage/repetition/capacity.json" s!"\{\"certified_images\":{checked},\"addresses_per_image\":256}\n"
