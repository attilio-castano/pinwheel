import Pinwheel.Hardware.Storage.Capacity
import Pinwheel.Compile.UART
import Pinwheel.Compile.SPI
import Pinwheel.Engine.Compatibility

open Pinwheel Pinwheel.Hardware

private def check (p : Reactive.Program) : IO Nat := do
  let words := Execution.imageWords p
  let n := words.toList.eraseDups.length
  match Storage.lower32 words with
  | none => throw (IO.userError s!"32-entry overflow: {n}")
  | some lowered =>
    unless lowered.val.expand == words do throw (IO.userError "lookup mismatch")
  return n

def main : IO Unit := do
  IO.FS.createDirAll "build/storage"
  let mut uart := 0
  let mut spi := 0
  for d in [0, 1, 3, 255] do
    for b in [:256] do
      uart := max uart (← check (Execution.widenProgram (Engine.Reactive.embedProgram (Compile.UART.program ⟨Fin.ofNat 256 d⟩ (BitVec.ofNat 8 b)))))
      spi := max spi (← check (Execution.widenProgram (Engine.Reactive.embedProgram (Compile.SPI.program ⟨Fin.ofNat 256 d⟩ (BitVec.ofNat 8 b)))))
  IO.println s!"UART/SPI: 1,024 configurations each; maxima {uart}/{spi}."
  let mut write := 0
  let mut read := 0
  for address in [:128] do
    for byte in [:256] do
      write := max write (← check (Execution.widenProgram (Compile.I2C.program ⟨3, 7⟩ ⟨Fin.ofNat 128 address, BitVec.ofNat 8 byte⟩)))
      read := max read (← check (Compile.I2CRead.program ⟨3, 7⟩ ⟨Fin.ofNat 128 address, BitVec.ofNat 8 byte⟩))
  IO.println s!"I2C: all 32,768 address/data combinations each; maxima {write}/{read}."
  let mut timingWrite := 0
  let mut timingRead := 0
  for duration in [:256] do
    for budget in [:256] do
      let cfg : I2C.Config := ⟨Fin.ofNat 256 duration, Fin.ofNat 256 budget⟩
      timingWrite := max timingWrite (← check (Execution.widenProgram (Compile.I2C.program cfg ⟨0x53, 0xa6⟩)))
      timingRead := max timingRead (← check (Compile.I2CRead.program cfg ⟨0x53, 0xa6⟩))
  IO.println s!"I2C: all 65,536 timer pairs each at fixed payload; maxima {timingWrite}/{timingRead}."
  let overflow : Execution.Words := Vector.ofFn fun k =>
    Execution.encode (.action ⟨⟨BitVec.ofNat 3 k.val, 7⟩, Fin.ofNat 256 k.val, none⟩)
  unless (Storage.lower32 overflow).isNone do throw (IO.userError "oversized image accepted")
  IO.FS.writeFile "build/storage/capacity.json"
    s!"\{\"uart_max\":{uart},\"spi_max\":{spi},\"write_payload_max\":{write},\"read_payload_max\":{read},\"write_timing_max\":{timingWrite},\"read_timing_max\":{timingRead},\"configurations\":198656,\"overflow_rejected\":true,\"boundary\":\"Payload and timing sweeps are separate, not their Cartesian product; every accepted image has a lookup certificate.\"}\n"
