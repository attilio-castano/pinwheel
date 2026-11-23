import Pinwheel.Hardware.Processor.MmioCircuit
import Lean.Data.Json

open Lean Pinwheel.Hardware Pinwheel.Hardware.Processor

namespace ProcessorMmioReplay

private def snapshot (d : Interface P) (bank : Values P) : Array Nat :=
  d.ports.map (fun ⟨_, p⟩ => (bank p).toNat)

private def values (d : Interface P) (bank : Array Nat) : Values P :=
  fun {w} p => BitVec.ofNat w bank[(d.position p).val]!

private def input (j : Json) : Except String (Values MmioInterface.Input) := do
  let reset ← j.getObjValAs? Bool "reset"
  let valid ← j.getObjValAs? Bool "request_valid"
  let device ← j.getObjValAs? Nat "device"
  let write ← j.getObjValAs? Bool "write"
  let word ← j.getObjValAs? Nat "word"
  let data ← j.getObjValAs? Nat "data"
  let gpio ← j.getObjValAs? Nat "gpio_input"
  let complete ← j.getObjValAs? Bool "tx_complete"
  let rxValid ← j.getObjValAs? Bool "rx_valid"
  let rxData ← j.getObjValAs? Nat "rx_data"
  let framing ← j.getObjValAs? Bool "framing_error"
  unless device < 4 && word < 64 && data < 2^32 && gpio < 2^32 && rxData < 256 do
    throw "Input exceeds wire width"
  return values MmioInterface.inputs
    #[reset.toNat, valid.toNat, device, write.toNat, word, data, gpio,
      complete.toNat, rxValid.toNat, rxData, framing.toNat]

def replay (stimulus startup result : String) : IO Unit := do
  let ri := MmioCircuit.registers
  let oi := MmioInterface.outputs
  let c := MmioCircuit.circuit
  let raw ← IO.ofExcept (Json.parse (← IO.FS.readFile startup))
  let mut bank ← IO.ofExcept (fromJson? raw : Except String (Array Nat))
  unless bank.size == ri.size do throw (IO.userError "Wrong startup register count")
  for (port, value) in ri.ports.zip bank do
    unless value < 2^port.1 do throw (IO.userError s!"Startup register exceeds its {port.1}-bit wire width")
  let mut rows : Array String := #[]
  let mut cycle := 0
  for line in (← IO.FS.readFile stimulus).splitOn "\n" do
    if line.isEmpty then continue
    let raw ← IO.ofExcept (Json.parse line)
    let i ← IO.ofExcept (input raw)
    let before := snapshot oi (c.observe i (values ri bank))
    bank := snapshot ri (c.step i (values ri bank))
    let after := snapshot oi (c.observe i (values ri bank))
    rows := rows.push (Json.mkObj [("cycle", toJson cycle), ("input", raw),
      ("pre", toJson before), ("post", toJson after), ("registers", toJson bank)]).compress
    cycle := cycle+1
  if cycle == 0 then throw (IO.userError "Stimulus must contain at least one edge")
  IO.FS.writeFile result (String.intercalate "\n" rows.toList ++ "\n")
  IO.println s!"MMIO: {cycle} physical transitions replayed."

end ProcessorMmioReplay

def main (args : List String) : IO Unit := do
  let [stimulus, startup, result] := args
    | throw (IO.userError "Usage: processor_mmio_replay stimulus.jsonl startup.json trace.jsonl")
  ProcessorMmioReplay.replay stimulus startup result
