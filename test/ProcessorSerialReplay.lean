import Pinwheel.Hardware.Processor.SerialCircuit
import Lean.Data.Json

open Lean Pinwheel.Hardware Pinwheel.Hardware.Processor
namespace ProcessorSerialReplay
private def snapshot (d : Interface P) (bank : Values P) : Array Nat :=
  d.ports.map (fun ⟨_,p⟩ => (bank p).toNat)
private def values (d : Interface P) (bank : Array Nat) : Values P :=
  fun {w} p => BitVec.ofNat w bank[(d.position p).val]!
private def input (j : Json) : Except String (Values SerialInterface.Input) := do
  let reset ← j.getObjValAs? Bool "reset"
  let valid ← j.getObjValAs? Bool "request_valid"
  let device ← j.getObjValAs? Nat "device"
  let write ← j.getObjValAs? Bool "write"
  let word ← j.getObjValAs? Nat "word"
  let data ← j.getObjValAs? Nat "data"
  let gpio ← j.getObjValAs? Nat "gpio_input"
  let rx ← j.getObjValAs? Bool "rx"
  unless device < 4 && word < 64 && data < 2^32 && gpio < 2^32 do throw "Input exceeds wire width"
  return values SerialInterface.inputs #[reset.toNat,valid.toNat,device,write.toNat,word,data,gpio,rx.toNat]

def replay (d : Uart.Timing) (stimulus result : String) : IO Unit := do
  let ri := SerialCircuit.registers d
  let oi := SerialInterface.outputs
  let c := SerialCircuit.circuit d
  let raw ← IO.ofExcept (Json.parse (← IO.FS.readFile stimulus))
  let segments ← IO.ofExcept raw.getArr?
  let mut frames : Array String := #[]
  let mut cycle := 0
  for segment in segments do
    let mut bank ← IO.ofExcept (segment.getObjValAs? (Array Nat) "startup")
    unless bank.size == ri.size do throw (IO.userError "Wrong startup register count")
    for (port,value) in ri.ports.zip bank do
      unless value < 2^port.1 do throw (IO.userError "Startup register exceeds wire width")
    let rows ← IO.ofExcept (segment.getObjValAs? (Array Json) "rows")
    for raw in rows do
      let i ← IO.ofExcept (input raw)
      let before := snapshot oi (c.observe i (values ri bank))
      bank := snapshot ri (c.step i (values ri bank))
      let after := snapshot oi (c.observe i (values ri bank))
      frames := frames.push (Json.mkObj [("cycle",toJson cycle),("input",raw),
        ("pre",toJson before),("post",toJson after),("registers",toJson bank)]).compress
      cycle := cycle+1
  if cycle == 0 then throw (IO.userError "Empty stimulus")
  IO.FS.writeFile result (String.intercalate "\n" frames.toList ++ "\n")
  IO.println s!"Serial D{d.divisor}: {cycle} physical transitions replayed."
end ProcessorSerialReplay

def main (args : List String) : IO Unit := do
  let [divisor,stimulus,result] := args | throw (IO.userError "Usage: serial_replay divisor segments.json trace.jsonl")
  let some n := divisor.toNat? | throw (IO.userError "Invalid divisor")
  if h : 4 ≤ n ∧ n % 2 = 0 then ProcessorSerialReplay.replay ⟨n,h.1,h.2⟩ stimulus result
  else throw (IO.userError "Divisor must be even and at least four")
