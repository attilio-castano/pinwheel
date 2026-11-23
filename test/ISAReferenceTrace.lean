import Lean.Data.Json
import Pinwheel.Hardware.Processor.RV32I.Semantics
import Pinwheel.Hardware.Processor.AddressMap

/-! Architectural differential adapter, not a CPU implementation. ROM/RAM use
the frozen checked address map. MMIO is explicitly outside this adapter: a
device hit is rejected rather than silently assigned upstream device behavior.
Each pending load/store/fence is completed once, synchronously for ISA testing.
-/
open Lean Pinwheel.Hardware Pinwheel.Hardware.Processor RV32I Semantics

namespace ISAReferenceTrace

def layout : AddressMap.Layout 10 10 :=
  ⟨⟨0x10000, 0x40000000, 0x40000100, 0x40000200⟩, by decide +kernel⟩

def memoryFault : AddressMap.Fault → MemoryFault
  | .misaligned => .misaligned
  | .access => .accessFault

def trapJson : Trap → Json
  | .illegalInstruction => Json.mkObj [("cause",toJson (2 : Nat)),("target",Json.null)]
  | .environmentCall => Json.mkObj [("cause",toJson (11 : Nat)),("target",Json.null)]
  | .breakpoint => Json.mkObj [("cause",toJson (3 : Nat)),("target",Json.null)]
  | .instructionAddressMisaligned a => Json.mkObj [("cause",toJson (0 : Nat)),("target",toJson a.toNat)]
  | .loadFault f a => Json.mkObj [("cause",toJson (if f == .misaligned then 4 else 5 : Nat)),("target",toJson a.toNat)]
  | .storeFault f a => Json.mkObj [("cause",toJson (if f == .misaligned then 6 else 7 : Nat)),("target",toJson a.toNat)]

def intentJson : Pending → Json
  | .load _ op _ a => Json.mkObj [("kind",toJson "load"),("address",toJson a.toNat),
      ("bytes",toJson (loadSize op).bytes),("signed",toJson (loadSigned op))]
  | .store _ op a v => Json.mkObj [("kind",toJson "store"),("address",toJson a.toNat),
      ("bytes",toJson (storeSize op).bytes),("operand",toJson v.toNat)]
  | .fence _ => Json.mkObj [("kind",toJson "fence_all")]

def readBytes (bytes : Array Nat) (offset count : Nat) : Nat :=
  (List.range count).foldl (fun n k => n + bytes[offset+k]! * 2^(8*k)) 0

def complete (pending : Pending) (rom ram : Array Nat) : Except String (Outcome × Array Nat) := do
  match pending with
  | .load origin op dest a =>
      let p := Pending.load origin op dest a
      match AddressMap.route layout ⟨.load,loadSize op,a⟩ with
      | .error f => return (finish p (.loadFault (memoryFault f)),ram)
      | .ok h =>
          let bytes ← match h.region with
            | .rom => pure rom
            | .ram => pure ram
            | _ => throw "MMIO completion is deliberately excluded from external ISA comparison"
          let data := BitVec.ofNat 32 (readBytes bytes h.relative (loadSize op).bytes)
          return (finish p (.loaded data),ram)
  | .store origin op a v =>
      let p := Pending.store origin op a v
      match AddressMap.route layout ⟨.store,storeSize op,a⟩ with
      | .error f => return (finish p (.storeFault (memoryFault f)),ram)
      | .ok h =>
          unless h.region == .ram do throw "MMIO completion is deliberately excluded from external ISA comparison"
          let next := (List.range (storeSize op).bytes).foldl
            (fun bytes k => bytes.set! (h.relative+k) (v.toNat / 2^(8*k) % 256)) ram
          return (finish p .stored,next)
  | .fence origin => return (finish (.fence origin) .fenced,ram)

def replayOne (j : Json) : Except String Json := do
  let id ← j.getObjValAs? Nat "id"
  let pc ← j.getObjValAs? Nat "pc"
  let word ← j.getObjValAs? Nat "word"
  let registers ← j.getObjValAs? (Array Nat) "registers"
  let ram ← j.getObjValAs? (Array Nat) "ram"
  unless pc < 4096 && pc % 4 == 0 && word < 2^32 && registers.size == 32 &&
      registers[0]! == 0 && registers.all (· < 2^32) && ram.size == 4096 && ram.all (· < 256) do
    throw "Malformed ISA case or unsupported fetch window"
  let rom := (List.range 4).foldl (fun bytes k => bytes.set! (pc+k) (word / 2^(8*k) % 256))
    (Array.replicate 4096 0)
  let state : State := ⟨BitVec.ofNat 32 pc, fun k => BitVec.ofNat 32 registers[k.val+1]!⟩
  let initial := step state (BitVec.ofNat 32 word)
  let (result, memory, intent) ← match initial with
    | .pending p => do
        let (result, memory) ← complete p rom ram
        pure (result,memory,intentJson p)
    | result => pure (result,ram,Json.null)
  let fault := match result with | .trapped _ _ f => trapJson f | _ => Json.null
  return Json.mkObj [("id",toJson id),("word",toJson result.word.toNat),
    ("pc",toJson result.state.pc.toNat),
    ("registers",toJson ((List.range 32).map fun k => (read result.state.registers (BitVec.ofNat 5 k)).toNat)),
    ("ram",toJson memory),("trap",fault),("intent",intent)]

end ISAReferenceTrace

def main (args : List String) : IO Unit := do
  let [source,destination] := args | throw (IO.userError "ISAReferenceTrace CASES.jsonl TRACE.jsonl")
  let mut results := #[]
  for line in (← IO.FS.readFile source).splitOn "\n" do
    if line.isEmpty then continue
    let result ← IO.ofExcept (Json.parse line >>= ISAReferenceTrace.replayOne)
    results := results.push result.compress
  unless results.size > 0 do throw (IO.userError "Empty ISA campaign")
  IO.FS.writeFile destination (String.intercalate "\n" results.toList ++ "\n")
  IO.println s!"ISA reference adapter: {results.size} architectural outcomes."
