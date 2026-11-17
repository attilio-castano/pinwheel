import Lean.Data.Json
import Pinwheel.Hardware.Processor.CoreModel
import Pinwheel.Hardware.Processor.AddressMap

/-! Upstream ACT4 execution adapter. This is finite executable validation, not
an ISA or RTL proof. All ROM/RAM bytes are supplied explicitly by the runner.
The controller uses owned deferred fetch/data replies, with deterministic stalls.
MMIO and traps are rejected: the admitted upstream I bodies must terminate at
the explicit adapter stop address with a0=1. FENCE has serialized local service.
-/
open Lean Pinwheel.Hardware Pinwheel.Hardware.Processor RV32I
namespace ArchitectureTestTrace

def layout : AddressMap.Layout 20 18 :=
  ⟨⟨0x1000000, 0x40000000, 0x40000100, 0x40000200⟩, by decide +kernel⟩

def readBytes (bytes : ByteArray) (offset count : Nat) : Nat :=
  (List.range count).foldl (fun n k => n + bytes[offset+k]!.toNat * 2^(8*k)) 0

def memFault : AddressMap.Fault → Semantics.MemoryFault
  | .misaligned => .misaligned | .access => .accessFault

/-- Reads return selected low bytes; the instruction semantics performs extension.
Stores commit only on the actual deferred response edge. -/
def service (intent : Semantics.Intent) (rom ram : ByteArray) :
    Except String (CoreModel.DataReply × ByteArray × Json × Json) := do
  match intent with
  | .load address size _ =>
    match AddressMap.route layout ⟨.load,size,address⟩ with
    | .error f => return (.fault (memFault f),ram,Json.null,Json.null)
    | .ok hit =>
      let bytes ← match hit.region with
        | .rom => pure rom | .ram => pure ram | _ => throw "MMIO excluded from ACT4 adapter"
      let value := readBytes bytes hit.relative size.bytes
      return (.success (BitVec.ofNat 32 value),ram,Json.null,toJson [address.toNat,size.bytes,value])
  | .store address size operand =>
    match AddressMap.route layout ⟨.store,size,address⟩ with
    | .error f => return (.fault (memFault f),ram,Json.null,Json.null)
    | .ok hit =>
      unless hit.region == .ram do throw "MMIO excluded from ACT4 adapter"
      let next := (List.range size.bytes).foldl (fun b k =>
        b.set! (hit.relative+k) (UInt8.ofNat (operand.toNat / 2^(8*k) % 256))) ram
      return (.success 0,next,toJson [address.toNat,size.bytes,operand.toNat % 2^(8*size.bytes)],Json.null)
  | .fenceAll => throw "FENCE must use local controller service"

def same (a b : Semantics.State) : Bool :=
  a.pc == b.pc && (List.finRange 31).all (fun k => a.registers k == b.registers k)

/-- Materialize the finite register bank to avoid retaining nested function updates. -/
def snapshot (s : Semantics.State) : Semantics.State :=
  let values := ((List.finRange 31).map s.registers).toArray
  ⟨s.pc, fun k => values[k.val]!⟩

def archJson (s : Semantics.State) : Json :=
  toJson ((List.range 32).map fun k => (Semantics.read s.registers (BitVec.ofNat 5 k)).toNat)

def runOne (j : Json) : IO Json := do
  let romPath ← IO.ofExcept (j.getObjValAs? String "rom")
  let ramPath ← IO.ofExcept (j.getObjValAs? String "ram")
  let tracePath ← IO.ofExcept (j.getObjValAs? String "trace")
  let finalPath ← IO.ofExcept (j.getObjValAs? String "final_ram")
  let stop ← IO.ofExcept (j.getObjValAs? Nat "stop")
  let limit ← IO.ofExcept (j.getObjValAs? Nat "limit")
  let rom ← IO.FS.readBinFile romPath
  let mut ram ← IO.FS.readBinFile ramPath
  unless rom.size == 0x400000 && ram.size == 0x100000 && stop < rom.size && stop % 4 == 0 do
    throw (IO.userError "Malformed complete ROM/RAM image or stop address")
  let handle ← IO.FS.Handle.mk tracePath .write
  let mut state := CoreModel.initial
  let mut architectural := CoreModel.boot
  let mut fetched : Option CoreModel.FetchReply := none
  let mut pending : Option Semantics.Intent := none
  let mut cycles := 0
  let mut retired := 0
  let mut fetchCount := 0
  let mut dataCount := 0
  let mut complete := false
  for cycle in [:limit*9+20] do
    if state.arch.pc.toNat == stop then
      match state.phase with
      | .fetchRequest => complete := true; break
      | _ => pure ()
    if retired >= limit then throw (IO.userError "Instruction bound exceeded")
    let mut input : CoreModel.Input := {}
    let mut write := Json.null
    let mut read := Json.null
    match state.phase with
    | .fetchRequest =>
      if cycle % 5 != 0 then
        input := {input with fetchReady := true}
        let pc := state.arch.pc
        fetched := some (match AddressMap.route layout ⟨.fetch,.word,pc⟩ with
          | .ok hit => if hit.region == .rom then .instruction (BitVec.ofNat 32 (readBytes rom hit.relative 4)) else .accessFault
          | .error _ => .accessFault)
        fetchCount := fetchCount+1
    | .fetchResponse =>
      if cycle % 7 != 0 then
        unless fetched.isSome do throw (IO.userError "Fetch response has no owned request")
        input := {input with fetchResponse := fetched}
        fetched := none
    | .dataRequest request =>
      if cycle % 5 != 1 then
        unless pending.isNone do throw (IO.userError "Duplicate outstanding data request")
        pending := some request.intent
        input := {input with dataService := some .deferred}
    | .dataResponse request =>
      if cycle % 7 != 2 then
        let some intent := pending | throw (IO.userError "Data response has no owned request")
        unless intent == request.intent do throw (IO.userError "Captured data request changed")
        let (reply,next,effect,received) ← IO.ofExcept (service intent rom ram)
        input := {input with dataResponse := some reply}
        ram := next
        write := effect
        read := received
        pending := none
        dataCount := dataCount+1
    | _ => pure ()
    let (next,event) := CoreModel.tick input state
    match event with
    | some (.retired word completion after) =>
      unless same architectural state.arch do throw (IO.userError "Controller changed architecture before completion")
      let expected ← match Semantics.step architectural word with
        | .retired _ after => pure after
        | .trapped _ _ _ => throw (IO.userError "Architectural instruction trapped")
        | .pending p =>
          let reply ← match p,completion with
            | .load _ _ _ _,.data .deferred _ r => pure r
            | .store _ _ _ _,.data .deferred _ r => pure r
            | .fence _,.fence => pure (.success 0)
            | _,_ => throw (IO.userError "Completion path disagrees with instruction")
          let result := match p with
            | .load c op rd address =>
              match reply with
              | .success data => Semantics.finish (.load c op rd address) (.loaded data)
              | .fault f => Semantics.finish (.load c op rd address) (.loadFault f)
            | .store c op address value =>
              match reply with
              | .success _ => Semantics.finish (.store c op address value) .stored
              | .fault f => Semantics.finish (.store c op address value) (.storeFault f)
            | .fence c => Semantics.finish (.fence c) .fenced
          match result with
          | .retired _ after => pure after
          | _ => throw (IO.userError "Architectural completion did not retire")
      unless same expected after && same after next.arch do throw (IO.userError "Semantic/controller state mismatch")
      handle.putStrLn (Json.mkObj [("pc",toJson state.arch.pc.toNat),("word",toJson word.toNat),
        ("next_pc",toJson after.pc.toNat),("registers",archJson after),("write",write),("read",read)]).compress
      architectural := snapshot after
      retired := retired+1
    | some (.trapped _ _) => throw (IO.userError s!"Unexpected controller trap at {state.arch.pc.toNat}")
    | some .reset => throw (IO.userError "Unexpected reset")
    | none =>
      unless same state.arch next.arch do throw (IO.userError "Silent architectural change")
      unless write == Json.null && read == Json.null do throw (IO.userError "RAM effect without retirement")
    state := if event.isSome then {next with arch := snapshot next.arch} else next
    cycles := cycles+1
  unless complete && pending.isNone && fetched.isNone && retired == fetchCount do
    throw (IO.userError "Incomplete execution or request accounting mismatch")
  unless (Semantics.read state.arch.registers 10).toNat == 1 do
    throw (IO.userError "Upstream test reported failure")
  IO.FS.writeBinFile finalPath ram
  return Json.mkObj [("retired",toJson retired),("cycles",toJson cycles),("fetches",toJson fetchCount),
    ("data_completions",toJson dataCount),("stop",toJson stop),("registers",archJson state.arch)]
end ArchitectureTestTrace

def main (args : List String) : IO Unit := do
  let [jobs,results] := args | throw (IO.userError "ArchitectureTestTrace JOBS.jsonl RESULTS.jsonl")
  let handle ← IO.FS.Handle.mk results .write
  for line in (← IO.FS.readFile jobs).splitOn "\n" do
    if line.isEmpty then continue
    let result ← ArchitectureTestTrace.runOne (← IO.ofExcept (Json.parse line))
    handle.putStrLn result.compress
    IO.println s!"ACT4 local: {result.compress}"
