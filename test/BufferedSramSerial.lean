import Pinwheel.Hardware.Buffered.SerialModel
import Pinwheel.Hardware.Buffered.SerialProofs

open Pinwheel.Hardware Pinwheel.Hardware.Buffered
open Serial

private def check (ok : Bool) (label : String) : IO Unit :=
  unless ok do throw (IO.userError ("Buffered SRAM serial fixture: " ++ label))
private def values (a : Array Nat) : Values Register := fun {w} r =>
  BitVec.ofNat w (a[registerIndex r]?.getD 0)
private def snapshot (s : Values Register) : Array Nat :=
  registers.map fun ⟨_,r⟩ => (s r).toNat
private def statusValues (seed : Nat) : Values Reactive.Output := fun {w} o =>
  let index := (Reactive.outputs.toList.map fun ⟨_,p⟩ => Reactive.outputLabel p).idxOf
    (Reactive.outputLabel o)
  BitVec.ofNat w (seed*137 + index*29 + 1)

private structure Run where
  model : State := {csnPrev := false}
  bank : Array Nat := registers.map fun _ => 0
  edges : Nat := 0
  deliveries : Nat := 0

/-- Every edge checks the record description against the actual ordinary
Circuit.step/observe, all thirteen next-register roots and all core inputs. -/
private def tick (r : Run) (i : Inputs) : IO Run := do
  let actual : Values Register := values r.bank
  for ⟨_,p⟩ in Reactive.inputs do
    check (circuit.observe i.values actual (.core p) == r.model.coreInput i p)
      s!"edge{r.edges} core_{Reactive.inputLabel p}"
  check (circuit.observe i.values actual .miso == r.model.miso i) s!"edge{r.edges} MISO"
  check (circuit.observe i.values actual .ready == r.model.readyOutput i) s!"edge{r.edges} READY"
  let model := r.model.step i
  let bank := snapshot (circuit.step i.values actual)
  check (bank == snapshot model.values) s!"edge{r.edges} all typed registers"
  let pulse := (circuit.observe i.values actual (.core .command)).toNat
  return {
    model := model
    bank := bank
    edges := r.edges + 1
    deliveries := r.deliveries + (if pulse != 0 then 1 else 0) }

private def pins (sck csn mosi : Bool) (seed : Nat := 0) : Inputs :=
  { sck, csn, mosi, rawInputs := BitVec.ofNat 2 seed, status := statusValues seed }
private def frame (opcode sequence payload : Nat) (header : Nat := 0xA710) : BitVec 160 :=
  BitVec.ofNat 160 ((header+opcode)*2^144 + sequence*2^128 + payload)

private def send (r : Run) (bits : Nat) (word : BitVec 160) (reject : Bool := false)
    (holdHigh : Bool := false) : IO Run := do
  let mut r ← tick r (pins false true false 1)
  r ← tick r (pins false false false 2)
  for k in [:bits] do
    let bit := if k < 160 then word.getLsbD (159-k) else false
    r ← tick r (pins false false bit (k+3))
    r ← tick r (pins true false bit (k+4))
    if holdHigh then r ← tick r (pins true false (!bit) (k+5))
  r ← tick r (pins false true false 77)
  let dispatchInputs : Inputs := { pins false true false 78 with
    status := fun {w} o => if Reactive.outputLabel o == "rejected" then
      BitVec.ofNat w (if reject then 1 else 0) else statusValues 78 o }
  r ← tick r dispatchInputs
  r ← tick r (pins false true false 79)
  check r.model.ready "response generated after dispatch/capture"
  return r

private def read (r : Run) (bits : Nat) : IO (Run × BitVec 192) := do
  let mut r ← tick r (pins false true false 101)
  r ← tick r (pins false false true 102)
  let mut received : Nat := 0
  for k in [:bits] do
    r ← tick r (pins false false (k%2 == 0) (k+103))
    let bit := r.model.miso (pins true false true (k+104))
    received := 2*received+bit.toNat
    r ← tick r (pins true false true (k+104))
  r ← tick r (pins false true false 197)
  return (r,BitVec.ofNat 192 received)

private def acceptedFrames : IO Nat := do
  let mut total := 0
  for opcode in [0,1,2,3,4,6,7,8] do
    let used := match opcode with
      | 0 => 5 | 1 => 98 | 2 => 24 | 3 => 60 | 4 => 32 | 6 => 60 | _ => 0
    let word := frame opcode (0xC100+opcode) (2^used-1)
    let mut r ← tick {} {cold := true, csn := true, sck := true}
    r ← send r 160 word false (opcode == 1)
    check (r.model.code == 0) s!"opcode{opcode} admitted"
    check (r.model.response.extractLsb' 176 16 == BitVec.ofNat 16 0x5A10)
      "accepted response header"
    check (r.model.response.extractLsb' 160 16 == BitVec.ofNat 16 (0xC100+opcode))
      "echoed request sequence"
    check (r.model.response.extractLsb' 155 5 == 0) "reserved status top bits zero"
    check (r.model.response.getLsbD 4 == false) "dispatch rejection preserved as false"
    check (r.deliveries == if opcode == 0 || opcode == 8 then 0 else 1) "one command pulse"
    let saved := r.model.response
    let (after,got) ← read r 192
    check (!after.model.ready && got == saved) "exact read consumes matching complete snapshot"
    total := total+after.edges
  return total

private def invalidFrames : IO Nat := do
  let mut total := 0
  for (bits,header,opcode,payload,code) in
      [(0,0xA710,1,0,1),(1,0xA710,1,0,1),(159,0xA710,1,0,1),
       (161,0xA710,1,0,1),(193,0xA710,1,0,1),(512,0xA710,1,0,1),
       (160,0xA700,1,0,2),(160,0xB710,1,0,2),(160,0xA710,5,0,3),
       (160,0xA710,15,0,3),(160,0xA710,0,32,3),(160,0xA710,1,2^98,3),
       (160,0xA710,2,2^24,3),(160,0xA710,3,2^60,3),
       (160,0xA710,4,2^32,3),(160,0xA710,6,2^60,3),
       (160,0xA710,7,1,3),(160,0xA710,8,1,3)] do
    let r ← tick {} {cold := true}
    let r ← send r bits (frame opcode 0xEF21 payload header)
    check (r.model.code.toNat == code && r.deliveries == 0) "invalid frame suppressed"
    check (r.model.response.extractLsb' 176 16 == BitVec.ofNat 16 (0x5A10+code))
      "invalid frame diagnostic response"
    check (r.model.sequence.toNat == if bits == 160 then 0xEF21 else 0)
      "length errors have zero sequence"
    if bits > 193 then check (r.model.count == 193) "overlong counter saturation"
    total := total+r.edges
  return total

private def retention : IO Nat := do
  let mut r ← tick {} {cold := true}
  r ← send r 160 (frame 3 19 0) true
  check (r.model.response.extractLsb' 176 16 == 0x5A14 && r.model.response.getLsbD 4)
    "dispatch rejected diagnostic latched over quiet capture"
  let saved := r.model.response
  let initialDeliveries := r.deliveries
  for bits in [0,1,17,191,193,257] do
    let (after,_) ← read r bits
    r := after
    check (r.model.ready && r.model.response == saved && r.deliveries == initialDeliveries)
      "aborted and overlong reads retain snapshot and suppress MOSI commands"
  let (after,got) ← read r 192
  check (!after.model.ready && got == saved) "retry starts at original bit zero"
  return after.edges

private def resetAndEdges : IO Nat := do
  let mut r ← tick {} {cold := true, sck := true, csn := false}
  -- SCK held high and CS held low at POR do not invent a transaction.
  for _ in [:4] do r ← tick r (pins true false true)
  r ← tick r (pins false false true)
  check (!r.model.active && r.model.count == 0 && r.deliveries == 0) "POR pin levels tracked"
  r ← tick r (pins false true false)
  r ← tick r (pins true false true)
  r ← tick r (pins false false true)
  check (!r.model.active) "CS asserted while SCK high requires fresh assertion"
  r ← tick r (pins false true false)
  r ← tick r (pins false false false)
  r ← tick r (pins true false true)
  check (r.model.active && r.model.count == 1) "fresh low-SCK assertion receives"
  r ← tick r {cold := true, sck := true, csn := false}
  check (!r.model.active && !r.model.ready && r.model.request == 0) "POR aborts partial upload"
  r ← send r 160 (frame 8 7 0)
  check (r.model.ready && r.deliveries == 0) "cold core operation preserves serial receipt"
  r ← tick r (pins false false false)
  r ← tick r {cold := true, sck := false, csn := false}
  check (!r.model.active && !r.model.ready && r.model.response == 0) "POR clears response owner"
  return r.edges

/-- Compare arbitrary represented frontend states as well as initialized
transactions. This includes inconsistent pipeline flags and saturated counts;
it does not assume those states are reachable from a host upload. -/
private def representedStates : IO Nat := do
  let mut total := 0
  for seed in [:32] do
    for count in [0,159,160,191,192,193,511] do
      let s : State := {
        sckPrev := seed%2 == 0
        csnPrev := seed%3 == 0
        active := seed%5 == 0
        reading := seed%7 == 0
        count := BitVec.ofNat 9 count
        request := frame (seed%16) (seed*317) ((2^127+seed*173)%2^128)
        dispatch := seed%2 == 0
        capture := seed%3 == 0
        code := BitVec.ofNat 4 seed
        sequence := BitVec.ofNat 16 (seed*373)
        rejected := seed%2 != 0
        response := BitVec.ofNat 192 (2^191 + seed*149*2^83 + seed)
        ready := seed%5 != 0 }
      let mut r : Run := {model := s,bank := snapshot s.values}
      for edge in [:8] do
        r ← tick r (pins (edge%2 == 0) (edge%3 == 0) (edge%5 == 0) (seed+edge))
      r ← tick r {pins true false true seed with cold := true}
      total := total+r.edges
  return total

def main : IO Unit := do
  check (Reactive.outputs.foldl (fun n ⟨w,_⟩ => n+w) 0 == 155) "fixed status layout size"
  check (registers.size == 13 && registers.foldl (fun n ⟨w,_⟩ => n+w) 0 == 389)
    "declared storage layout"
  for (entry,k) in registers.toList.zipIdx do
    let ⟨_,r⟩ := entry
    check (registerIndex r == k) "register snapshot enumeration"
  let accepted ← acceptedFrames
  let invalid ← invalidFrames
  let retained ← retention
  let reset ← resetAndEdges
  let represented ← representedStates
  IO.println s!"Buffered SRAM serial: {accepted+invalid+retained+reset+represented} ordinary typed edges; all13 registers/all17 core ports against independent record model; eight opcodes, length/header/reserved rejection, one-shot delivery, saturated count, held SCK, POR, immutable snapshot, partial/overlong retry, exact consume and 224 independently seeded represented states passed."
