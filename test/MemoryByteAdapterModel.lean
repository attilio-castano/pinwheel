import Lean
import Pinwheel.Hardware.Memory.ByteAdapterModel

open Lean Elab Command
open Pinwheel.Hardware.Memory
namespace MemoryByteAdapterModelTests

structure Request where
  write : Bool
  signed : Bool
  size : Nat
  address : Nat
  offset : Nat
  data : Nat
  deriving DecidableEq, Repr

structure Input where
  reset : Bool := false
  offered : Option Request := none
  ready : Bool := false

structure State where
  words : Array Nat
  q : Nat
  pending : Option Request
  deriving DecidableEq, Repr

/-- Independent natural-number access rules. Response tags: read=0, store=1,
misaligned=2, reserved=3. Neither reference transition nor access arithmetic
calls ByteAccess, SinglePort, or ByteAdapterModel. -/
def fault (r : Request) : Nat :=
  if r.size = 3 then 3 else if r.offset % (2^r.size) ≠ 0 then 2 else 0

def response (r : Request) (q : Nat) : Nat × Nat :=
  if fault r ≠ 0 then (fault r, 0)
  else if r.write then (1, 0)
  else
    let span := 256^(2^r.size)
    let value := q / (256^r.offset) % span
    (0, if r.signed && value ≥ span/2 then value + 2^32 - span else value)

def patched (r : Request) (q : Nat) : Nat :=
  let low := 256^r.offset
  let span := 256^(2^r.size)
  q % low + (r.data % span)*low + (q/(low*span))*(low*span)

def observe (i : Input) (s : State) : Bool × Option (Nat × Nat) :=
  if i.reset then (false, none) else (s.pending.isNone, s.pending.map (fun r => response r s.q))

def advance (i : Input) (s : State) : State :=
  if i.reset then {s with pending := none} else
  match s.pending with
  | some r =>
    if !i.ready then s else
    {s with
      pending := none
      words := if r.write && fault r = 0 then s.words.set! r.address (patched r s.q) else s.words}
  | none => match i.offered with
    | none => s
    | some r => {s with pending := some r, q := if fault r = 0 then s.words[r.address]! else s.q}

def ramCommand (i : Input) (s : State) : Nat × Nat × Nat :=
  if i.reset then (0, 0, 0) else match s.pending with
  | some r => if i.ready && r.write && fault r = 0 then (2, r.address, patched r s.q) else (0, 0, 0)
  | none => match i.offered with
    | some r => if fault r = 0 then (1, r.address, 0) else (0, 0, 0)
    | none => (0, 0, 0)

def Request.model (a : Nat) (r : Request) : ByteAdapterModel.Request a :=
  if r.write then .store (BitVec.ofNat 2 r.size) (BitVec.ofNat a r.address)
    (BitVec.ofNat 2 r.offset) (BitVec.ofNat 32 r.data)
  else .read r.signed (BitVec.ofNat 2 r.size) (BitVec.ofNat a r.address) (BitVec.ofNat 2 r.offset)

def modelRequest : ByteAdapterModel.Request a → Request
  | .read signed size address offset => ⟨false, signed, size.toNat, address.toNat, offset.toNat, 0⟩
  | .store size address offset data => ⟨true, false, size.toNat, address.toNat, offset.toNat, data.toNat⟩

def canonical (r : Request) : Request :=
  {r with signed := if r.write then false else r.signed, data := if r.write then r.data else 0}

def Input.model (a : Nat) (i : Input) : ByteAdapterModel.Input a :=
  ⟨i.reset, i.offered.map (Request.model a), i.ready⟩

def State.model (a : Nat) (s : State) : ByteAdapterModel.State a :=
  ⟨⟨fun address => BitVec.ofNat 32 s.words[address.toNat]!, BitVec.ofNat 32 s.q⟩,
    s.pending.map (Request.model a)⟩

def stateView (s : ByteAdapterModel.State a) : State :=
  ⟨Array.ofFn (fun k : Fin (2^a) => (s.memory.contents (BitVec.ofFin k)).toNat),
    s.memory.q.toNat, s.pending.map modelRequest⟩

def responseView : ByteAdapterModel.Response → Nat × Nat
  | .read value => (0, value.toNat)
  | .stored => (1, 0)
  | .fault .misaligned => (2, 0)
  | .fault .reservedSize => (3, 0)

def outputView (o : ByteAdapterModel.Output) : Bool × Option (Nat × Nat) := (o.ready, o.offered.map responseView)

def commandView : SinglePort.Command a 32 → Nat × Nat × Nat
  | .idle => (0, 0, 0)
  | .read address => (1, address.toNat, 0)
  | .write address data => (2, address.toNat, data.toNat)

structure Fixture (a : Nat) where
  model : ByteAdapterModel.State a
  reference : State
  /-- Acceptance ordinal plus fixed acceptance-time response snapshot. -/
  token : Option (Nat × (Nat × Nat)) := none
  accepted : Nat := 0
  completed : Nat := 0
  canceled : Nat := 0
  stores : Nat := 0
  cycles : Nat := 0

def check (i : Input) (f : Fixture a) : IO (Fixture a) := do
  let i := {i with offered := i.offered.map canonical}
  let modelInput := i.model a
  let pre := outputView ((ByteAdapterModel.component a).observe modelInput f.model)
  let expectedPre := observe i f.reference
  unless pre = expectedPre do throw (IO.userError s!"Pre-output mismatch at {f.cycles}")
  let cmd := commandView (ByteAdapterModel.command modelInput f.model)
  unless cmd = ramCommand i f.reference do throw (IO.userError s!"RAM command mismatch at {f.cycles}")
  let next := ByteAdapterModel.step modelInput f.model
  let expected := advance i f.reference
  unless stateView next = expected do
    throw (IO.userError s!"State mismatch at {f.cycles}: actual {repr (stateView next)}, expected {repr expected}")
  unless outputView ((ByteAdapterModel.component a).observe modelInput next) = observe i expected do
    throw (IO.userError s!"Post-output mismatch at {f.cycles}")
  let mut token := f.token
  let mut accepted := f.accepted
  let mut completed := f.completed
  let mut canceled := f.canceled
  let mut stores := f.stores
  if i.reset then
    canceled := canceled + if token.isSome then 1 else 0
    token := none
  else
    if i.ready then
      if let some delivered := pre.2 then
        let some (_, snapshot) := token | throw (IO.userError "Response without accepted occurrence")
        unless delivered = snapshot do throw (IO.userError "Accepted snapshot changed while pending")
        unless (delivered.1 = 1) = (cmd.1 = 2) do throw (IO.userError "Store acknowledgement/write edge differs")
        completed := completed + 1
        stores := stores + if delivered.1 = 1 then 1 else 0
        token := none
    if pre.1 then
      if let some request := i.offered then
        unless token.isNone do throw (IO.userError "Overlapping acceptance occurrences")
        token := some (accepted, response request f.reference.words[request.address]!)
        accepted := accepted + 1
  unless token.isSome = expected.pending.isSome do throw (IO.userError "Pending occurrence lost/duplicated")
  unless accepted = completed + canceled + (if token.isSome then 1 else 0) do
    throw (IO.userError "Occurrence conservation failed")
  -- Rebuild the model's contents from its own snapshot, avoiding a long chain
  -- of closure updates while keeping the independent reference separate.
  return ⟨(stateView next).model a, expected, token, accepted, completed, canceled, stores, f.cycles+1⟩

def initial (a : Nat) : Fixture a :=
  let s : State := ⟨Array.ofFn (fun k : Fin (2^a) =>
    (0x80ff7f01 + k.val*0x10204081) % 2^32), 0xfedcba98, none⟩
  {model := s.model a, reference := s}

def attack (a : Nat) : Request := ⟨true, false, 0, 2^a-1, 3, 0xdeadbeef⟩

def campaign (a : Nat) : IO Nat := do
  let mut f := initial a
  for raw in [:4] do
    for offset in [:4] do
      for address in [:2^a] do
        for kind in [:3] do
          let request : Request := ⟨kind = 2, kind = 1, raw, address, offset,
            (0xa580ff7f + 37*address) % 2^32⟩
          for abort in [false, true] do
            f ← check ⟨false, some request, false⟩ f
            for _ in [:3] do f ← check ⟨false, some (attack a), false⟩ f
            -- Offered hostile work cannot replace the completing request.
            f ← check ⟨abort, some (attack a), true⟩ f
            f ← check ⟨true, some (attack a), true⟩ f
            f ← check ⟨false, none, true⟩ f
  let mut seed : Nat := 0x62797465 + a
  for cycle in [:6000] do
    seed := (1664525*seed + 1013904223) % 2^32
    let data := seed
    seed := (1664525*seed + 1013904223) % 2^32
    let r : Request := ⟨seed % 3 = 0, seed % 5 = 0, (seed/16)%4, (seed/256)%(2^a), (seed/64)%4, data⟩
    f ← check ⟨cycle % 131 = 0, if seed % 7 = 0 then none else some r, seed % 5 < 3⟩ f
  f ← check ⟨false, none, true⟩ f
  f ← check ⟨false, none, true⟩ f
  unless f.token.isNone && f.reference.pending.isNone do throw (IO.userError "Final drain failed")
  unless f.accepted = f.completed + f.canceled do throw (IO.userError "Final global accounting failed")
  unless f.stores > 0 && f.canceled > 0 do throw (IO.userError "Store/abort coverage missing")
  IO.println s!"Byte adapter a{a}: {f.cycles} edges, {f.accepted} accepted / {f.completed} completed / {f.canceled} canceled, {f.stores} stores."
  return f.cycles

def mutationControls : IO Nat := do
  let f := initial 1
  let request : Request := ⟨true, false, 0, 0, 2, 0x12345678⟩
  let accept : Input := ⟨false, some request, false⟩
  let pending := ByteAdapterModel.step (accept.model 1) f.model
  let held : Input := ⟨false, some (attack 1), false⟩
  let finish : Input := ⟨false, some (attack 1), true⟩
  let reset : Input := ⟨true, some (attack 1), true⟩
  let faultRequest : Request := {request with size := 1, offset := 3}
  let faultInput : Input := ⟨false, some faultRequest, false⟩
  let referencePending := advance accept f.reference
  let finished := ByteAdapterModel.step (finish.model 1) pending
  let early := {pending with memory := (ByteAdapterModel.step (finish.model 1) pending).memory}
  let faultRead := {ByteAdapterModel.step (faultInput.model 1) f.model with memory := pending.memory}
  let replacement := {finished with pending := some ((attack 1).model 1)}
  let lost := {pending with pending := none}
  let duplicate := {finished with pending := pending.pending}
  let liveOperand := {pending with pending := some (({request with data := (attack 1).data}).model 1)}
  let probes : List (String × ByteAdapterModel.State 1 × State) :=
    [("store-on-request", early, referencePending),
     ("commit-while-stalled", finished, advance held referencePending),
     ("fault-reads-Q", faultRead, advance faultInput f.reference),
     ("reset-commits-store", finished, advance reset referencePending),
     ("same-edge-replacement", replacement, advance finish referencePending),
     ("drop-stalled-response", lost, advance held referencePending),
     ("duplicate-store", duplicate, advance finish referencePending),
     ("live-store-operand", ByteAdapterModel.step (finish.model 1) liveOperand, advance finish referencePending)]
  for (name, actual, expected) in probes do
    if stateView actual = expected then throw (IO.userError s!"Semantic mutation escaped: {name}")
  return probes.length

end MemoryByteAdapterModelTests

elab "#audit_byte_adapter" : command => do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    if name.toString.startsWith "Pinwheel.Hardware.Memory.ByteAdapterModel." ||
        name.toString.startsWith "MemoryByteAdapterModelTests." then
      count := count + 1
      let axioms ← collectAxioms name
      let bad := axioms.filter fun a => a != ``propext && a != ``Classical.choice && a != ``Quot.sound
      unless bad.isEmpty do throwError "Unapproved byte adapter axioms in {name}: {bad}"
  if count < 40 then throwError "Incomplete byte adapter audit"
  logInfo m!"Byte adapter audit: {count} declarations, standard axioms only."

#audit_byte_adapter

def main : IO Unit := do
  let mut edges := 0
  for a in [0, 1, 3] do edges := edges + (← MemoryByteAdapterModelTests.campaign a)
  let mutations ← MemoryByteAdapterModelTests.mutationControls
  IO.println s!"Byte adapter: {edges} independent arithmetic/array/occurrence-ledger edges; {mutations} semantic mutations rejected."
