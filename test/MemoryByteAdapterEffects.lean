import Lean
import Pinwheel.Hardware.Memory.ByteAdapterEffects

open Lean Elab Command
open Pinwheel.Hardware Pinwheel.Hardware.Memory

namespace MemoryByteAdapterEffectsTests

open ByteAdapterModel ByteAdapterEffects

/-- Independent integer arithmetic: tags read=0, stored=1, misaligned=2,
reserved=3. No access/model function is used to interpret an event. -/
def response (request : ByteAdapterModel.Request a) (word : Nat) : Nat × Nat :=
  let size := request.size.toNat
  let offset := request.offset.toNat
  if size = 3 then (3, 0) else if offset % (2^size) ≠ 0 then (2, 0) else
  match request with
  | .store _ _ _ _ => (1, 0)
  | .read signed _ _ _ =>
    let span := 256^(2^size)
    let data := word / (256^offset) % span
    (0, if signed && data ≥ span/2 then data + 2^32 - span else data)

def responseView : ByteAdapterModel.Response → Nat × Nat
  | .read data => (0, data.toNat)
  | .stored => (1, 0)
  | .fault .misaligned => (2, 0)
  | .fault .reservedSize => (3, 0)

def patch (word data size offset : Nat) : Nat :=
  let low := 256^offset
  let span := 256^(2^size)
  word % low + (data % span)*low + (word/(low*span))*(low*span)

def applyEvent (words : Array Nat) (event : Event a) : Except String (Array Nat) := do
  let address := event.request.address.toNat
  let some word := words[address]? | throw "event address outside memory"
  let expected := response event.request word
  unless responseView event.response = expected do throw "wrong read value, acknowledgement, or fault"
  match event.request with
  | .read _ _ _ _ => return words
  | .store size _ offset data =>
    return if expected.1 = 1 then words.set! address (patch word data.toNat size.toNat offset.toNat) else words

def reconstruct (words : Array Nat) (events : List (Event a)) : Except String (Array Nat) :=
  events.foldlM applyEvent words

def words (s : ByteAdapterModel.State a) : Array Nat :=
  Array.ofFn (fun address : Fin (2^a) => (s.memory.contents (BitVec.ofFin address)).toNat)

def state (data : Array Nat) (q : Nat) (pending : Option (ByteAdapterModel.Request a)) :
    ByteAdapterModel.State a :=
  ⟨⟨fun address => BitVec.ofNat 32 data[address.toNat]!, BitVec.ofNat 32 q⟩, pending⟩

structure Fixture (a : Nat) where
  actual : ByteAdapterModel.State a
  reconstructed : Array Nat
  initialWords : Array Nat
  eventHistory : List (Event a) := []
  writeHistory : List (BitVec a × ByteAccess.Word) := []
  accepted : Nat := 0
  completed : Nat := 0
  canceled : Nat := 0
  faults : Nat := 0
  stores : Nat := 0
  edges : Nat := 0

def checkExtraction (i : Input a) (s : ByteAdapterModel.State a) (es : List (Event a)) : Except String Unit := do
  let observed := (ByteAdapterModel.component a).observe i s
  let expectedEvents := if i.reset || !i.ready then [] else
    match s.pending, observed.offered with
    | some request, some result => [⟨request, result⟩]
    | _, _ => []
  unless es = expectedEvents do throw "Event extraction lost a completion or changed its identity"

def check (i : Input a) (f : Fixture a) : IO (Fixture a) := do
  let es := events i f.actual
  let observed := (ByteAdapterModel.component a).observe i f.actual
  match checkExtraction i f.actual es with
  | .error message => throw (IO.userError message)
  | .ok _ => pure ()
  let rebuilt ← match reconstruct f.reconstructed es with
    | .ok data => pure data
    | .error message => throw (IO.userError s!"edge {f.edges}: {message}")
  let next := ByteAdapterModel.step i f.actual
  unless rebuilt = words next do throw (IO.userError s!"edge {f.edges}: event effects disagree with actual words")
  let writes := committedWrites i f.actual
  let folded := writes.foldl (fun data write => data.set! write.1.toNat write.2.toNat) f.reconstructed
  unless folded = rebuilt do throw (IO.userError "Actual full-word writes disagree with atomic byte effects")
  let accepted := f.accepted + if !i.reset && observed.ready && i.offered.isSome then 1 else 0
  let canceled := f.canceled + if i.reset && f.actual.pending.isSome then 1 else 0
  let completed := f.completed + es.length
  unless accepted = completed + canceled + (if next.pending.isSome then 1 else 0) do
    throw (IO.userError "Completion/fault/reset occurrence accounting mismatch")
  let faults := f.faults + (es.filter (fun e => (responseView e.response).1 ≥ 2)).length
  let stores := f.stores + (es.filter (fun e => e.response == .stored)).length
  return {f with
    actual := state (words next) next.memory.q.toNat next.pending
    reconstructed := rebuilt
    eventHistory := es.reverse ++ f.eventHistory
    writeHistory := writes.reverse ++ f.writeHistory
    accepted, completed, canceled, faults, stores, edges := f.edges+1}

def initial (a : Nat) : Fixture a :=
  let data := Array.ofFn (fun k : Fin (2^a) => (0x80ff7f01 + k.val*0x10204081) % 2^32)
  {actual := state data 0xfedcba98 none, reconstructed := data, initialWords := data}

def request (a kind size address offset data : Nat) : ByteAdapterModel.Request a :=
  if kind = 2 then .store (BitVec.ofNat 2 size) (BitVec.ofNat a address)
    (BitVec.ofNat 2 offset) (BitVec.ofNat 32 data)
  else .read (kind = 1) (BitVec.ofNat 2 size) (BitVec.ofNat a address) (BitVec.ofNat 2 offset)

def campaign (a : Nat) : IO Nat := do
  let mut f := initial a
  let hostile := request a 2 0 (2^a-1) 3 0xdeadbeef
  for size in [:4] do
    for offset in [:4] do
      for address in [:2^a] do
        for kind in [:3] do
          for abort in [false, true] do
            let r := request a kind size address offset (0xa580ff7f + 37*address)
            f ← check ⟨false, some r, true⟩ f
            f ← check ⟨false, some hostile, false⟩ f
            f ← check ⟨false, some hostile, false⟩ f
            f ← check ⟨abort, some hostile, true⟩ f
            f ← check ⟨true, some hostile, true⟩ f
            f ← check ⟨false, none, true⟩ f
  let mut seed : Nat := 0x65666665 + a
  for cycle in [:2000] do
    seed := (1664525*seed + 1013904223) % 2^32
    let r := request a (seed%3) ((seed/16)%4) ((seed/256)%(2^a)) ((seed/64)%4) seed
    f ← check ⟨cycle%97 = 0, if seed%7 = 0 then none else some r, seed%5 < 3⟩ f
  f ← check ⟨false, none, true⟩ f
  unless f.actual.pending.isNone && f.accepted = f.completed + f.canceled do
    throw (IO.userError "History failed final drain/accounting")
  let rebuilt ← match reconstruct f.initialWords f.eventHistory.reverse with
    | .ok data => pure data
    | .error message => throw (IO.userError message)
  let folded := f.writeHistory.reverse.foldl (fun data write => data.set! write.1.toNat write.2.toNat) f.initialWords
  unless rebuilt = f.reconstructed && folded = rebuilt do throw (IO.userError "Whole-history effects were reset or reordered")
  unless f.faults > 0 && f.stores > 0 && f.canceled > 0 do throw (IO.userError "Missing fault/store/reset coverage")
  IO.println s!"Byte effects a{a}: {f.edges} edges, {f.completed} events, {f.stores} stores, {f.faults} faults, {f.canceled} cancellations."
  return f.edges

def rejected (name : String) (result : Except String α) : IO Unit :=
  match result with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError s!"Mutation escaped: {name}")

def get (result : Except String α) : IO α :=
  match result with
  | .error message => throw (IO.userError message)
  | .ok value => pure value

def mutationControls : IO Nat := do
  let data := #[0x11223344, 0xaabbccdd]
  let initial : ByteAdapterModel.State 1 := state data 0xfedcba98 none
  let store : ByteAdapterModel.Request 1 := .store 0 0 1 0x78
  let pending := ByteAdapterModel.step ⟨false, some store, false⟩ initial
  let finish : Input 1 := ⟨false, none, true⟩
  let reset : Input 1 := ⟨true, some (.store 2 0 0 0), true⟩
  let finished := ByteAdapterModel.step finish pending
  let good := events finish pending
  let stored ← get (reconstruct data good)
  unless stored = words finished do throw (IO.userError "Mutation fixture store is not valid")
  -- The response is checked independently against the abstract current word.
  rejected "corrupt-read" (reconstruct (a := 1) data [⟨.read false 0 0 1, .read 0x32⟩])
  rejected "invent-fault" (reconstruct (a := 1) data [⟨.read false 0 0 1, .fault .misaligned⟩])
  let changed : List (Event 1) := [⟨.store 0 0 1 0x79, .stored⟩]
  rejected "change-completing-request" (checkExtraction finish pending changed)
  let changedWords ← get (reconstruct data changed)
  if changedWords = stored then throw (IO.userError "Mutated store operand was invisible")
  let dropped ← get (reconstruct data ([] : List (Event 1)))
  if dropped = stored then throw (IO.userError "Dropped store was invisible")
  let faultRequest : ByteAdapterModel.Request 1 := .store 1 0 3 0x1234
  let faultPending := ByteAdapterModel.step ⟨false, some faultRequest, false⟩ initial
  rejected "drop-fault" (checkExtraction finish faultPending [])
  let resetWords ← get (reconstruct data (events reset pending))
  unless resetWords = data do throw (IO.userError "Reset fixture changed memory")
  if resetWords = stored then throw (IO.userError "Reset committing pending store was invisible")
  if resetWords = data.set! 0 0 then throw (IO.userError "Reset clearing a word was invisible")
  let afterReset ← get (reconstruct data (good ++ events reset finished))
  unless afterReset = stored do throw (IO.userError "Prior store disappeared from effect history")
  if afterReset = data then throw (IO.userError "Reset rollback of committed history was invisible")
  return 9

end MemoryByteAdapterEffectsTests

elab "#audit_byte_effects" : command => do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    if name.toString.startsWith "Pinwheel.Hardware.Memory.ByteAdapterEffects." ||
        name.toString.startsWith "_private.Pinwheel.Hardware.Memory.ByteAdapterEffects." ||
        name.toString.startsWith "MemoryByteAdapterEffectsTests." ||
        name.toString.startsWith "_private.test.MemoryByteAdapterEffects." then
      count := count+1
      let axioms ← collectAxioms name
      let bad := axioms.filter fun a => a != ``propext && a != ``Classical.choice && a != ``Quot.sound
      unless bad.isEmpty do throwError "Unapproved byte effect axioms in {name}: {bad}"
  if count < 25 then throwError "Incomplete byte effect audit"
  logInfo m!"Byte effect audit: {count} declarations, standard axioms only."

#audit_byte_effects

def main : IO Unit := do
  let mut edges := 0
  for a in [0, 1, 3] do edges := edges + (← MemoryByteAdapterEffectsTests.campaign a)
  let mutations ← MemoryByteAdapterEffectsTests.mutationControls
  IO.println s!"Byte effects: {edges} independent event/array reconstruction edges; {mutations} semantic mutation probes rejected."
