import Lean
import Pinwheel.Hardware.Memory.ByteAdapterRefinement

open Lean Elab Command Pinwheel.Hardware Pinwheel.Hardware.Memory
namespace MemoryByteAdapterRefinementTests

/-- A downstream artifact theorem retains the exact physical event extractor
and every final RAM address, with no fixed power-up image or inactive metadata.
The separately checked correspondence premise is deliberately explicit. -/
theorem imported_memory_reconstruction
    (rtl : Timed.Component (Values (ByteAdapterInterface.Input a))
      (Values (ByteAdapterCircuit.Register a)) (Values ByteAdapterInterface.Output))
    (proof : Artifact.Correspondence (ByteAdapterCircuit.circuit a) rtl)
    (raw : Values (ByteAdapterCircuit.Register a)) (reset : Values (ByteAdapterInterface.Input a))
    (hr : reset ByteAdapterInterface.reset = 1) (traffic : List (Values (ByteAdapterInterface.Input a))) :
    ByteAdapterEffects.replay (ByteAdapterCircuit.view raw).memory.contents
      (rtl.eventTrace (ByteAdapterRefinement.artifactEvents rtl) (rtl.step reset raw) traffic) =
      some (ByteAdapterCircuit.view (rtl.run (rtl.step reset raw) traffic)).memory.contents :=
  ByteAdapterRefinement.artifact_replay_after_reset proof reset raw hr traffic

theorem arbitrary_empty_image (image : Sram.State a 32)
    (garbage : Values (ByteAdapterCircuit.Metadata a)) :
    ByteAdapterModel.Valid (ByteAdapterCircuit.view (ByteAdapterRefinement.emptyRaw image garbage)) ∧
      (ByteAdapterCircuit.view (ByteAdapterRefinement.emptyRaw image garbage)).memory = image := by
  rw [ByteAdapterRefinement.view_emptyRaw]
  simp [ByteAdapterModel.Valid]

def values (d : Interface P) (bank : Array Nat) : Values P :=
  fun {w} p => BitVec.ofNat w bank[(d.position p).val]!

def snapshot (d : Interface P) (raw : Values P) : Array Nat :=
  d.ports.map fun ⟨_, p⟩ => (raw p).toNat

structure Issued where
  write : Bool
  signed : Bool
  size : Nat
  address : Nat
  offset : Nat
  data : Nat
  deriving DecidableEq, Repr

def issued (pins : Array Nat) : Issued :=
  ⟨pins[2]! = 1, pins[3]! = 1, pins[4]!, pins[5]!, pins[6]!, pins[7]!⟩

def requestView : ByteAdapterModel.Request a → Array Nat
  | .read signed size address offset => #[0, if signed then 1 else 0, size.toNat, address.toNat, offset.toNat, 0]
  | .store size address offset data => #[1, 0, size.toNat, address.toNat, offset.toNat, data.toNat]

def issuedView (r : Issued) : Array Nat :=
  #[if r.write then 1 else 0, if !r.write && r.signed then 1 else 0,
    r.size, r.address, r.offset, if r.write then r.data else 0]

def responseView : ByteAdapterModel.Response → Nat × Nat
  | .read data => (0, data.toNat)
  | .stored => (1, 0)
  | .fault .reservedSize => (2, 0)
  | .fault .misaligned => (3, 0)

def eventView (event : ByteAdapterEffects.Event a) : Array Nat × (Nat × Nat) :=
  (requestView event.request, responseView event.response)

/-- Independent integer byte arithmetic; no ByteAccess/model operation is used. -/
def result (r : Issued) (word : Nat) : Nat × Nat :=
  if r.size = 3 then (2, 0) else if r.offset % (2^r.size) ≠ 0 then (3, 0)
  else if r.write then (1, 0) else
    let span := 256^(2^r.size)
    let selected := word/(256^r.offset)%span
    (0, if r.signed && selected ≥ span/2 then selected+2^32-span else selected)

def patch (r : Issued) (word : Nat) : Nat :=
  let low := 256^r.offset
  let span := 256^(2^r.size)
  word%low + (r.data%span)*low + (word/(low*span))*(low*span)

def contents (words : Array Nat) : Contents a 32 := fun addr => BitVec.ofNat 32 words[addr.toNat]!
def words (memory : Contents a 32) : Array Nat := Array.ofFn fun k : Fin (2^a) => (memory (BitVec.ofFin k)).toNat

structure Ledger (a : Nat) where
  bank : Array Nat
  memory : Array Nat
  origin : Array Nat
  pending : Option Issued := none
  history : List (ByteAdapterEffects.Event a) := []
  accepted : Nat := 0
  completed : Nat := 0
  canceled : Nat := 0
  stores : Nat := 0
  faults : Nat := 0
  edges : Nat := 0

def check (pins : Array Nat) (f : Ledger a) : IO (Ledger a) := do
  let i : Values (ByteAdapterInterface.Input a) := values (ByteAdapterInterface.inputs a) pins
  let raw : Values (ByteAdapterCircuit.Register a) := values (ByteAdapterCircuit.registers a) f.bank
  let es := ByteAdapterRefinement.events i raw
  let completion := if pins[0]! = 0 && pins[8]! = 1 then f.pending else none
  let expected := completion.toList.map fun r => (issuedView r, result r f.memory[r.address]!)
  unless es.map eventView = expected do
    throw (IO.userError s!"Actual response/request event mismatch at edge {f.edges}")
  let mut rebuilt := f.memory
  for r in completion.toList do
    if (result r f.memory[r.address]!).1 = 1 then rebuilt := rebuilt.set! r.address (patch r f.memory[r.address]!)
  -- Check the library interpreter against an independently updated integer array.
  match ByteAdapterEffects.replay (a := a) (contents f.memory) es with
  | none => throw (IO.userError "Accepted physical event failed the atomic interpreter")
  | some after => unless words after = rebuilt do throw (IO.userError "Atomic replay disagrees with integer effects")
  let bank := snapshot (ByteAdapterCircuit.registers a) ((ByteAdapterCircuit.circuit a).step i raw)
  unless bank.extract 0 (2^a) = rebuilt do throw (IO.userError "Event replay did not reconstruct every physical word")
  let acceptedNow := pins[0]! = 0 && f.pending.isNone && pins[1]! = 1
  let canceledNow := pins[0]! = 1 && f.pending.isSome
  let pending := if pins[0]! = 1 then none else match f.pending with
    | some r => if pins[8]! = 1 then none else some r
    | none => if acceptedNow then some (issued pins) else none
  let accepted := f.accepted + if acceptedNow then 1 else 0
  let canceled := f.canceled + if canceledNow then 1 else 0
  let completed := f.completed + es.length
  unless accepted = completed+canceled+(if pending.isSome then 1 else 0) do
    throw (IO.userError "Completion occurrence accounting lost a repeated request or reset cancellation")
  return {f with
    bank, memory := rebuilt, pending, history := es.reverse ++ f.history,
    accepted, canceled, completed, stores := f.stores+(es.filter fun e => e.response == .stored).length,
    faults := f.faults+(es.filter fun e => (responseView e.response).1 ≥ 2).length, edges := f.edges+1}

def initial (a : Nat) : Ledger a :=
  let memory := Array.ofFn fun k : Fin (2^a) => (0x80ff7f01+k.val*0x10204081)%2^32
  {memory, origin := memory, bank := memory ++ #[0xfedcba98, 1, 1, 3, 2^a-1, 3, 0xdeadbeef, 0]}

def campaign (a : Nat) : IO Nat := do
  let mut f := initial a
  for size in [:4] do
    for offset in [:4] do
      for address in [:2^a] do
        for kind in [:3] do
          for abort in [false, true] do
            let command := #[0, 1, if kind = 2 then 1 else 0, if kind = 1 then 1 else 0,
              size, address, offset, 0x80ff7fa5, 1]
            f ← check command f
            f ← check #[0, 1, 1, 1, 2, 2^a-1, 0, 0xdeadbeef, 0] f
            f ← check #[0, 0, 0, 1, 3, 0, 3, 0, 0] f
            f ← check #[if abort then 1 else 0, 1, 1, 0, 2, 0, 0, 0, 1] f
            f ← check #[1, 1, 1, 1, 2, 0, 0, 0, 1] f
  let mut seed : Nat := 0x65766e74+a
  for cycle in [:1200] do
    seed := (1664525*seed+1013904223)%2^32
    f ← check #[if cycle%101 = 0 then 1 else 0, if seed%7 < 5 then 1 else 0,
      seed%2, seed/2%2, seed/4%4, seed/16%(2^a), seed/64%4, seed, if seed%5 < 3 then 1 else 0] f
  f ← check #[0, 0, 0, 0, 0, 0, 0, 0, 1] f
  unless f.pending.isNone && f.accepted = f.completed+f.canceled do throw (IO.userError "History did not drain")
  match ByteAdapterEffects.replay (a := a) (contents f.origin) f.history.reverse with
  | none => throw (IO.userError "Whole physical event history failed atomic replay")
  | some after => unless words after = f.memory do throw (IO.userError "History replay lost ordering or reset persistence")
  unless f.stores > 0 && f.faults > 0 && f.canceled > 0 do throw (IO.userError "Missing effect coverage")
  IO.println s!"Byte physical events a{a}: {f.edges} edges, {f.completed} events, {f.stores} stores, {f.faults} faults, {f.canceled} cancellations."
  return f.edges

def alter (observation : Values ByteAdapterInterface.Output) (index value : Nat) :
    Values ByteAdapterInterface.Output := fun {w} p =>
  if (ByteAdapterInterface.outputs.position p).val = index then BitVec.ofNat w value else observation p

def dirtyReset (a : Nat) : IO Nat := do
  let d := 2^a
  for flags in [:128] do
    let memory := (initial a).memory
    -- This Q is deliberately unrelated to the pending word; only the reset
    -- boundary admits subsequent atomic events from this fabricated state.
    let bank := memory ++ #[0xfedcba98, flags/2%2, flags/4%2, flags/8%4,
      flags%d, flags/32%4, 0xa580ff7f, flags%2]
    let raw : Values (ByteAdapterCircuit.Register a) := values (ByteAdapterCircuit.registers a) bank
    let reset : Values (ByteAdapterInterface.Input a) := values (ByteAdapterInterface.inputs a)
      #[1, 1, 1, 1, 2, 0, 0, 0, 1]
    unless (ByteAdapterRefinement.events reset raw).isEmpty do
      throw (IO.userError "Dirty reset emitted an architectural completion")
    let after := snapshot (ByteAdapterCircuit.registers a) ((ByteAdapterCircuit.circuit a).step reset raw)
    unless after = bank.set! (d+7) 0 do throw (IO.userError "Dirty reset changed retained storage")
    let recovered : Ledger a := {bank := after, memory, origin := memory}
    let offered ← check #[0, 1, 0, 1, 0, flags%d, flags%4, 0xdeadbeef, 1] recovered
    let completed ← check #[0, 0, 1, 0, 3, 0, 3, 0, 1] offered
    unless completed.completed = 1 && completed.memory = memory do
      throw (IO.userError "Reset did not recover a real atomic read")
  return 384

/-- This deliberately wrong component has no correspondence certificate. Its
events must expose its actual corrupted outputs, rather than model responses. -/
def corruptedReadback : Timed.Component (Values (ByteAdapterInterface.Input 1))
    (Values (ByteAdapterCircuit.Register 1)) (Values ByteAdapterInterface.Output) :=
  {(ByteAdapterCircuit.circuit 1).component with
    observe := fun i r => alter ((ByteAdapterCircuit.circuit 1).observe i r) 3 0x81}

def mutationControls : IO Nat := do
  let ri := ByteAdapterCircuit.registers 1
  let ii := ByteAdapterInterface.inputs 1
  let raw0 : Values (ByteAdapterCircuit.Register 1) := values ri (initial 1).bank
  let load : Values (ByteAdapterInterface.Input 1) := values ii #[0, 1, 0, 0, 0, 0, 3, 0xdeadbeef, 1]
  let finish : Values (ByteAdapterInterface.Input 1) := values ii #[0, 1, 1, 1, 3, 1, 2, 0xdeadbeef, 1]
  let raw : Values (ByteAdapterCircuit.Register 1) := (ByteAdapterCircuit.circuit 1).step load raw0
  let actual : Values ByteAdapterInterface.Output := (ByteAdapterCircuit.circuit 1).observe finish raw
  let good := ByteAdapterRefinement.events finish raw
  unless good.map eventView = [(#[0, 0, 0, 0, 3, 0], (0, 0x80))] do
    throw (IO.userError "Active-read mutation fixture is not the intended completion")
  let badData := ByteAdapterRefinement.artifactEvents corruptedReadback finish raw
  unless badData.map eventView = [(#[0, 0, 0, 0, 3, 0], (0, 0x81))] do
    throw (IO.userError "Imported extractor repaired corrupt actual response data")
  unless (ByteAdapterEffects.replay (a := 1) (contents (initial 1).memory) badData).isNone do
    throw (IO.userError "Wrong imported read data escaped atomic replay")
  let badCode := ByteAdapterRefinement.extract finish raw (alter actual 2 1)
  unless (ByteAdapterEffects.replay (a := 1) (contents (initial 1).memory) badCode).isNone do
    throw (IO.userError "Store acknowledgement for a read escaped atomic replay")
  let rawBank := snapshot ri raw
  let wrongAddress : Values (ByteAdapterCircuit.Register 1) := values ri (rawBank.set! 6 1)
  let badIdentity := ByteAdapterRefinement.extract finish wrongAddress actual
  unless badIdentity ≠ good && (ByteAdapterEffects.replay (a := 1) (contents (initial 1).memory) badIdentity).isNone do
    throw (IO.userError "Changed actual retained request address escaped identity/read validation")
  let missing := ByteAdapterRefinement.extract finish raw (alter actual 1 0)
  unless missing.isEmpty && missing ≠ good do throw (IO.userError "Dropped valid was hidden by event extraction")
  let reset : Values (ByteAdapterInterface.Input 1) := values ii #[1, 1, 1, 0, 2, 0, 0, 0, 1]
  let resetGood := ByteAdapterRefinement.events reset raw
  let spurious := ByteAdapterRefinement.extract reset raw actual
  unless resetGood.isEmpty && spurious = good && spurious ≠ resetGood do
    throw (IO.userError "Extractor hid a spurious actual response during reset")
  let stalled : Values (ByteAdapterInterface.Input 1) := values ii #[0, 1, 1, 0, 2, 0, 0, 0, 0]
  unless (ByteAdapterRefinement.extract stalled raw actual).isEmpty do
    throw (IO.userError "Unaccepted response produced an event")
  let store : Values (ByteAdapterInterface.Input 1) := values ii #[0, 1, 1, 1, 0, 0, 1, 0x78, 0]
  let stored : Values (ByteAdapterCircuit.Register 1) := (ByteAdapterCircuit.circuit 1).step store raw0
  let storeEvents := ByteAdapterRefinement.events finish stored
  let changed : Values (ByteAdapterCircuit.Register 1) := values ri ((snapshot ri stored).set! 8 0x79)
  let changedEvents := ByteAdapterRefinement.events finish changed
  let some expected := ByteAdapterEffects.replay (a := 1) (contents (initial 1).memory) storeEvents
    | throw (IO.userError "Store fixture unexpectedly failed")
  let some mutated := ByteAdapterEffects.replay (a := 1) (contents (initial 1).memory) changedEvents
    | throw (IO.userError "Changed operand fixture unexpectedly faulted")
  unless storeEvents ≠ changedEvents && words expected ≠ words mutated do
    throw (IO.userError "Retained store operand corruption escaped effect reconstruction")
  unless (good ++ good).map eventView ≠ good.map eventView do
    throw (IO.userError "Duplicated completion escaped occurrence accounting")
  return 7

end MemoryByteAdapterRefinementTests

elab "#audit_byte_refinement" : command => do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    if name.toString.startsWith "Pinwheel.Hardware.Memory.ByteAdapterRefinement." ||
        name.toString.startsWith "MemoryByteAdapterRefinementTests." then
      count := count+1
      let axioms ← collectAxioms name
      let bad := axioms.filter fun a => a != ``propext && a != ``Classical.choice && a != ``Quot.sound
      unless bad.isEmpty do throwError "Unapproved physical event axioms in {name}: {bad}"
  if count < 40 then throwError "Incomplete physical event audit"
  logInfo m!"Byte physical event audit: {count} declarations, standard axioms only."

#audit_byte_refinement

def main : IO Unit := do
  let mut edges := 0
  for a in [0, 1, 2, 3] do edges := edges+(← MemoryByteAdapterRefinementTests.campaign a)
  let mut resetEdges := 0
  for a in [0, 1, 2, 3] do resetEdges := resetEdges+(← MemoryByteAdapterRefinementTests.dirtyReset a)
  let mutations ← MemoryByteAdapterRefinementTests.mutationControls
  IO.println s!"Byte physical effects: {edges} independent event/array/occurrence-ledger edges plus {resetEdges} dirty-reset/recovery edges; {mutations} semantic mutation controls rejected."
