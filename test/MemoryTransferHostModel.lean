import Lean
import Pinwheel.Hardware.Memory.TransferHostModel

open Lean Elab Command
open Pinwheel.Hardware
open Pinwheel.Hardware.Memory
open Pinwheel.Hardware.Memory.TransferHostModel

namespace MemoryTransferHostModelTests

structure Oracle where
  phase : Nat
  sourceBase : Nat
  destinationBase : Nat
  length : Nat
  index : Nat
  done : Bool
  error : Bool
  source : Array Nat
  destination : Array Nat
  sourceQ : Nat
  destinationQ : Nat
  sourcePending : Bool
  destinationPending : Bool
  deriving BEq, Repr

def words (a : Nat) (memory : Contents a w) : Array Nat :=
  (Array.range (2^a)).map (fun k => (memory (BitVec.ofNat a k)).toNat)

def contents (a w : Nat) (array : Array Nat) : Contents a w :=
  fun address => BitVec.ofNat w (array[address.toNat]?.getD 0)

def capture (a : Nat) (s : TransferModel.State a wi wo) : Oracle :=
  ⟨match s.control.phase with | .idle => 0 | .issueRead => 1 | .transfer => 2,
    s.control.config.sourceBase.toNat, s.control.config.destinationBase.toNat,
    s.control.config.length, s.control.index, s.control.done, s.control.error,
    words a s.source.memory.contents, words a s.destination.memory.contents,
    s.source.memory.q.toNat, s.destination.memory.q.toNat, s.source.pending, s.destination.pending⟩

def materialize (a wi wo : Nat) (s : TransferModel.State a wi wo) : TransferModel.State a wi wo :=
  let c := capture a s
  { s with
    source := ⟨⟨contents a wi c.source, BitVec.ofNat wi c.sourceQ⟩, c.sourcePending⟩
    destination := ⟨⟨contents a wo c.destination, BitVec.ofNat wo c.destinationQ⟩, c.destinationPending⟩ }

def initial (a wi wo : Nat) (source destination : Array Nat) : TransferModel.State a wi wo :=
  TransferModel.initialState ⟨contents a wi source, BitVec.ofNat wi 123⟩
    ⟨contents a wo destination, BitVec.ofNat wo 199⟩

def clearControl (s : Oracle) : Oracle :=
  { s with
    phase := 0, sourceBase := 0, destinationBase := 0, length := 0,
    index := 0, done := false, error := false }

/-- Independent integer/array adapter; this calls no stream-memory transition
or controller function. The only shared types are the input request tags. -/
def hostMemory (request : Option (StreamModel.Request a w)) (ready pending : Bool)
    (array : Array Nat) (q : Nat) : Array Nat × Nat × Bool :=
  if pending && !ready then (array, q, pending)
  else match request with
    | none => (array, q, false)
    | some (.read address) => (array, array[address.toNat]?.getD 0, true)
    | some (.write address value) => (array.set! address.toNat value.toNat, q, false)

/-- This oracle performs range arithmetic on integers and state updates on
arrays; it does not invoke the model's decoder, wrapper, or transfer logic. -/
def oracleStep (a wo : Nat) (f : Nat → Nat) (i : Input a wi wo) (s : Oracle) : Oracle :=
  if i.reset then { clearControl s with sourcePending := false, destinationPending := false }
  else
    let clear := { s with done := false, error := false }
    if s.phase == 0 then
      if i.start.isSome && !s.sourcePending && !s.destinationPending then
        match i.start with
        | none => clear
        | some c =>
          let length := c.length.toNat
          if length ≤ 2^a-c.sourceBase.toNat && length ≤ 2^a-c.destinationBase.toNat then
            { clear with
              sourceBase := c.sourceBase.toNat, destinationBase := c.destinationBase.toNat,
              length := length, index := 0, phase := if length == 0 then 0 else 1,
              done := length == 0 }
          else { clearControl clear with error := true }
      else
        let source := hostMemory (if i.start.isSome then none else i.sourceRequest)
          i.sourceResponseReady s.sourcePending s.source s.sourceQ
        let destination := hostMemory (if i.start.isSome then none else i.destinationRequest)
          i.destinationResponseReady s.destinationPending s.destination s.destinationQ
        { clear with
          source := source.1, sourceQ := source.2.1, sourcePending := source.2.2,
          destination := destination.1, destinationQ := destination.2.1, destinationPending := destination.2.2 }
    else if s.phase == 1 then
      if s.sourcePending then { clear with destinationPending := false }
      else { clear with
        phase := 2, sourcePending := true, destinationPending := false,
        sourceQ := s.source[(s.sourceBase+s.index) % 2^a]?.getD 0 }
    else
      if !s.sourcePending then { clear with destinationPending := false }
      else { clear with
        sourcePending := false, destinationPending := false, index := s.index+1,
        phase := if s.index+1 < s.length then 1 else 0, done := s.index+1 ≥ s.length,
        destination := s.destination.set! ((s.destinationBase+s.index) % 2^a) (f s.sourceQ % 2^wo) }

def expectedOutput (i : Input a wi wo) (s : Oracle) : Output wi wo :=
  if i.reset then ⟨false, false, false, false, ⟨false, none⟩, ⟨false, none⟩⟩
  else
    ⟨s.phase == 0 && !s.sourcePending && !s.destinationPending, s.phase != 0, s.done, s.error,
      ⟨s.phase == 0 && !i.start.isSome && (!s.sourcePending || i.sourceResponseReady),
        if s.phase == 0 && s.sourcePending then some (BitVec.ofNat wi s.sourceQ) else none⟩,
      ⟨s.phase == 0 && !i.start.isSome && (!s.destinationPending || i.destinationResponseReady),
        if s.phase == 0 && s.destinationPending then some (BitVec.ofNat wo s.destinationQ) else none⟩⟩

structure Result where
  finalState : Oracle
  edges : Nat
  starts : Nat
  sourceRequests : Nat
  destinationRequests : Nat
  sourceResponses : Array Nat
  destinationResponses : Array Nat

def runFrom (a wi wo : Nat) (m : Stream.Map wi wo) (f : Nat → Nat)
    (initialState : TransferModel.State a wi wo) (inputs : List (Input a wi wo)) : IO Result := do
  let mut logical := initialState
  let mut expected := capture a initialState
  let mut result : Result := ⟨expected, 0, 0, 0, 0, #[], #[]⟩
  for i in inputs do
    let o := observe i logical
    unless decide (o = expectedOutput i expected) do
      throw (IO.userError s!"edge {result.edges}: incorrect pre-edge ports/status")
    if o.startReady && i.start.isSome then result := { result with starts := result.starts+1 }
    if o.source.ready && i.sourceRequest.isSome then
      result := { result with sourceRequests := result.sourceRequests+1 }
    if o.destination.ready && i.destinationRequest.isSome then
      result := { result with destinationRequests := result.destinationRequests+1 }
    if i.sourceResponseReady then
      if let some value := o.source.offered then
        result := { result with sourceResponses := result.sourceResponses.push value.toNat }
    if i.destinationResponseReady then
      if let some value := o.destination.offered then
        result := { result with destinationResponses := result.destinationResponses.push value.toNat }
    expected := oracleStep a wo f i expected
    logical := materialize a wi wo (step m i logical)
    unless capture a logical == expected do
      throw (IO.userError s!"edge {result.edges}: expected {repr expected}, got {repr (capture a logical)}")
    unless decide (observe i logical = expectedOutput i expected) do
      throw (IO.userError s!"edge {result.edges}: incorrect post-edge ports/status")
    result := { result with edges := result.edges+1 }
  return { result with finalState := expected }

def inversion (w : Nat) : Stream.Map w w :=
  ⟨.inv (.input .data), fun value => ~~~value, fun _ => rfl⟩

def lowNibble : Stream.Map 8 4 :=
  ⟨.slice 0 4 (by decide) (.input .data), fun value => value.extractLsb' 0 4, fun _ => rfl⟩

def command (a sourceBase destinationBase length : Nat) : TransferModel.RawCommand a :=
  ⟨BitVec.ofNat a sourceBase, BitVec.ofNat a destinationBase, BitVec.ofNat (a+1) length⟩

def loaderTransferReadback : IO Nat := do
  let source := #[17, 88, 33, 44]
  let destination := #[9, 7, 13, 3]
  let load : List (Input 2 8 4) := (List.range 4).map fun k =>
    ⟨false, none, some (.write (BitVec.ofNat 2 k) (BitVec.ofNat 8 source[k]!)), true,
      some (.write (BitVec.ofNat 2 k) (BitVec.ofNat 4 destination[k]!)), true⟩
  let noisy : Input 2 8 4 :=
    ⟨false, some (command 2 3 3 7), some (.write 1 255), false, some (.write 0 15), false⟩
  let start := { noisy with start := some (command 2 1 0 3) }
  let readback : List (Input 2 8 4) := (List.range 4).map fun k =>
    ⟨false, none, some (.read (BitVec.ofNat 2 k)), true, some (.read (BitVec.ofNat 2 k)), true⟩
  let r ← runFrom 2 8 4 lowNibble (fun n => n%16) (initial 2 8 4 #[0, 0, 0, 0] #[0, 0, 0, 0])
    (load ++ [start] ++ List.replicate 6 noisy ++ readback ++ [quiet])
  unless r.finalState.source == source && r.finalState.destination == #[8, 1, 12, 3] &&
      r.sourceResponses == source && r.destinationResponses == #[8, 1, 12, 3] &&
      r.starts == 1 && r.sourceRequests == 8 && r.destinationRequests == 8 do
    throw (IO.userError "load/start priority/busy exclusion/readback workflow failed")
  return r.edges

def pendingBeforeStart : IO Nat := do
  let readBoth : Input 2 8 8 := ⟨false, none, some (.read 1), true, some (.read 2), true⟩
  let blocked : Input 2 8 8 :=
    ⟨false, some (command 2 0 0 1), some (.write 0 255), false, some (.write 0 255), false⟩
  let sourceDrain := { blocked with sourceResponseReady := true }
  let bothDrain := { sourceDrain with destinationResponseReady := true }
  let r ← runFrom 2 8 8 (inversion 8) (fun n => 255-n)
    (initial 2 8 8 #[17, 88, 33, 44] #[91, 7, 201, 63])
    [readBoth, blocked, blocked, sourceDrain, bothDrain, blocked, quiet, quiet, quiet]
  unless r.starts == 1 && r.sourceRequests == 1 && r.destinationRequests == 1 &&
      r.sourceResponses == #[88] && r.destinationResponses == #[201] &&
      r.finalState.source == #[17, 88, 33, 44] && r.finalState.destination == #[238, 7, 201, 63] &&
      r.finalState.phase == 0 && !r.finalState.done do
    throw (IO.userError "pending responses were lost, accepted start too early, or new requests bypassed start priority")
  return r.edges

def exhaustiveIdle : IO Nat := do
  let requests : Array (Option (StreamModel.Request 1 2)) :=
    #[none, some (.read 0), some (.read 1), some (.write 0 1), some (.write 1 3)]
  let starts : Array (Option (TransferModel.RawCommand 1)) :=
    #[none, some (command 1 0 0 2), some (command 1 1 1 0), some (command 1 1 1 2)]
  let mut edges := 0
  for source in [#[0, 0], #[1, 2], #[3, 3]] do
    for destination in [#[0, 0], #[2, 1], #[3, 3]] do
      for sourcePending in [false, true] do
        for destinationPending in [false, true] do
          let init := initial 1 2 2 source destination
          let init := { init with
            source := { init.source with pending := sourcePending },
            destination := { init.destination with pending := destinationPending } }
          for sourceReady in [false, true] do
            for destinationReady in [false, true] do
              for sourceRequest in requests do
                for destinationRequest in requests do
                  for start in starts do
                    let r ← runFrom 1 2 2 (inversion 2) (fun n => 3-n) init
                      [⟨false, start, sourceRequest, sourceReady, destinationRequest, destinationReady⟩]
                    edges := edges+r.edges
  return edges

def exhaustiveCommands (a wi wo : Nat) (m : Stream.Map wi wo) (f : Nat → Nat) : IO Nat := do
  let source := (Array.range (2^a)).map (fun k => (13*k+7)%2^wi)
  let destination := (Array.range (2^a)).map (fun k => (9*k+3)%2^wo)
  let mut edges := 0
  for sourceBase in [0:2^a] do
    for destinationBase in [0:2^a] do
      for length in [0:2^(a+1)] do
        let valid := length ≤ 2^a-sourceBase && length ≤ 2^a-destinationBase
        let i : Input a wi wo :=
          ⟨false, some (command a sourceBase destinationBase length), some (.write 0 0), true,
            some (.write 0 0), true⟩
        let r ← runFrom a wi wo m f (initial a wi wo source destination)
          (i :: List.replicate (if valid then 2*length+1 else 1) quiet)
        let expected := (Array.range (2^a)).map fun address =>
          if valid && destinationBase ≤ address && address < destinationBase+length then
            f source[sourceBase+(address-destinationBase)]! % 2^wo
          else destination[address]!
        unless r.starts == 1 && r.sourceRequests == 0 && r.destinationRequests == 0 &&
            r.finalState.source == source && r.finalState.destination == expected &&
            r.finalState.phase == 0 && !r.finalState.done && !r.finalState.error do
          throw (IO.userError s!"command {sourceBase}/{destinationBase}/{length}: incorrect acceptance/completion")
        edges := edges+r.edges
  return edges

def aborts : IO Nat := do
  let init := initial 2 8 8 #[17, 88, 33, 44] #[91, 7, 201, 63]
  let start : Input 2 8 8 := { quiet with start := some (command 2 0 0 4) }
  let reset : Input 2 8 8 :=
    ⟨true, some (command 2 0 0 4), some (.write 0 255), true, some (.write 0 255), true⟩
  let mut edges := 0
  for cut in [0:9] do
    let r ← runFrom 2 8 8 (inversion 8) (fun n => 255-n) init
      ([start] ++ List.replicate cut quiet ++ [reset, quiet, quiet,
        ⟨false, none, some (.read 0), true, some (.read 0), true⟩, quiet])
    let expected := (Array.range 4).map fun k =>
      if k < cut/2 then 255-(#[17, 88, 33, 44] : Array Nat)[k]! else (#[91, 7, 201, 63] : Array Nat)[k]!
    unless r.finalState.destination == expected && r.finalState.source == #[17, 88, 33, 44] &&
        r.finalState.phase == 0 && !r.finalState.sourcePending && !r.finalState.destinationPending &&
        r.sourceResponses == #[17] && r.destinationResponses == #[expected[0]!] do
      throw (IO.userError s!"abort at {cut}: prefix, reset masking, or post-abort host readback failed")
    edges := edges+r.edges
  let dirty := { init with
    control := { init.control with phase := .transfer, index := 17, done := true, error := true },
    source := { init.source with pending := true }, destination := { init.destination with pending := true } }
  let r ← runFrom 2 8 8 (inversion 8) (fun n => 255-n) dirty [reset, quiet]
  unless r.finalState.sourceQ == 123 && r.finalState.destinationQ == 199 && r.starts == 0 &&
      r.sourceResponses.isEmpty && r.destinationResponses.isEmpty do
    throw (IO.userError "reset failed to preserve arbitrary Q or masked handshake")
  return edges+r.edges

def randomRequest (a w seed : Nat) : Option (StreamModel.Request a w) :=
  match seed%3 with
  | 0 => none
  | 1 => some (.read (BitVec.ofNat a (seed/3)))
  | _ => some (.write (BitVec.ofNat a (seed/3)) (BitVec.ofNat w (seed/17)))

def randomRun (a wi wo : Nat) (m : Stream.Map wi wo) (f : Nat → Nat) : IO Nat := do
  let mut seed := 49157
  let mut inputs : Array (Input a wi wo) := #[]
  for _ in [0:1024] do
    seed := (1664525*seed+1013904223)%4294967296
    inputs := inputs.push ⟨seed%37 == 0,
      if seed%5 == 0 then some (command a (seed/7) (seed/19) (seed/29)) else none,
      randomRequest a wi (seed/41), seed%2 == 0,
      randomRequest a wo (seed/97), seed%3 != 0⟩
  let source := (Array.range (2^a)).map (fun k => (17*k+11)%2^wi)
  let destination := (Array.range (2^a)).map (fun k => (23*k+5)%2^wo)
  let r ← runFrom a wi wo m f (initial a wi wo source destination) (inputs.toList ++ List.replicate (2*2^a+2) quiet)
  return r.edges

end MemoryTransferHostModelTests

elab "#audit_transfer_host_model" : command => do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    if name.toString.startsWith "Pinwheel.Hardware.Memory.TransferHostModel." ||
        name.toString.startsWith "_private.Pinwheel.Hardware.Memory.TransferHostModel." then
      count := count+1
      let axioms ← collectAxioms name
      let bad := axioms.filter fun a => a != ``propext && a != ``Classical.choice && a != ``Quot.sound
      unless bad.isEmpty do throwError "Unapproved axioms in {name}: {bad}"
  if count == 0 then throwError "Empty host wrapper audit"
  logInfo m!"Transfer host model audit: {count} declarations, standard axioms only."

#audit_transfer_host_model

def main : IO Unit := do
  let workflow ← MemoryTransferHostModelTests.loaderTransferReadback
  let pending ← MemoryTransferHostModelTests.pendingBeforeStart
  let idle ← MemoryTransferHostModelTests.exhaustiveIdle
  let mut commands := 0
  commands := commands + (← MemoryTransferHostModelTests.exhaustiveCommands 0 0 0
    (MemoryTransferHostModelTests.inversion 0) (fun _ => 0))
  commands := commands + (← MemoryTransferHostModelTests.exhaustiveCommands 1 2 2
    (MemoryTransferHostModelTests.inversion 2) (fun n => 3-n))
  commands := commands + (← MemoryTransferHostModelTests.exhaustiveCommands 2 8 4
    MemoryTransferHostModelTests.lowNibble (fun n => n%16))
  let aborts ← MemoryTransferHostModelTests.aborts
  let mut random := 0
  random := random + (← MemoryTransferHostModelTests.randomRun 0 0 0
    (MemoryTransferHostModelTests.inversion 0) (fun _ => 0))
  random := random + (← MemoryTransferHostModelTests.randomRun 1 2 2
    (MemoryTransferHostModelTests.inversion 2) (fun n => 3-n))
  random := random + (← MemoryTransferHostModelTests.randomRun 2 8 4
    MemoryTransferHostModelTests.lowNibble (fun n => n%16))
  IO.println s!"Transfer host model: {workflow} loader/transfer/readback, {pending} pending-drain, {idle} exhaustive idle, {commands} command, {aborts} abort/recovery, {random} seeded random edges; every state field and pre/post output matches independent integer/array oracle."
