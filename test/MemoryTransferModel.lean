import Lean
import Pinwheel.Hardware.Memory.TransferModel

open Lean Elab Command
open Pinwheel.Hardware
open Pinwheel.Hardware.Memory
open Pinwheel.Hardware.Memory.TransferModel

namespace MemoryTransferModelTests

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

def capture (a : Nat) (s : State a wi wo) : Oracle :=
  ⟨match s.control.phase with | .idle => 0 | .issueRead => 1 | .transfer => 2,
    s.control.config.sourceBase.toNat, s.control.config.destinationBase.toNat,
    s.control.config.length, s.control.index, s.control.done, s.control.error,
    words a s.source.memory.contents, words a s.destination.memory.contents,
    s.source.memory.q.toNat, s.destination.memory.q.toNat, s.source.pending, s.destination.pending⟩

def materialize (a wi wo : Nat) (s : State a wi wo) : State a wi wo :=
  let c := capture a s
  { s with
    source := ⟨⟨contents a wi c.source, BitVec.ofNat wi c.sourceQ⟩, c.sourcePending⟩
    destination := ⟨⟨contents a wo c.destination, BitVec.ofNat wo c.destinationQ⟩, c.destinationPending⟩ }

def clearControl (s : Oracle) : Oracle :=
  { s with
    phase := 0
    sourceBase := 0
    destinationBase := 0
    length := 0
    index := 0
    done := false
    error := false }

/-- Independent integer/array controller and memory oracle. It calls no range
decoder, controller transition, or stream-memory transition from the model. -/
def oracleStep (a wo : Nat) (f : Nat → Nat) (i : HostInput a) (s : Oracle) : Oracle :=
  if i.reset then { clearControl s with sourcePending := false, destinationPending := false }
  else
    let clear := { s with done := false, error := false, destinationPending := false }
    if s.phase == 0 then
      match i.start with
      | none => clear
      | some c =>
        let length := c.length.toNat
        if length ≤ 2^a-c.sourceBase.toNat && length ≤ 2^a-c.destinationBase.toNat then
          { clear with
            sourceBase := c.sourceBase.toNat
            destinationBase := c.destinationBase.toNat
            length := length
            index := 0
            phase := if length == 0 then 0 else 1
            done := length == 0 }
        else { clearControl clear with error := true }
    else if s.phase == 1 then
      if s.sourcePending then clear
      else { clear with
        phase := 2
        sourcePending := true
        sourceQ := s.source[(s.sourceBase+s.index) % 2^a]?.getD 0 }
    else
      if !s.sourcePending then clear
      else { clear with
        sourcePending := false
        index := s.index+1
        phase := if s.index+1 < s.length then 1 else 0
        done := s.index+1 ≥ s.length
        destination := s.destination.set! ((s.destinationBase+s.index) % 2^a) (f s.sourceQ % 2^wo) }

def expectedOutput (a wo : Nat) (f : Nat → Nat) (i : HostInput a) (s : Oracle) : Output a wo :=
  if i.reset then ⟨false, false, false, false, none, false, none⟩
  else ⟨s.phase == 0, s.phase != 0, s.done, s.error,
    if s.phase == 1 then some (BitVec.ofNat a (s.sourceBase+s.index)) else none,
    s.phase == 2,
    if s.phase == 2 && s.sourcePending then
      some (BitVec.ofNat a (s.destinationBase+s.index), BitVec.ofNat wo (f s.sourceQ))
    else none⟩

def runFrom (a wi wo : Nat) (m : Stream.Map wi wo) (f : Nat → Nat)
    (initial : State a wi wo) (inputs : List (HostInput a)) : IO (Oracle × Nat) := do
  let mut logical := initial
  let mut expected := capture a initial
  let mut edges := 0
  for i in inputs do
    unless decide ((component m).observe i logical = expectedOutput a wo f i expected) do
      throw (IO.userError s!"edge {edges}: incorrect pre-edge ports/status")
    expected := oracleStep a wo f i expected
    logical := materialize a wi wo (closedStep m i logical)
    let actual := capture a logical
    unless actual == expected do
      throw (IO.userError s!"edge {edges}: expected {repr expected}, got {repr actual}")
    unless decide ((component m).observe i logical = expectedOutput a wo f i expected) do
      throw (IO.userError s!"edge {edges}: incorrect post-edge ports/status")
    edges := edges+1
  return (expected, edges)

def inversion (w : Nat) : Stream.Map w w :=
  ⟨.inv (.input .data), fun value => ~~~value, fun _ => rfl⟩

def lowNibble : Stream.Map 8 4 :=
  ⟨.slice 0 4 (by decide) (.input .data), fun value => value.extractLsb' 0 4, fun _ => rfl⟩

def exhaustiveCommands (a wi wo : Nat) (m : Stream.Map wi wo) (f : Nat → Nat)
    (sourceSeeds destinationSeeds : Array Nat) : IO Nat := do
  let mut edges := 0
  for ss in sourceSeeds do
    let source := (Array.range (2^a)).map (fun k => ss / (2^wi)^k % 2^wi)
    for ds in destinationSeeds do
      let destination := (Array.range (2^a)).map (fun k => ds / (2^wo)^k % 2^wo)
      let initial := initialState
        (⟨contents a wi source, BitVec.ofNat wi (ss*3+1)⟩ : Sram.State a wi)
        (⟨contents a wo destination, BitVec.ofNat wo (ds*5+2)⟩ : Sram.State a wo)
      for sourceBase in [0:2^a] do
        for destinationBase in [0:2^a] do
          for length in [0:2^(a+1)] do
            let command : RawCommand a :=
              ⟨BitVec.ofNat a sourceBase, BitVec.ofNat a destinationBase, BitVec.ofNat (a+1) length⟩
            let valid := length ≤ 2^a-sourceBase && length ≤ 2^a-destinationBase
            let (result, count) ← runFrom a wi wo m f initial
              (⟨false, some command⟩ :: List.replicate (if valid then 2*length+1 else 1) quiet)
            let expected := (Array.range (2^a)).map fun address =>
              if valid && destinationBase ≤ address && address < destinationBase+length then
                f source[sourceBase+(address-destinationBase)]! % 2^wo
              else destination[address]!
            unless result.destination == expected && result.source == source &&
                !result.done && !result.error && result.phase == 0 do
              throw (IO.userError s!"command {sourceBase}/{destinationBase}/{length}: wrong completion or pulse clear")
            edges := edges+count
  return edges

def abortsAndBusy : IO Nat := do
  let m := inversion 8
  let f := fun n => 255-n
  let source := #[17, 88, 33, 44]
  let destination := #[91, 7, 201, 63]
  let initial := initialState
    (⟨contents 2 8 source, 123⟩ : Sram.State 2 8)
    (⟨contents 2 8 destination, 199⟩ : Sram.State 2 8)
  let full : RawCommand 2 := ⟨0, 0, 4⟩
  let invalid : RawCommand 2 := ⟨3, 3, 2⟩
  let mut edges := 0
  for cut in [0:9] do
    let (result, count) ← runFrom 2 8 8 m f initial
      ([⟨false, some full⟩] ++ List.replicate cut quiet ++
        [⟨true, some invalid⟩, quiet, quiet, quiet])
    let expected := (Array.range 4).map fun k => if k < cut/2 then f source[k]! else destination[k]!
    unless result.destination == expected && result.source == source &&
        !result.sourcePending && !result.destinationPending do
      throw (IO.userError s!"abort after {cut} edges lost committed prefix or retained a stale response")
    edges := edges+count
  let (_, busyCount) ← runFrom 2 8 8 m f initial
    ([⟨false, some full⟩] ++ List.replicate 8 ⟨false, some invalid⟩ ++ [quiet])
  edges := edges+busyCount
  let one : RawCommand 2 := ⟨3, 2, 1⟩
  let (_, heldCount) ← runFrom 2 8 8 m f initial (List.replicate 6 ⟨false, some one⟩ ++ [quiet])
  edges := edges+heldCount
  -- Reset also recovers arbitrary pending bits, Q, and incoherent protocol progress.
  let dirty := { initial with
    control := { initial.control with phase := .transfer, index := 17, done := true, error := true }
    source := { initial.source with pending := true }
    destination := { initial.destination with pending := true } }
  let (_, dirtyCount) ← runFrom 2 8 8 m f dirty [⟨true, some full⟩, quiet]
  return edges+dirtyCount

def openStalls : IO Nat := do
  let m := inversion 8
  let command : RawCommand 2 := ⟨1, 2, 2⟩
  let invalid : RawCommand 2 := ⟨3, 3, 7⟩
  let inputs : Array (Input 2 8) := #[
    ⟨false, some command, true, some 91, true⟩,
    ⟨false, some invalid, false, some 99, true⟩,
    ⟨false, none, false, none, false⟩,
    ⟨false, none, true, none, false⟩,
    ⟨false, none, true, none, true⟩,
    ⟨false, none, true, some 3, false⟩,
    ⟨false, some invalid, true, some 3, false⟩,
    ⟨false, none, true, some 3, true⟩,
    ⟨false, none, false, some 51, true⟩,
    ⟨false, none, true, none, true⟩,
    ⟨false, none, true, some 7, true⟩,
    ⟨false, none, true, none, true⟩]
  let expectedPhase := #[1, 1, 1, 2, 2, 2, 2, 1, 1, 2, 0, 0]
  let expectedIndex := #[0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 2, 2]
  let mut control := initialControl 2
  let mut writes : Array (Nat × Nat) := #[]
  for k in [0:inputs.size] do
    let i := inputs[k]?.getD ⟨false, none, false, none, false⟩
    let o := observe m i control
    if let some (address, value) := o.destinationWrite then
      if i.destinationReady then writes := writes.push (address.toNat, value.toNat)
      else unless address.toNat == 2 && value.toNat == 252 && !o.sourceResponseReady do
        throw (IO.userError "stalled response/write changed or was retired")
    control := step i control
    let phase := match control.phase with | .idle => 0 | .issueRead => 1 | .transfer => 2
    unless phase == expectedPhase[k]! && control.index == expectedIndex[k]! &&
        control.done == (k == 10) && !control.error do
      throw (IO.userError s!"open controller edge {k}: incorrect service/stall/status behavior")
  unless writes == #[(2,252),(3,248)] do
    throw (IO.userError "open controller lost, duplicated, or misrouted transformed writes")
  return inputs.size

end MemoryTransferModelTests

elab "#audit_transfer_model" : command => do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    if name.toString.startsWith "Pinwheel.Hardware.Memory.TransferModel." ||
        name.toString.startsWith "_private.Pinwheel.Hardware.Memory.TransferModel." then
      count := count+1
      let axioms ← collectAxioms name
      let bad := axioms.filter fun a => a != ``propext && a != ``Classical.choice && a != ``Quot.sound
      unless bad.isEmpty do throwError "Unapproved axioms in {name}: {bad}"
  if count == 0 then throwError "Empty transfer model audit"
  logInfo m!"Transfer model audit: {count} declarations, standard axioms only."

#audit_transfer_model

def main : IO Unit := do
  let mut edges := 0
  edges := edges + (← MemoryTransferModelTests.exhaustiveCommands 0 0 0
    (MemoryTransferModelTests.inversion 0) (fun _ => 0) #[0] #[0])
  edges := edges + (← MemoryTransferModelTests.exhaustiveCommands 1 2 2
    (MemoryTransferModelTests.inversion 2) (fun n => 3-n) (Array.range 16) (Array.range 16))
  edges := edges + (← MemoryTransferModelTests.exhaustiveCommands 2 8 4
    MemoryTransferModelTests.lowNibble (fun n => n%16) #[0, 1234567, 4294967295] #[0, 12345, 65535])
  let aborts ← MemoryTransferModelTests.abortsAndBusy
  let openEdges ← MemoryTransferModelTests.openStalls
  IO.println s!"Transfer model: {edges} exhaustive-command composition edges, {aborts} abort/busy/restart edges, {openEdges} open-stall edges; closed state and pre/post outputs match the independent oracle; open service/stall behavior checked."
