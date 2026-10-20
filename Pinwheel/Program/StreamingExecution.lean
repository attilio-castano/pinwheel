import Pinwheel.Program.Streaming

/-! Bounded-storage operational semantics for the streaming ISA. -/
namespace Pinwheel.Program.Streaming

inductive Phase where
  | free | fetch | boundary | low | high | completed | fault
  deriving DecidableEq, Repr

def Phase.code : Phase → BitVec 3
  | .free => 0 | .fetch => 1 | .boundary => 2 | .low => 3
  | .high => 4 | .completed => 5 | .fault => 6

def Phase.busy : Phase → Bool
  | .fetch | .boundary | .low | .high => true
  | _ => false

def Phase.retained : Phase → Bool
  | .completed | .fault => true
  | _ => false

/-- Physical host actions are independent of the engine's queue actions. -/
structure Input where
  «initialize» : Bool := false
  command : BitVec 4 := 0
  startCount : BitVec 16 := 0
  expectedGeneration : BitVec 16 := 0
  expectedTransfer : BitVec 16 := 0
  txPush : Bool := false
  rxPop : Bool := false
  txData : BitVec 32 := 0
  txBits : BitVec 6 := 32
  rawInputs : BitVec 2 := 0
  deriving DecidableEq, Repr

/-- No field contains a transfer transcript. All storage has a fixed width or fixed depth. -/
structure State (addrBits : Nat) where
  phase : Phase := .free
  pc : BitVec 7 := 0
  current : Instruction := .halt
  total : BitVec 16 := 0
  remaining : BitVec 16 := 0
  countdown : BitVec 8 := 0
  cellBit : Bool := false
  tx : Queue addrBits := Queue.empty addrBits
  rx : Queue addrBits := Queue.empty addrBits
  txShift : BitVec 32 := 0
  txValid : BitVec 6 := 0
  rxPartial : BitVec 32 := 0
  rxUsed : BitVec 6 := 0
  samplerFirst : BitVec 2 := 0
  samplerSecond : BitVec 2 := 0
  pins : Engine.Reactive.Pins := {}
  generation : BitVec 16 := 0
  transfer : BitVec 16 := 0
  txAccepted : BitVec 16 := 0
  txConsumed : BitVec 16 := 0
  rxProduced : BitVec 16 := 0
  rxPopped : BitVec 16 := 0
  deriving DecidableEq, Repr

def Instruction.cell : Instruction → Cell
  | .pulse c | .stream c => c
  | _ => {}

def State.owned (s : State addrBits) (i : Input) : Bool :=
  (s.phase.busy || s.phase.retained) && i.expectedGeneration == s.generation &&
    i.expectedTransfer == s.transfer

def State.sample (s : State addrBits) (raw : BitVec 2) : State addrBits :=
  { s with samplerFirst := raw, samplerSecond := s.samplerFirst }

def State.lastCell (s : State addrBits) : Bool :=
  s.current.isStream && s.remaining == 1

def Cell.basePins (c : Cell) (high last : Bool) : Engine.Reactive.Pins :=
  let base := if high then c.highPins else c.lowPins
  let levels := if high then c.lastHighLevels else c.lastLowLevels
  let enabled := if high then c.lastHighEnabled else c.lastLowEnabled
  if last then ⟨base.levels ||| levels, base.enabled ||| enabled⟩ else base

/-- TX changes only its selected output. Enable mode encodes open-drain data. -/
def Cell.dataPins (c : Cell) (high last bit : Bool) : Engine.Reactive.Pins :=
  let base := c.basePins high last
  let value := bit != c.txInvert
  let mask : BitVec 3 := 1 <<< c.txOutput.val
  if c.transmit then
    if c.txEnableMode then
      ⟨base.levels &&& ~~~mask,
        (base.enabled &&& ~~~mask) ||| (if value then 0 else mask)⟩
    else
      ⟨(base.levels &&& ~~~mask) ||| (if value then mask else 0), base.enabled ||| mask⟩
  else base

def State.txReady (s : State addrBits) : Bool :=
  !s.current.cell.transmit || s.txValid != 0 || s.tx.readable

def State.rxReady (s : State addrBits) : Bool :=
  !s.current.cell.receive || s.rx.writable

def State.canReserve (s : State addrBits) : Bool :=
  !s.current.isStream || (s.txReady && s.rxReady)

def State.selectedTx (s : State addrBits) : Chunk :=
  if s.txValid == 0 then s.tx.peek
  else ⟨s.txShift, ⟨(s.txValid.toNat - 1) % 32, Nat.mod_lt _ (by decide)⟩⟩

def State.enginePop (s : State addrBits) : Bool :=
  s.phase == .boundary && s.canReserve && s.current.isStream &&
    s.current.cell.transmit && s.txValid == 0

def State.captures (s : State addrBits) : Bool :=
  s.phase == .low && s.countdown == 0 && s.current.isStream && s.current.cell.receive

def State.capturedWord (s : State addrBits) : BitVec 32 :=
  (s.rxPartial <<< 1) ||| BitVec.ofNat 32 (if s.samplerSecond[s.current.cell.rxInput.val] then 1 else 0)

def State.enginePush (s : State addrBits) : Option Chunk :=
  if s.captures && (s.rxUsed == 31 || s.remaining == 1) then
    some ⟨s.capturedWord, ⟨s.rxUsed.toNat % 32, Nat.mod_lt _ (by decide)⟩⟩
  else none

/-- An already admitted host reservation can finish after the engine retains.
Unused accepted TX stays owned in the FIFO and prevents a drained RELEASE. -/
def State.hostPush (s : State addrBits) (i : Input) : Option Chunk :=
  if h : s.owned i = true ∧ i.txPush = true ∧
      0 < i.txBits.toNat ∧ i.txBits.toNat ≤ 32 ∧
      s.txAccepted.toNat + i.txBits.toNat ≤ s.total.toNat then
    some ⟨i.txData, ⟨i.txBits.toNat - 1, by omega⟩⟩
  else none

def State.hostPop (s : State addrBits) (i : Input) : Bool :=
  s.owned i && i.rxPop

def State.stop (p : Program) (s : State addrBits) (failed : Bool) : State addrBits :=
  { s with phase := if failed then .fault else .completed, pins := p.idle }

/-- Engine actions use only pre-edge credits and pre-edge synchronized samples. -/
def engine (p : Program) (s : State addrBits) : State addrBits :=
  let c := s.current.cell
  let isStream := s.current.isStream
  match s.phase with
  | .fetch =>
    match p.fetch s.pc.toNat with
    | none => s.stop p true
    | some .halt => s.stop p false
    | some .fault => s.stop p true
    | some (.stream cell) =>
      if s.remaining == 0 then { s with pc := s.pc + 1 }
      else { s with
        phase := .boundary, current := .stream cell,
        pins := cell.basePins false (s.remaining == 1) }
    | some (.pulse cell) =>
      { s with phase := .boundary, current := .pulse cell, pins := cell.lowPins }
  | .boundary =>
    if s.canReserve then
      let word := s.selectedTx
      let bit := isStream && c.transmit && word.data[31]
      { s with
        phase := .low, countdown := BitVec.ofNat 8 c.lowDuration.val,
        cellBit := bit,
        txShift := if isStream && c.transmit then word.data <<< 1 else s.txShift,
        txValid := if isStream && c.transmit then BitVec.ofNat 6 (word.validBits - 1) else s.txValid,
        txConsumed := s.txConsumed + (if isStream && c.transmit then 1 else 0),
        pins := if isStream then c.dataPins false s.lastCell bit else c.lowPins }
    else s
  | .low =>
    if s.countdown == 0 then
      { s with
        phase := .high, countdown := BitVec.ofNat 8 c.highDuration.val,
        rxPartial := if s.captures then
          (if s.enginePush.isSome then 0 else s.capturedWord) else s.rxPartial,
        rxUsed := if s.captures then
          (if s.enginePush.isSome then 0 else s.rxUsed + 1) else s.rxUsed,
        rxProduced := s.rxProduced + (if s.captures then 1 else 0),
        pins := if isStream then c.dataPins true s.lastCell s.cellBit else c.highPins }
    else { s with countdown := s.countdown - 1 }
  | .high =>
    if s.countdown == 0 then
      { s with
        phase := if isStream && s.remaining.toNat > 1 then .boundary else .fetch,
        pc := if isStream && s.remaining.toNat > 1 then s.pc else s.pc + 1,
        remaining := s.remaining - (if isStream then 1 else 0),
        pins := c.basePins false s.lastCell }
    else { s with countdown := s.countdown - 1 }
  | _ => s

/-- Host queue service and engine movement are simultaneous, with no empty/full bypass. -/
def clock (p : Program) (i : Input) (s : State addrBits) : State addrBits :=
  let pushed := s.hostPush i
  let popped := s.hostPop i
  let next := engine p s
  { next with
    tx := s.tx.tick pushed s.enginePop
    rx := s.rx.tick s.enginePush popped
    txAccepted := s.txAccepted +
      (if s.tx.willPush pushed then BitVec.ofNat 16 (pushed.getD {}).validBits else 0)
    rxPopped := s.rxPopped +
      (if s.rx.willPop popped then BitVec.ofNat 16 s.rx.peek.validBits else 0)
    samplerFirst := i.rawInputs
    samplerSecond := s.samplerFirst }

def State.canStart (s : State addrBits) (i : Input) : Bool :=
  s.phase == .free && i.expectedGeneration == s.generation && s.transfer != 65535

def State.drained (s : State addrBits) : Bool :=
  s.tx.count == 0 && s.rx.count == 0 && s.txValid == 0 && s.rxUsed == 0

def State.canRelease (s : State addrBits) (i : Input) : Bool :=
  s.phase.retained && s.owned i && s.drained

def State.reset (p : Program) (s : State addrBits) (cold : Bool) : State addrBits :=
  { pins := p.idle, generation := if cold then 0 else s.generation,
    transfer := if cold then 0 else s.transfer }

def State.start (p : Program) (s : State addrBits) (i : Input) : State addrBits :=
  { phase := .fetch, total := i.startCount, remaining := i.startCount,
    pins := p.idle, generation := s.generation, transfer := s.transfer + 1,
    samplerFirst := i.rawInputs, samplerSecond := s.samplerFirst }

def State.release (p : Program) (s : State addrBits) (i : Input) : State addrBits :=
  { pins := p.idle, generation := s.generation, transfer := s.transfer,
    samplerFirst := i.rawInputs, samplerSecond := s.samplerFirst }

/-- Cold reset dominates warm reset, then admitted START/RELEASE; rejected commands still clock. -/
def step (p : Program) (i : Input) (s : State addrBits) : State addrBits :=
  if i.initialize then s.reset p true
  else if i.command == 15 then s.reset p false
  else if i.command == 3 && s.canStart i then s.start p i
  else if i.command == 4 && s.canRelease i then s.release p i
  else clock p i s

def run (p : Program) (s : State addrBits) (inputs : List Input) : State addrBits :=
  inputs.foldl (fun s i => step p i s) s

end Pinwheel.Program.Streaming
