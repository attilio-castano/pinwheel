import Pinwheel.Program.StreamingReady
import Pinwheel.Program.StreamingSafety

/-! Bounded sampled-ready execution. WAIT uses the cached guard and countdown;
samplers and independently owned host queue actions continue on every clock. -/
namespace Pinwheel.Program.StreamingReady

def State.owned (s : State a) (i : Input) : Bool :=
  (s.phase.busy || s.phase.retained) && i.expectedGeneration == s.generation &&
    i.expectedTransfer == s.transfer

def State.sample (s : State a) (raw : BitVec 2) : State a :=
  {s with samplerFirst := raw, samplerSecond := s.samplerFirst}

def State.lastCell (s : State a) : Bool := s.current.isStream && s.remaining == 1

def State.txReady (s : State a) : Bool :=
  !s.current.cell.transmit || s.txValid != 0 || s.tx.readable

def State.rxReady (s : State a) : Bool := !s.current.cell.receive || s.rx.writable

def State.canReserve (s : State a) : Bool :=
  !s.current.isStream || (s.txReady && s.rxReady)

def State.selectedTx (s : State a) : Chunk :=
  if s.txValid == 0 then s.tx.peek
  else ⟨s.txShift, ⟨(s.txValid.toNat - 1) % 32, Nat.mod_lt _ (by decide)⟩⟩

def State.enginePop (s : State a) : Bool :=
  s.phase == .boundary && s.canReserve && s.current.isStream &&
    s.current.cell.transmit && s.txValid == 0

def State.waitReady (s : State a) : Bool := s.current.guard.matches s.samplerSecond

def State.timedOut (s : State a) : Bool :=
  s.phase == .waiting && !s.waitReady && s.current.guard.limit.expires s.countdown

def State.captures (s : State a) : Bool :=
  s.current.isStream && s.current.cell.receive &&
    ((s.phase == .low && s.countdown == 0 && !s.current.hasHighGuard) ||
      (s.phase == .waiting && s.waitReady))

def State.capturedWord (s : State a) : BitVec 32 :=
  (s.rxPartial <<< 1) ||| BitVec.ofNat 32
    (if s.samplerSecond[s.current.cell.rxInput.val] then 1 else 0)

def State.emittingCapture (s : State a) : Bool :=
  s.captures && (s.rxUsed == 31 || s.remaining == 1)

/-- A timeout exports existing samples, without manufacturing a new sample. -/
def State.timeoutChunk (s : State a) : Option Chunk :=
  if s.rxUsed == 0 then none
  else some ⟨s.rxPartial, ⟨(s.rxUsed.toNat - 1) % 32, Nat.mod_lt _ (by decide)⟩⟩

def State.enginePush (s : State a) : Option Chunk :=
  if s.timedOut then s.timeoutChunk
  else if s.emittingCapture then
    some ⟨s.capturedWord, ⟨s.rxUsed.toNat % 32, Nat.mod_lt _ (by decide)⟩⟩
  else none

def State.hostPush (s : State a) (i : Input) : Option Chunk :=
  if h : s.owned i = true ∧ i.txPush = true ∧
      0 < i.txBits.toNat ∧ i.txBits.toNat ≤ 32 ∧
      s.txAccepted.toNat + i.txBits.toNat ≤ s.total.toNat then
    some ⟨i.txData, ⟨i.txBits.toNat - 1, by omega⟩⟩
  else none

def State.hostPop (s : State a) (i : Input) : Bool := s.owned i && i.rxPop

def State.stop (p : Program) (s : State a) (failed : Bool) : State a :=
  {s with phase := if failed then .fault else .completed, pins := p.idle}

def State.captureData (s : State a) : State a :=
  {s with
    rxPartial := if s.captures then (if s.emittingCapture then 0 else s.capturedWord) else s.rxPartial
    rxUsed := if s.captures then (if s.emittingCapture then 0 else s.rxUsed + 1) else s.rxUsed
    rxProduced := s.rxProduced + (if s.captures then 1 else 0)}

def State.enterHigh (s : State a) : State a :=
  {s.captureData with phase := .high, countdown := BitVec.ofNat 8 s.current.cell.highDuration.val}

def State.timeoutFault (p : Program) (s : State a) : State a :=
  {s with phase := .fault, pins := p.idle, rxPartial := 0, rxUsed := 0}

def State.highPins (s : State a) : Pins :=
  if s.current.isStream then s.current.cell.dataPins true s.lastCell s.cellBit
  else s.current.cell.highPins

def engine (p : Program) (s : State a) : State a :=
  let c := s.current.cell
  let isStream := s.current.isStream
  match s.phase with
  | .fetch =>
    match p.fetch s.pc.toNat with
    | none => s.stop p true
    | some .halt => s.stop p false
    | some .fault => s.stop p true
    | some (.stream cell guard) =>
      if s.remaining == 0 then {s with pc := s.pc + 1}
      else {s with
        phase := .boundary, current := .stream cell guard,
        pins := cell.basePins false (s.remaining == 1)}
    | some (.pulse cell) =>
      {s with phase := .boundary, current := .pulse cell, pins := cell.lowPins}
    | some (.driveWait pins guard) =>
      {s with
        phase := .waiting, current := .driveWait pins guard, pins := pins,
        countdown := guard.limit.initialCountdown}
  | .boundary =>
    if s.canReserve then
      let word := s.selectedTx
      let bit := isStream && c.transmit && word.data[31]
      {s with
        phase := .low, countdown := BitVec.ofNat 8 c.lowDuration.val,
        cellBit := bit,
        txShift := if isStream && c.transmit then word.data <<< 1 else s.txShift,
        txValid := if isStream && c.transmit then BitVec.ofNat 6 (word.validBits - 1) else s.txValid,
        txConsumed := s.txConsumed + (if isStream && c.transmit then 1 else 0),
        pins := if isStream then c.dataPins false s.lastCell bit else c.lowPins}
    else s
  | .low =>
    if s.countdown == 0 then
      if s.current.hasHighGuard then
        {s with phase := .waiting, countdown := s.current.guard.limit.initialCountdown, pins := s.highPins}
      else {s.enterHigh with pins := s.highPins}
    else {s with countdown := s.countdown - 1}
  | .waiting =>
    if s.waitReady then
      if isStream then s.enterHigh
      else {s with phase := .fetch, pc := s.pc + 1, countdown := 0}
    else if s.current.guard.limit.expires s.countdown then s.timeoutFault p
    else {s with countdown := s.current.guard.limit.poll s.countdown}
  | .high =>
    if s.countdown == 0 then
      {s with
        phase := if isStream && s.remaining.toNat > 1 then .boundary else .fetch,
        pc := if isStream && s.remaining.toNat > 1 then s.pc else s.pc + 1,
        remaining := s.remaining - (if isStream then 1 else 0),
        pins := c.basePins false s.lastCell}
    else {s with countdown := s.countdown - 1}
  | _ => s

def clock (p : Program) (i : Input) (s : State a) : State a :=
  let pushed := s.hostPush i
  let popped := s.hostPop i
  let next := engine p s
  {next with
    tx := s.tx.tick pushed s.enginePop
    rx := s.rx.tick s.enginePush popped
    txAccepted := s.txAccepted +
      (if s.tx.willPush pushed then BitVec.ofNat 16 (pushed.getD {}).validBits else 0)
    rxPopped := s.rxPopped +
      (if s.rx.willPop popped then BitVec.ofNat 16 s.rx.peek.validBits else 0)
    samplerFirst := i.rawInputs
    samplerSecond := s.samplerFirst}

def State.canStart (s : State a) (i : Input) : Bool :=
  s.phase == .free && i.expectedGeneration == s.generation && s.transfer != 65535

def State.drained (s : State a) : Bool :=
  s.tx.count == 0 && s.rx.count == 0 && s.txValid == 0 && s.rxUsed == 0

def State.canRelease (s : State a) (i : Input) : Bool :=
  s.phase.retained && s.owned i && s.drained

def State.reset (p : Program) (s : State a) (cold : Bool) : State a :=
  {pins := p.idle, generation := if cold then 0 else s.generation,
    transfer := if cold then 0 else s.transfer}

def State.start (p : Program) (s : State a) (i : Input) : State a :=
  {phase := .fetch, total := i.startCount, remaining := i.startCount,
    pins := p.idle, generation := s.generation, transfer := s.transfer + 1,
    samplerFirst := i.rawInputs, samplerSecond := s.samplerFirst}

def State.release (p : Program) (s : State a) (i : Input) : State a :=
  {pins := p.idle, generation := s.generation, transfer := s.transfer,
    samplerFirst := i.rawInputs, samplerSecond := s.samplerFirst}

def step (p : Program) (i : Input) (s : State a) : State a :=
  if i.initialize then s.reset p true
  else if i.command == 15 then s.reset p false
  else if i.command == 3 && s.canStart i then s.start p i
  else if i.command == 4 && s.canRelease i then s.release p i
  else clock p i s

def run (p : Program) (s : State a) (inputs : List Input) : State a :=
  inputs.foldl (fun s i => step p i s) s

def State.ReservationCredit (s : State a) : Prop :=
  (s.phase = .low ∨ s.phase = .waiting) → s.current.isStream = true →
    s.current.cell.receive = true → s.rx.writable = true

def State.PartialCredit (s : State a) : Prop :=
  0 < s.rxUsed.toNat → s.rx.writable = true

structure State.Structural (s : State a) : Prop where
  accepted : s.txAccepted.toNat ≤ s.total.toNat
  txValid : s.txValid.toNat ≤ 32
  rxUsed : s.rxUsed.toNat < 32
  reservationCredit : s.ReservationCredit
  partialCredit : s.PartialCredit

end Pinwheel.Program.StreamingReady
