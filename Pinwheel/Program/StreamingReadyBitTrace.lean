import Pinwheel.Program.StreamingReadySafety
import Pinwheel.Program.StreamingCounting
import Pinwheel.Program.StreamingQueueTrace

namespace Pinwheel.Program.StreamingReady
set_option linter.unusedSimpArgs false

def State.pendingTx (s : State a) : List Bool := Streaming.Packing.txBits s.txShift s.txValid.toNat
def State.pendingRx (s : State a) : List Bool := Streaming.Packing.rxBits s.rxPartial s.rxUsed.toNat

/-- This event is the value reserved at the low boundary, before pin inversion. -/
def State.txEvent (s : State a) : List Bool :=
  if s.consumes then [s.selectedTx.data[31]] else []

/-- A capture reads the pre-edge second synchronizer stage exactly once. -/
def State.rxEvent (s : State a) : List Bool :=
  if s.captures then [s.samplerSecond[s.current.cell.rxInput.val]] else []


theorem selectedTx_bits (s : State a) (bound : s.txValid.toNat ≤ 32)
    (nonzero : s.txValid ≠ 0#6) : s.selectedTx.txBits = s.pendingTx := by
  have positive : 0 < s.txValid.toNat := by
    have := BitVec.toNat_ne_iff_ne.mpr nonzero
    simp only [BitVec.toNat_ofNat] at this
    omega
  simp [State.selectedTx, nonzero, Streaming.Chunk.txBits, Streaming.Chunk.validBits, State.pendingTx,
    Nat.mod_eq_of_lt (show s.txValid.toNat - 1 < 32 by omega), Nat.sub_add_cancel positive]

theorem consumes_ready (s : State a) (consume : s.consumes = true)
    (emptyShift : s.txValid = 0#6) : s.tx.readable = true := by
  simp only [State.consumes, Bool.and_eq_true] at consume
  rcases consume with ⟨⟨⟨_, reserve⟩, stream⟩, transmit⟩
  simp [State.canReserve, State.txReady, stream, transmit, emptyShift] at reserve
  exact reserve.1

theorem engine_tx_flow (p : Program) (s : State a) (bound : s.txValid.toNat ≤ 32) :
    s.pendingTx ++ (if s.tx.willPop s.enginePop then s.tx.peek.txBits else []) =
      s.txEvent ++ (engine p s).pendingTx := by
  have pop : s.enginePop = (s.consumes && s.txValid == 0) := by
    simp [State.enginePop, State.consumes, Bool.and_assoc]
  have validBound : s.selectedTx.validBits - 1 < 64 := by
    have := s.selectedTx.validBits_le
    omega
  simp only [State.pendingTx, (engine_tx_fields p s).1, (engine_tx_fields p s).2.1]
  by_cases consume : s.consumes = true
  · have length : (BitVec.ofNat 6 (s.selectedTx.validBits - 1)).toNat =
        s.selectedTx.validBits - 1 := by
      simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt validBound]
    simp only [consume, ↓reduceIte, length, State.txEvent, pop, Bool.true_and]
    by_cases empty : s.txValid = 0#6
    · have ready := consumes_ready s consume empty
      simpa [empty, Streaming.Queue.willPop, ready, State.selectedTx, Streaming.Chunk.txBits] using
        Streaming.Packing.txBits_cons s.tx.peek.data s.tx.peek.validBits s.tx.peek.validBits_positive
    · have before := selectedTx_bits s bound empty
      simp only [State.pendingTx] at before
      rw [← before]
      simpa [empty, Streaming.Queue.willPop, Streaming.Chunk.txBits] using
        Streaming.Packing.txBits_cons s.selectedTx.data s.selectedTx.validBits s.selectedTx.validBits_positive
  · simp [consume, pop, State.txEvent, Streaming.Queue.willPop]


theorem engine_rx_flow (p : Program) (s : State a) (bound : s.rxUsed.toNat < 32) :
    s.pendingRx ++ s.rxEvent =
      (match s.enginePush with | some chunk => chunk.rxBits | none => []) ++
        (engine p s).pendingRx := by
  by_cases timeout : s.timedOut = true
  · have noCapture := timedOut_captures_false s timeout
    rw [engine_timedOut p s timeout]
    by_cases empty : s.rxUsed = 0#6
    · simp [State.pendingRx,State.rxEvent,noCapture,State.enginePush,timeout,State.timeoutChunk,
        empty,State.timeoutFault]
    · obtain ⟨chunk,pushed,data,bits⟩ := timeoutChunk_fields s bound empty
      simp [State.pendingRx,State.rxEvent,noCapture,State.enginePush,timeout,pushed,
        State.timeoutFault,Streaming.Chunk.rxBits,data,bits]
  · simp only [State.pendingRx,(engine_rx_fields p s).1,(engine_rx_fields p s).2.1,timeout,↓reduceIte]
    by_cases capture : s.captures = true
    · by_cases flush : (s.rxUsed == 31 || s.remaining == 1) = true
      · simp only [State.enginePush,timeout,State.emittingCapture,capture,flush,State.rxEvent,
          Streaming.Chunk.rxBits,Streaming.Chunk.validBits,Bool.and_self,Bool.false_eq_true,↓reduceIte,
          Streaming.Packing.rxBits_zero,List.append_nil]
        simpa [State.capturedWord,Nat.mod_eq_of_lt bound] using
          (Streaming.Packing.rxBits_capture s.rxPartial s.rxUsed.toNat
            s.samplerSecond[s.current.cell.rxInput.val] bound).symm
      · simp only [State.enginePush,timeout,State.emittingCapture,capture,flush,Bool.true_and,
          Bool.false_eq_true,↓reduceIte,State.rxEvent,List.nil_append]
        simpa [State.capturedWord,BitVec.toNat_add,
          Nat.mod_eq_of_lt (show s.rxUsed.toNat+1 < 64 by omega)] using
          (Streaming.Packing.rxBits_capture s.rxPartial s.rxUsed.toNat
            s.samplerSecond[s.current.cell.rxInput.val] bound).symm
    · simp [State.enginePush,timeout,State.emittingCapture,capture,State.rxEvent]

def State.acceptedBits (s : State a) (i : Input) : List Bool :=
  if s.tx.willPush (s.hostPush i) then (s.hostPush i).getD {} |>.txBits else []

def State.exportedBits (s : State a) (i : Input) : List Bool :=
  if s.rx.willPop (s.hostPop i) then s.rx.peek.rxBits else []


abbrev BitTrace := Streaming.BitTrace

structure BitTrace.Related (trace : BitTrace) (s : State a) : Prop where
  txQueue : s.tx.Contents trace.txQueued
  rxQueue : s.rx.Contents trace.rxQueued
  txOrder : trace.accepted = trace.consumed ++ s.pendingTx ++ trace.txQueued.flatMap Streaming.Chunk.txBits
  rxOrder : trace.captured = trace.exported ++ trace.rxQueued.flatMap Streaming.Chunk.rxBits ++ s.pendingRx

def BitTrace.clock (trace : BitTrace) (s : State a) (i : Input) : BitTrace :=
  { txQueued := s.tx.traceTick trace.txQueued (s.hostPush i) s.enginePop
    rxQueued := s.rx.traceTick trace.rxQueued s.enginePush (s.hostPop i)
    accepted := trace.accepted ++ s.acceptedBits i
    consumed := trace.consumed ++ s.txEvent
    captured := trace.captured ++ s.rxEvent
    exported := trace.exported ++ s.exportedBits i }

theorem BitTrace.Related.clock (p : Program) (s : State a) (i : Input) (trace : BitTrace)
    (related : trace.Related s) (structural : s.Structural) :
    (trace.clock s i).Related (StreamingReady.clock p i s) := by
  constructor
  · exact related.txQueue.tick s.tx trace.txQueued (s.hostPush i) s.enginePop
  · exact related.rxQueue.tick s.rx trace.rxQueued s.enginePush (s.hostPop i)
  · have queue := related.txQueue.flow s.tx trace.txQueued (s.hostPush i) s.enginePop Streaming.Chunk.txBits
    have engineFlow := engine_tx_flow p s structural.txValid
    change (trace.accepted ++ s.acceptedBits i) =
      (trace.consumed ++ s.txEvent) ++ (engine p s).pendingTx ++
        (s.tx.traceTick trace.txQueued (s.hostPush i) s.enginePop).flatMap Streaming.Chunk.txBits
    rw [related.txOrder]
    simp only [List.append_assoc]
    simp only [State.acceptedBits]
    rw [queue, ← List.append_assoc s.pendingTx, engineFlow, List.append_assoc]
  · have queue := related.rxQueue.flow s.rx trace.rxQueued s.enginePush (s.hostPop i) Streaming.Chunk.rxBits
    have engineFlow := engine_rx_flow p s structural.rxUsed
    have arrival : (if s.rx.willPush s.enginePush then (s.enginePush.getD {}).rxBits else []) =
        (match s.enginePush with | some chunk => chunk.rxBits | none => []) := by
      rw [enginePush_credit s structural]
      cases s.enginePush <;> rfl
    rw [arrival] at queue
    change (trace.captured ++ s.rxEvent) =
      (trace.exported ++ s.exportedBits i) ++
        (s.rx.traceTick trace.rxQueued s.enginePush (s.hostPop i)).flatMap Streaming.Chunk.rxBits ++
        (engine p s).pendingRx
    rw [related.rxOrder]
    simp only [List.append_assoc]
    rw [engineFlow, ← List.append_assoc (trace.rxQueued.flatMap Streaming.Chunk.rxBits), queue]
    simp only [List.append_assoc, State.exportedBits]

theorem BitTrace.Related.reset (p : Program) (s : State a) (cold : Bool) :
    BitTrace.Related ({} : BitTrace) (s.reset p cold) := by
  constructor
  · exact Streaming.Queue.empty_contents _
  · exact Streaming.Queue.empty_contents _
  · simp [State.reset, State.pendingTx]
  · simp [State.reset, State.pendingRx]

theorem BitTrace.Related.start (p : Program) (s : State a) (i : Input) :
    BitTrace.Related ({} : BitTrace) (s.start p i) := by
  constructor
  · exact Streaming.Queue.empty_contents _
  · exact Streaming.Queue.empty_contents _
  · simp [State.start, State.pendingTx]
  · simp [State.start, State.pendingRx]

theorem BitTrace.Related.release (p : Program) (s : State a) (i : Input) :
    BitTrace.Related ({} : BitTrace) (s.release p i) := by
  constructor
  · exact Streaming.Queue.empty_contents _
  · exact Streaming.Queue.empty_contents _
  · simp [State.release, State.pendingTx]
  · simp [State.release, State.pendingRx]

/-- Reset cancels a trace; START allocates a new one; RELEASE closes a drained trace. -/
def BitTrace.step (trace : BitTrace) (s : State a) (i : Input) : BitTrace :=
  if i.initialize then {}
  else if i.command == 15 then {}
  else if i.command == 3 && s.canStart i then {}
  else if i.command == 4 && s.canRelease i then {}
  else trace.clock s i

theorem BitTrace.Related.step (p : Program) (s : State a) (i : Input) (trace : BitTrace)
    (related : trace.Related s) (structural : s.Structural) :
    (trace.step s i).Related (StreamingReady.step p i s) := by
  simp only [BitTrace.step, StreamingReady.step]
  split
  · exact BitTrace.Related.reset p s true
  · split
    · exact BitTrace.Related.reset p s false
    · split
      · exact BitTrace.Related.start p s i
      · split
        · exact BitTrace.Related.release p s i
        · exact related.clock p s i trace structural

def traceRun (p : Program) (s : State a) (trace : BitTrace) : List Input → BitTrace
  | [] => trace
  | i :: inputs => traceRun p (step p i s) (trace.step s i) inputs

theorem traceRun_related (p : Program) (s : State a) (trace : BitTrace) (inputs : List Input)
    (related : trace.Related s) (structural : s.Structural) :
    (traceRun p s trace inputs).Related (run p s inputs) := by
  induction inputs generalizing s trace with
  | nil => exact related
  | cons i inputs induction =>
    exact induction (step p i s) (trace.step s i)
      (related.step p s i trace structural) (step_structural p s i structural)

theorem BitTrace.Related.drained (s : State a) (trace : BitTrace)
    (related : trace.Related s) (drained : s.drained = true) :
    trace.accepted = trace.consumed ∧ trace.captured = trace.exported := by
  simp only [State.drained, Bool.and_eq_true, beq_iff_eq] at drained
  rcases drained with ⟨⟨⟨txEmpty, rxEmpty⟩, txValid⟩, rxUsed⟩
  have txChunks : trace.txQueued = [] := by
    apply List.length_eq_zero_iff.mp
    simpa [txEmpty] using related.txQueue.length
  have rxChunks : trace.rxQueued = [] := by
    apply List.length_eq_zero_iff.mp
    simpa [rxEmpty] using related.rxQueue.length
  constructor
  · simpa [txChunks, State.pendingTx, txValid] using related.txOrder
  · simpa [rxChunks, State.pendingRx, rxUsed] using related.rxOrder

end Pinwheel.Program.StreamingReady
