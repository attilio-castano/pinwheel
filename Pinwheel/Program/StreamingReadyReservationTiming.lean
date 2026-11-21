import Pinwheel.Program.StreamingReadyControl
import Pinwheel.Program.StreamingSafety

/-! Fixed reservation cuts are checked in the state immediately before their
edges. Each slot carries the actual inputs through the next cut, so callers
choose the cadence. An elastic protocol can instead let the cell park when
credit is unavailable, using the same reservation step. -/
namespace Pinwheel.Program.StreamingReady.ReservationTiming

structure Slot where
  reserve : Input
  rest : List Input

def Slot.inputs (slot : Slot) : List Input := slot.reserve :: slot.rest

def Slot.ready (slot : Slot) (s : State a) : Bool :=
  decide (slot.reserve.initialize = false ∧ slot.reserve.command ≠ 15#4 ∧ s.phase = .boundary) &&
    s.current.isStream && s.canReserve

theorem Slot.ready_sound (slot : Slot) (s : State a) (ready : slot.ready s = true) :
    slot.reserve.Runtime ∧ s.phase = .boundary ∧ s.current.isStream = true ∧
      s.canReserve = true := by
  simpa [Slot.ready, Streaming.Input.Runtime, Bool.and_eq_true, and_assoc] using ready

/-- The index of the first mandatory reservation with an unmet pre-edge
obligation. Host actions on its reservation edge are absent from the check. -/
def firstMiss (p : Program) (s : State a) : List Slot → Option Nat
  | [] => none
  | slot :: rest =>
    if slot.ready s then (firstMiss p (run p s slot.inputs) rest).map Nat.succ else some 0

def OnTime (p : Program) (s : State a) : List Slot → Prop
  | [] => True
  | slot :: rest => slot.ready s = true ∧ OnTime p (run p s slot.inputs) rest

theorem firstMiss_none (p : Program) (s : State a) (slots : List Slot) :
    firstMiss p s slots = none ↔ OnTime p s slots := by
  induction slots generalizing s with
  | nil => simp [firstMiss, OnTime]
  | cons slot rest ih =>
    cases ready : slot.ready s <;> simp [firstMiss, OnTime, ready, ih]

theorem firstMiss_some (p : Program) (s : State a) (slots : List Slot) (index : Nat)
    (miss : firstMiss p s slots = some index) :
    ∃ prior slot suffix, slots = prior ++ slot :: suffix ∧ prior.length = index ∧
      OnTime p s prior ∧ slot.ready (run p s (prior.flatMap Slot.inputs)) = false := by
  induction slots generalizing s index with
  | nil => simp [firstMiss] at miss
  | cons slot rest ih =>
    cases ready : slot.ready s with
    | false =>
      have zero : index = 0 := by simpa [firstMiss, ready, eq_comm] using miss
      exact ⟨[], slot, rest, rfl, zero.symm, trivial, ready⟩
    | true =>
      cases tailMiss : firstMiss p (run p s slot.inputs) rest with
      | none => simp [firstMiss, ready, tailMiss] at miss
      | some j =>
        have next : j.succ = index := by simpa [firstMiss, ready, tailMiss] using miss
        obtain ⟨prior, failed, suffix, tail, size, before, bad⟩ := ih _ _ tailMiss
        refine ⟨slot :: prior, failed, suffix, ?_, ?_, ⟨ready, before⟩, ?_⟩
        · simp [tail]
        · simpa only [List.length_cons, size] using next
        · simpa [run, List.foldl_append] using bad

theorem reserve_edge (p : Program) (s : State a) (slot : Slot) (ready : slot.ready s = true) :
    (step p slot.reserve s).phase = .low ∧
      (step p slot.reserve s).txConsumed =
        s.txConsumed + (if s.current.cell.transmit then 1 else 0) := by
  obtain ⟨runtime, boundary, stream, credit⟩ := slot.ready_sound s ready
  rw [step_busy_eq_clock p s slot.reserve runtime (by simp [boundary, Phase.busy])]
  simp [clock, engine, boundary, stream, credit]

/-- Without pre-edge credit an ordinary edge holds the boundary pins and
leaves consumption unchanged. The host can still perform queue actions. -/
theorem park_edge (p : Program) (s : State a) (i : Input) (runtime : i.Runtime)
    (boundary : s.phase = .boundary) (noCredit : s.canReserve = false) :
    (step p i s).phase = .boundary ∧ (step p i s).pins = s.pins ∧
      (step p i s).txConsumed = s.txConsumed := by
  rw [step_busy_eq_clock p s i runtime (by simp [boundary, Phase.busy])]
  simp [clock, engine, boundary, noCredit]

/-- A push on a missed reservation edge becomes queue credit in the state at
the next cut. That push cannot make the engine reserve on the current edge. -/
theorem push_on_missed_edge (p : Program) (s : State a) (i : Input) (runtime : i.Runtime)
    (boundary : s.phase = .boundary) (noCredit : s.canReserve = false)
    (accepted : s.tx.willPush (s.hostPush i) = true) :
    (step p i s).phase = .boundary ∧ (step p i s).txConsumed = s.txConsumed ∧
      (step p i s).tx.readable = true ∧
      (step p i s).txAccepted = s.txAccepted +
        BitVec.ofNat 16 ((s.hostPush i).getD {}).validBits := by
  obtain ⟨phase, _, consumed⟩ := park_edge p s i runtime boundary noCredit
  refine ⟨phase, consumed, ?_, ?_⟩
  · rw [step_busy_eq_clock p s i runtime (by simp [boundary, Phase.busy])]
    have noPop : s.enginePop = false := by simp [State.enginePop, noCredit]
    change (s.tx.tick (s.hostPush i) s.enginePop).readable = true
    rw [noPop]
    have count := Streaming.Queue.tick_count s.tx (s.hostPush i) false
    simp [accepted, Streaming.Queue.willPop] at count
    simp only [Streaming.Queue.readable, bne_iff_ne]
    omega
  · rw [step_busy_eq_clock p s i runtime (by simp [boundary, Phase.busy])]
    simp [clock, accepted]

end Pinwheel.Program.StreamingReady.ReservationTiming
