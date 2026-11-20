import Pinwheel.Program.StreamingEthernetDeadline
import Pinwheel.Program.StreamingReadyReservation

/-! A host offer envelope for the depth-two Ethernet engine. The schedule
is checked against the wire cadence and its own offers before execution.
The proof derives queue admission and then the exact wire result. -/
namespace Pinwheel.Program.StreamingEthernetPacedHost
open StreamingReady StreamingEthernetCore StreamingEthernetDeadline

/-- Bits requested by the host, in submission order. Each offer must carry
one full word and both owner tags. -/
def offered (i : Input) : List Bool :=
  if i.txPush then Streaming.Packing.txBits i.txData 32 else []

def offers (inputs : List Input) : List Bool := inputs.flatMap offered

def HostClock (generation transfer : BitVec 16) (i : Input) : Prop :=
  Ordinary i ∧ (i.txPush = true →
    i.expectedGeneration = generation ∧ i.expectedTransfer = transfer ∧ i.txBits = 32#6)

/-- At every offer in a cell there must be fewer than two words outstanding
using only the schedule's accepted prefix and the cell's prior reservation
count. A reservation within this cell can only increase the available room. -/
def OfferRoom (reserved : Nat) : Nat → List Input → Prop
  | _, [] => True
  | submitted, edge :: rest =>
    (edge.txPush = true → submitted < reserved + 64) ∧
      OfferRoom reserved (submitted + (offered edge).length) rest

instance (reserved accepted : Nat) (inputs : List Input) : Decidable (OfferRoom reserved accepted inputs) :=
  match inputs with
  | [] => isTrue trivial
  | edge :: rest =>
    haveI := instDecidableOfferRoom reserved (accepted + (offered edge).length) rest
    inferInstanceAs (Decidable ((edge.txPush = true → accepted < reserved + 64) ∧
      OfferRoom reserved (accepted + (offered edge).length) rest))

/-- A static host schedule needs one available bit at each six-clock cell
boundary and must fit each full-word offer into the depth-two FIFO. These
obligations do not refer to the executed core state. -/
def RefillPlan : Nat → Nat → List CellInputs → Prop
  | _, _, [] => True
  | accepted, reserved, cell :: rest =>
    reserved < accepted ∧ OfferRoom reserved accepted cell.inputs ∧
      RefillPlan (accepted + (offers cell.inputs).length) (reserved + 1) rest

instance (accepted reserved : Nat) (cells : List CellInputs) : Decidable (RefillPlan accepted reserved cells) :=
  match cells with
  | [] => isTrue trivial
  | cell :: rest =>
    haveI := instDecidableRefillPlan (accepted + (offers cell.inputs).length) (reserved + 1) rest
    inferInstanceAs (Decidable (reserved < accepted ∧ OfferRoom reserved accepted cell.inputs ∧
      RefillPlan (accepted + (offers cell.inputs).length) (reserved + 1) rest))

structure WordTrace (s : State 1) (trace : BitTrace) : Prop where
  order : trace.Related s
  counts : trace.NaturalCounts s
  structural : s.Structural
  progress : s.Progress
  owned : (s.phase.busy || s.phase.retained) = true
  fullWords : ∀ chunk ∈ trace.txQueued, chunk.validBits = 32

private theorem queue_bits (chunks : List Streaming.Chunk) (full : ∀ chunk ∈ chunks, chunk.validBits = 32) :
    (chunks.flatMap Streaming.Chunk.txBits).length = 32 * chunks.length := by
  induction chunks with
  | nil => rfl
  | cons chunk tail ih =>
    simp [Streaming.Chunk.txBits, full chunk List.mem_cons_self,
      ih (fun word member => full word (List.mem_cons_of_mem _ member)), Nat.mul_succ, Nat.add_comm]

private theorem writable (s : State 1) (trace : BitTrace) (valid : WordTrace s trace)
    (room : trace.accepted.length < s.txConsumed.toNat + 64) : s.tx.writable = true := by
  have size := congrArg List.length valid.order.txOrder
  simp only [List.length_append, valid.counts.consumed,
    queue_bits trace.txQueued valid.fullWords, valid.order.txQueue.length] at size
  change decide (s.tx.count.val < 2) = true
  apply decide_eq_true
  omega

private theorem run_preserves_owner (s : State 1) (inputs : List Input)
    (ordinary : ∀ i ∈ inputs, Ordinary i) :
    let next := run program s inputs
    next.generation = s.generation ∧ next.transfer = s.transfer ∧ next.total = s.total := by
  induction inputs generalizing s with
  | nil => exact ⟨rfl, rfl, rfl⟩
  | cons i tail ih =>
    obtain ⟨gen, owner, total⟩ := ih (step program i s) (fun j member => ordinary j (List.mem_cons_of_mem _ member))
    have fields : (step program i s).generation = s.generation ∧
        (step program i s).transfer = s.transfer ∧ (step program i s).total = s.total := by
      rw [(ordinary i List.mem_cons_self).step]
      exact engine_reservation_fields program s
    exact ⟨gen.trans fields.1, owner.trans fields.2.1, total.trans fields.2.2⟩

private theorem on_clock (s : State 1) (trace : BitTrace) (i : Input)
    (valid : WordTrace s trace) (host : HostClock s.generation s.transfer i)
    (room : i.txPush = true → trace.accepted.length < s.txConsumed.toNat + 64)
    (budget : trace.accepted.length + (offered i).length ≤ s.total.toNat) :
    let next := step program i s
    let seen := trace.step s i
    WordTrace next seen ∧ seen.accepted = trace.accepted ++ offered i ∧
      s.txConsumed.toNat ≤ next.txConsumed.toNat := by
  let next := step program i s
  let seen := trace.step s i
  have owner : (next.phase.busy || next.phase.retained) = true := by
    change (((step program i s).phase).busy || ((step program i s).phase).retained) = true
    rw [host.1.step]
    exact engine_reservation_owned program s valid.owned
  have consumed : s.txConsumed.toNat ≤ next.txConsumed.toNat := by
    change s.txConsumed.toNat ≤ (step program i s).txConsumed.toNat
    rw [host.1.step]
    exact Nat.le.intro (engine_count_nat program s valid.progress).1.symm
  have ghost : seen = trace.clock s i := by
    simp [seen, BitTrace.step, host.1.1, host.1.2]
  have unchanged : ∀ chunk ∈ (if s.tx.willPop s.enginePop then trace.txQueued.drop 1 else trace.txQueued),
      chunk.validBits = 32 := by
    intro word member
    split at member
    · exact valid.fullWords word (List.mem_of_mem_drop member)
    · exact valid.fullWords word member
  have admitted : (∀ chunk ∈ seen.txQueued, chunk.validBits = 32) ∧
      seen.accepted = trace.accepted ++ offered i := by
    cases push : i.txPush with
    | false =>
      have noOffer : s.hostPush i = none := by simp [State.hostPush, push]
      rw [ghost]
      simpa [BitTrace.clock, State.acceptedBits, Streaming.Queue.traceTick,
        Streaming.Queue.willPush, offered, noOffer, push] using unchanged
    | true =>
      obtain ⟨generation, transfer, bits⟩ := host.2 push
      let chunk : Streaming.Chunk := ⟨i.txData, 31⟩
      have fits : s.txAccepted.toNat + 32 ≤ s.total.toNat := by
        simpa [valid.counts.accepted, offered, push] using budget
      have present : s.hostPush i = some chunk := by
        simp [State.hostPush, State.owned, valid.owned, generation, transfer, push, bits, fits, chunk]
      have accepted : s.tx.willPush (s.hostPush i) = true := by
        simp [Streaming.Queue.willPush, present, writable s trace valid (room push)]
      rw [ghost]
      simp only [BitTrace.clock, State.acceptedBits, Streaming.Queue.traceTick, accepted, ↓reduceIte]
      rw [present]
      refine ⟨List.forall_mem_append.mpr ⟨unchanged, ?_⟩, ?_⟩
      · intro word mem
        rcases List.mem_singleton.mp mem with rfl
        rfl
      · simp only [offered, push, ↓reduceIte, Option.getD_some]
        rfl
  exact ⟨⟨valid.order.step program s i trace valid.structural,
    valid.counts.step program s i trace valid.order valid.structural valid.progress,
    step_structural program s i valid.structural, step_progress program s i valid.progress, owner, admitted.1⟩,
    admitted.2, consumed⟩

private theorem apply_offers (s : State 1) (trace : BitTrace) (inputs : List Input)
    (valid : WordTrace s trace) (reserved : Nat) (covered : reserved ≤ s.txConsumed.toNat)
    (host : ∀ i ∈ inputs, HostClock s.generation s.transfer i)
    (room : OfferRoom reserved trace.accepted.length inputs)
    (budget : trace.accepted.length + (offers inputs).length ≤ s.total.toNat) :
    let next := run program s inputs
    let seen := traceRun program s trace inputs
    WordTrace next seen ∧ seen.accepted = trace.accepted ++ offers inputs := by
  induction inputs generalizing s trace with
  | nil => exact ⟨valid, by simp [offers, traceRun]⟩
  | cons i tail ih =>
    have first := host i List.mem_cons_self
    let stepState := step program i s
    let stepTrace := trace.step s i
    have length : (offers (i :: tail)).length = (offered i).length + (offers tail).length := by simp [offers]
    have later := on_clock s trace i valid first (fun push => by have earlier := room.1 push; omega)
      (by omega)
    have fields := run_preserves_owner s [i] (by simpa using first.1)
    have hostTail : ∀ j ∈ tail, HostClock stepState.generation stepState.transfer j := by
      rw [show stepState.generation = s.generation from fields.1,
        show stepState.transfer = s.transfer from fields.2.1]
      exact fun j member => host j (List.mem_cons_of_mem _ member)
    have nextRoom : OfferRoom reserved stepTrace.accepted.length tail := by
      rw [show stepTrace.accepted = _ from later.2.1, List.length_append]
      exact room.2
    have nextBudget : stepTrace.accepted.length + (offers tail).length ≤ stepState.total.toNat := by
      rw [show stepState.total = s.total from fields.2.2, show stepTrace.accepted = _ from later.2.1,
        List.length_append]
      omega
    obtain ⟨validTail, acceptedTail⟩ := ih stepState stepTrace later.1 (Nat.le_trans covered later.2.2)
      hostTail nextRoom nextBudget
    refine ⟨validTail, ?_⟩
    change (traceRun program stepState stepTrace tail).accepted = _
    rw [acceptedTail, show stepTrace.accepted = _ from later.2.1]
    simp [offers, List.append_assoc]

private theorem trace_append (s : State a) (trace : BitTrace) (first rest : List Input) :
    traceRun program s trace (first ++ rest) =
      traceRun program (run program s first) (traceRun program s trace first) rest := by
  induction first generalizing s trace with
  | nil => rfl
  | cons i tail ih => exact ih (step program i s) (trace.step s i)

/-- The static host offer envelope supplies the actual queue reservations.
The engine admits every full-word offer and preserves its order. -/
theorem service (s : State 1) (trace : BitTrace) (cells : List CellInputs)
    (boundary : Boundary s cells.length) (valid : WordTrace s trace)
    (timed : ∀ c ∈ cells, c.Timed)
    (host : ∀ i ∈ blocks cells, HostClock s.generation s.transfer i)
    (plan : RefillPlan trace.accepted.length s.txConsumed.toNat cells)
    (budget : trace.accepted.length + (offers (blocks cells)).length ≤ s.total.toNat) :
    ReadySchedule s cells ∧ (traceRun program s trace (blocks cells)).accepted =
      trace.accepted ++ offers (blocks cells) := by
  induction cells generalizing s trace with
  | nil => exact ⟨trivial, by simp [traceRun, blocks, offers]⟩
  | cons cell tail ih =>
    let stepState := run program s cell.inputs
    let stepTrace := traceRun program s trace cell.inputs
    have split : blocks (cell :: tail) = cell.inputs ++ blocks tail := rfl
    have appendOffers : offers (blocks (cell :: tail)) = offers cell.inputs ++ offers (blocks tail) := by
      simp [split, offers]
    have enough := can_reserve s trace boundary.row valid.order valid.counts
      (by simpa [valid.counts.accepted] using plan.1)
    have timing := timed cell List.mem_cons_self
    have first : ∀ i ∈ cell.inputs, HostClock s.generation s.transfer i := fun i member =>
      host i (split.symm ▸ List.mem_append_left _ member)
    have tailHost : ∀ i ∈ blocks tail, HostClock stepState.generation stepState.transfer i := by
      have fields := run_preserves_owner s cell.inputs (fun i member => (first i member).1)
      rw [show stepState.generation = s.generation from fields.1,
        show stepState.transfer = s.transfer from fields.2.1]
      exact fun i member => host i (split.symm ▸ List.mem_append_right _ member)
    have firstBudget : trace.accepted.length + (offers cell.inputs).length ≤ s.total.toNat := by
      rw [appendOffers, List.length_append] at budget
      omega
    obtain ⟨seen, admitted⟩ := apply_offers s trace cell.inputs valid s.txConsumed.toNat (Nat.le_refl _)
      first plan.2.1 firstBudget
    have stepBudget : stepTrace.accepted.length + (offers (blocks tail)).length ≤ stepState.total.toNat := by
      have fields := run_preserves_owner s cell.inputs (fun i member => (first i member).1)
      rw [show stepTrace.accepted = _ from admitted, List.length_append,
        show stepState.total = _ from fields.2.2]
      rw [appendOffers, List.length_append] at budget
      omega
    rw [split, trace_append]
    cases tail with
    | nil =>
      exact ⟨⟨timing, enough, trivial⟩, by simpa [traceRun, appendOffers, blocks, offers] using admitted⟩
    | cons second rest =>
      have advancing := cell_exact s _ cell trace boundary enough timing
      have remains : 1 < (cell :: second :: rest).length := by simp
      have nextBoundary : Boundary stepState (second :: rest).length := by
        have continued := advancing.1
        rw [if_pos remains] at continued
        simpa only [List.length_cons, Nat.add_sub_cancel] using continued
      have consumed : stepState.txConsumed.toNat = s.txConsumed.toNat + 1 := by
        rw [← seen.counts.consumed, advancing.2.2, List.length_append, valid.counts.consumed]
        rfl
      have nextPlan : RefillPlan stepTrace.accepted.length stepState.txConsumed.toNat (second :: rest) := by
        rw [show stepTrace.accepted = _ from admitted, List.length_append, consumed]
        exact plan.2.2
      obtain ⟨schedule, finished⟩ := ih stepState stepTrace nextBoundary seen
        (fun c present => timed c (List.mem_cons_of_mem _ present)) tailHost nextPlan stepBudget
      refine ⟨⟨timing, enough, schedule⟩, ?_⟩
      rw [finished, admitted]
      simp [offers, List.append_assoc]

/-- Every allowed full-word refill schedule under this independent PHY
clock drives exactly the words supplied by the host. Neither queue credit
nor acceptance of a particular offer is a premise. -/
theorem frame_from_offers (s : State 1) (cells : List CellInputs) (finish : Input)
    (trace : BitTrace) (bits : List Bool) (width : Nat → Fin 2)
    (boundary : Boundary s cells.length) (valid : WordTrace s trace)
    (initial : s.txConsumed = 0#16) (size : bits.length = cells.length)
    (phy : PhyClock width cells)
    (host : ∀ i ∈ blocks cells, HostClock s.generation s.transfer i)
    (plan : RefillPlan trace.accepted.length s.txConsumed.toNat cells)
    (payload : trace.accepted ++ offers (blocks cells) = bits)
    (capacity : bits.length ≤ s.total.toNat) (terminal : Ordinary finish) (noOffer : finish.txPush = false) :
    let inputs := blocks cells ++ [finish]
    (run program s inputs).phase = .completed ∧
      pinTrace program s inputs = bits.flatMap cellPins ++ [txPins false, idlePins] ∧
      (traceRun program s trace inputs).consumed = bits := by
  have budget : trace.accepted.length + (offers (blocks cells)).length ≤ s.total.toNat := by
    rw [← List.length_append, payload]
    exact capacity
  obtain ⟨ready, seen⟩ := service s trace cells boundary valid
    (timed_cells width cells (fun i member => (host i member).1) phy) host plan budget
  apply frame_from_schedule s cells finish trace bits boundary valid.order valid.counts valid.structural
    initial size ready terminal.runtime
  rw [trace_append]
  simp [traceRun, BitTrace.step, BitTrace.clock, State.acceptedBits, State.hostPush, Streaming.Queue.willPush,
    terminal.1, terminal.2, noOffer, seen, payload]

end Pinwheel.Program.StreamingEthernetPacedHost
