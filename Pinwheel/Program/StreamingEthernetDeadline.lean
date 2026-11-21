import Pinwheel.Program.StreamingEthernetCoreFrame
import Pinwheel.Program.StreamingReadyCounting

/-! Fixed-rate Ethernet service can be proved from word availability at
burst deadlines and a PHY's own clock, without a trace of observed credits. -/
namespace Pinwheel.Program.StreamingEthernetDeadline
open StreamingReady StreamingEthernetCore

/-- A runtime edge between START and the retained terminal edge. -/
def Ordinary (i : Input) : Prop := i.initialize = false ∧ i.command = 0#4

theorem Ordinary.runtime {i : Input} (ordinary : Ordinary i) : i.Runtime :=
  ⟨ordinary.1, by rw [ordinary.2]; decide⟩

theorem Ordinary.step {i : Input} (ordinary : Ordinary i) (s : State a) :
    step program i s = clock program i s := by
  simp [StreamingReady.step, ordinary.1, ordinary.2]

/-- The PHY samples on clock two of a six-clock cell. Its sampled high
interval may be one or two clocks, independently in every cell. -/
def phyLevel (width : Nat → Fin 2) (edge : Nat) : Bool :=
  decide (2 ≤ edge % 6 ∧ edge % 6 < 3 + (width (edge / 6)).val)

def PhyClock (width : Nat → Fin 2) (cells : List CellInputs) : Prop :=
  ∀ (k : Fin cells.length) (tick : Fin 6),
    (cells[k.val].inputs[tick.val]?.getD {}).rawInputs[0] = phyLevel width (6 * k.val + tick.val)

/-- Credit becomes visible in the pre-edge state of a reservation. A
host can certify a refill earlier, using its accepted words and the same
runtime input tape that feeds the core. -/
def BurstService (s : State a) (cells : List CellInputs) : Prop :=
  ∀ burst : Nat, 64 * burst < cells.length →
    ∃ visible : Nat, visible ≤ 6 * (64 * burst) ∧
      min cells.length (64 * (burst + 1)) ≤
        (run program s ((blocks cells).take visible)).txAccepted.toNat

theorem can_reserve (s : State a) (trace : BitTrace)
    (row : s.current = streamRow) (order : trace.Related s) (counts : trace.NaturalCounts s)
    (available : s.txConsumed.toNat < s.txAccepted.toNat) : s.canReserve = true := by
  by_cases valid : s.txValid = 0#6
  · by_cases empty : s.tx.count.val = 0
    · have noQueue : trace.txQueued = [] := List.length_eq_zero_iff.mp (order.txQueue.length.trans empty)
      have same := congrArg List.length order.txOrder
      simp [noQueue, State.pendingTx, valid, counts.accepted, counts.consumed] at same
      omega
    · simp [State.canReserve, State.txReady, State.rxReady, row, streamRow, txCell,
        Instruction.isStream, Instruction.cell, Streaming.Queue.readable, empty]
  · simp [State.canReserve, State.txReady, State.rxReady, row, streamRow, txCell,
      Instruction.isStream, Instruction.cell, valid]

private theorem accepted_ordinary (s : State a) (i : Input) (ordinary : Ordinary i) :
    s.txAccepted.toNat ≤ (step program i s).txAccepted.toNat := by
  rw [ordinary.step s]
  cases offered : s.hostPush i with
  | none => simp [clock, offered, Streaming.Queue.willPush, engine_tx_fields]
  | some chunk =>
    by_cases accept : s.tx.willPush (some chunk) = true
    · have bound := hostPush_bound s i chunk offered
      have total := s.total.isLt
      simp [clock, offered, accept, engine_tx_fields, BitVec.toNat_add, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (show chunk.validBits < 65536 by omega),
        Nat.mod_eq_of_lt (show s.txAccepted.toNat + chunk.validBits < 65536 by omega)]
    · simp [clock, offered, accept, engine_tx_fields]

private theorem accepted_run (s : State a) (inputs : List Input) (ordinary : ∀ i ∈ inputs, Ordinary i) :
    s.txAccepted.toNat ≤ (run program s inputs).txAccepted.toNat := by
  induction inputs generalizing s with
  | nil => exact Nat.le_refl _
  | cons i tail ih =>
    exact Nat.le_trans (accepted_ordinary s i (ordinary i List.mem_cons_self))
      (ih (step program i s) (fun j member => ordinary j (List.mem_cons_of_mem _ member)))

private theorem credit_from_bursts (s : State a) (cells : List CellInputs)
    (ordinary : ∀ i ∈ blocks cells, Ordinary i) (service : BurstService s cells) :
    ∀ k < cells.length, k < (run program s ((blocks cells).take (6 * k))).txAccepted.toNat := by
  intro k inside
  let burst := k / 64
  have before : 64 * burst ≤ k := by dsimp [burst]; omega
  have covered : k < 64 * (burst + 1) := by dsimp [burst]; omega
  obtain ⟨visible, early, accepted⟩ := service burst (Nat.lt_of_le_of_lt before inside)
  let trace := (blocks cells).take (6 * k)
  have take : trace.take visible = (blocks cells).take visible := by
    rw [List.take_take, Nat.min_eq_left (show visible ≤ 6 * k by omega)]
  have monotone := accepted_run (run program s (trace.take visible)) (trace.drop visible)
    (fun i mem => ordinary i (List.mem_of_mem_take (List.mem_of_mem_drop mem)))
  have joined : run program (run program s (trace.take visible)) (trace.drop visible) = run program s trace := by
    simp only [run, ← List.foldl_append, List.take_append_drop]
  rw [joined, take] at monotone
  change k < (run program s trace).txAccepted.toNat
  omega

theorem timed_cells (width : Nat → Fin 2) (cells : List CellInputs)
    (ordinary : ∀ i ∈ blocks cells, Ordinary i) (phy : PhyClock width cells) :
    ∀ cell ∈ cells, cell.Timed := by
  intro cell member
  obtain ⟨k, inside, rfl⟩ := List.mem_iff_getElem.mp member
  have level (tick : Fin 6) : phyLevel width (6 * k + tick.val) =
      decide (2 ≤ tick.val ∧ tick.val < 3 + (width k).val) := by
    have residue : (6 * k + tick.val) % 6 = tick.val := by have h := tick.isLt; omega
    have quotient : (6 * k + tick.val) / 6 = k := by have h := tick.isLt; omega
    simp [phyLevel, residue, quotient]
  refine ⟨fun i hit => (ordinary i (List.mem_flatMap.mpr ⟨cells[k], member, hit⟩)).runtime, ?_, ?_, ?_⟩
  · have h := phy ⟨k, inside⟩ 0
    rw [level] at h
    simpa [CellInputs.inputs] using h
  · have h := phy ⟨k, inside⟩ 1
    rw [level] at h
    simpa [CellInputs.inputs] using h
  · have h := phy ⟨k, inside⟩ 2
    rw [level] at h
    simpa [CellInputs.inputs, show 2 < 3 + (width k).val by omega] using h

private theorem scheduled (s : State a) (cells : List CellInputs) (trace : BitTrace)
    (boundary : Boundary s cells.length) (related : trace.Related s)
    (counts : trace.NaturalCounts s) (structural : s.Structural) (progress : s.Progress)
    (timed : ∀ cell ∈ cells, cell.Timed)
    (credit : ∀ k < cells.length,
      s.txConsumed.toNat + k < (run program s ((blocks cells).take (6 * k))).txAccepted.toNat) :
    ReadySchedule s cells := by
  induction cells generalizing s trace with
  | nil => trivial
  | cons cell tail ih =>
    have enough := can_reserve s trace boundary.row related counts (by simpa [run] using credit 0 (by simp))
    have timing := timed cell List.mem_cons_self
    refine ⟨timing, enough, ?_⟩
    cases tail with
    | nil => trivial
    | cons first rest =>
      let next := run program s cell.inputs
      let seen := traceRun program s trace cell.inputs
      have advancing := cell_exact s _ cell trace boundary enough timing
      have remains : 1 < (cell :: first :: rest).length := by simp
      have nextBoundary : Boundary next (first :: rest).length := by
        have continued := advancing.1
        rw [if_pos remains] at continued
        simpa only [List.length_cons, Nat.add_sub_cancel] using continued
      have newCounts := traceRun_natural program s trace cell.inputs counts related structural progress
      have consumed : next.txConsumed.toNat = s.txConsumed.toNat + 1 := by
        rw [← newCounts.consumed, advancing.2.2, List.length_append, counts.consumed]
        rfl
      refine ih next seen nextBoundary (traceRun_related program s trace cell.inputs related structural)
        newCounts (run_structural program s cell.inputs structural) (run_progress program s cell.inputs progress)
        (fun c present => timed c (List.mem_cons_of_mem _ present)) ?_
      intro k inside
      have more : k + 1 < (cell :: first :: rest).length := by simp; omega
      have used := credit (k + 1) more
      have inputs : (blocks (cell :: first :: rest)).take (6 * (k + 1)) =
          cell.inputs ++ (blocks (first :: rest)).take (6 * k) := by
        rw [show blocks (cell :: first :: rest) = cell.inputs ++ blocks (first :: rest) from rfl,
          List.take_append]
        have size : cell.inputs.length = 6 := rfl
        rw [List.take_of_length_le (show cell.inputs.length ≤ 6 * (k + 1) by omega),
          show 6 * (k + 1) - cell.inputs.length = 6 * k by omega]
      rw [inputs] at used
      change next.txConsumed.toNat + k < _
      rw [consumed]
      simpa only [run, List.foldl_append, next, Nat.add_assoc, Nat.add_comm 1 k] using used

theorem frame_from_schedule (s : State a) (cells : List CellInputs) (finish : Input)
    (trace : BitTrace) (bits : List Bool)
    (boundary : Boundary s cells.length) (related : trace.Related s)
    (counts : trace.NaturalCounts s) (structural : s.Structural)
    (initial : s.txConsumed = 0#16) (size : bits.length = cells.length)
    (ready : ReadySchedule s cells) (terminal : finish.Runtime)
    (payload : (traceRun program s trace (blocks cells ++ [finish])).accepted = bits) :
    let inputs := blocks cells ++ [finish]
    (run program s inputs).phase = .completed ∧
      pinTrace program s inputs = bits.flatMap cellPins ++ [txPins false, idlePins] ∧
      (traceRun program s trace inputs).consumed = bits := by
  obtain ⟨ended, sent, sentSize, wire, tx⟩ := frame_exact s cells finish trace boundary ready terminal
  have empty : trace.consumed = [] := by simpa [initial] using counts.consumed
  rw [empty, List.nil_append] at tx
  let final := traceRun program s trace (blocks cells ++ [finish])
  have finalOrder := (traceRun_related program s trace (blocks cells ++ [finish]) related structural).txOrder
  change final.accepted = final.consumed ++ _ ++ _ at finalOrder
  have sentPrefix : sent <+: bits := ⟨_, by simpa [payload, tx, final, List.append_assoc] using finalOrder.symm⟩
  have sentEq := sentPrefix.eq_of_length (sentSize.trans size.symm)
  exact ⟨ended, sentEq ▸ wire, tx.trans sentEq⟩

/-- Independent PHY timing and bounded host burst service suffice for the
whole Ethernet frame. The accepted payload is the host contract; Lean
recovers the same bits in reservation order and at all PHY sample edges. -/
theorem frame_from_bursts (s : State a) (cells : List CellInputs) (finish : Input)
    (trace : BitTrace) (bits : List Bool) (width : Nat → Fin 2)
    (boundary : Boundary s cells.length) (related : trace.Related s)
    (counts : trace.NaturalCounts s) (structural : s.Structural) (progress : s.Progress)
    (initial : s.txConsumed = 0#16) (size : bits.length = cells.length)
    (ordinary : ∀ i ∈ blocks cells, Ordinary i) (terminal : finish.Runtime)
    (phy : PhyClock width cells) (service : BurstService s cells)
    (payload : (traceRun program s trace (blocks cells ++ [finish])).accepted = bits) :
    let inputs := blocks cells ++ [finish]
    (run program s inputs).phase = .completed ∧
      pinTrace program s inputs = bits.flatMap cellPins ++ [txPins false, idlePins] ∧
      (traceRun program s trace inputs).consumed = bits := by
  have hasCredit := credit_from_bursts s cells ordinary service
  exact frame_from_schedule s cells finish trace bits boundary related counts structural initial size
    (scheduled s cells trace boundary related counts structural progress
      (timed_cells width cells ordinary phy) (by simpa [initial] using hasCredit)) terminal payload

end Pinwheel.Program.StreamingEthernetDeadline
