import Pinwheel.Hardware.StreamingReady.Core
import Pinwheel.Hardware.StreamingReady.TxQueue

/-! Connect the existing Ready core's TX registers and controls to the
depth-two queue model. -/
namespace Pinwheel.Hardware.StreamingReady.TxShiftCore

open Pinwheel.Hardware

abbrev Chunk := BitVec 32 × BitVec 6

def asRing (s : Values (Core.Register 1)) : TxQueue.Ring Chunk :=
  ⟨s .txHead, s .txTail, s .txCount, fun index => (s (.txWord index), s (.txBits index))⟩

def RingInvariant (s : Values (Core.Register 1)) : Prop := (asRing s).WellFormed

def clears (i : Values Core.Input) (s : Values (Core.Register 1)) : Bool :=
  decide (Core.clearedRuntime.eval i s = 1)

def pushes (i : Values Core.Input) (s : Values (Core.Register 1)) : Bool :=
  decide (Core.pushing.eval i s = 1)

def pops (i : Values Core.Input) (s : Values (Core.Register 1)) : Bool :=
  decide (Core.loadingTX.eval i s = 1)

def incoming (i : Values Core.Input) : Chunk := (i .txData, i .txBits)

private theorem band_value : ∀ x y : BitVec 1, x &&& y = 1 ↔ x = 1 ∧ y = 1 := by
  decide +kernel

private theorem either_value : ∀ x y : BitVec 1, ~~~(~~~x &&& ~~~y) = 1 ↔ x = 1 ∨ y = 1 := by
  decide +kernel

private theorem inv_value : ∀ x : BitVec 1, ~~~x = 1 ↔ x ≠ 1 := by
  decide +kernel

private theorem ofBool_value (x : Bool) : BitVec.ofBool x = 1 ↔ x = true := by
  cases x <;> decide +kernel

private theorem both_one (i : Values Core.Input) (s : Values (Core.Register 1)) (x y : Core.E 1 1) :
    (Core.both x y).eval i s = 1 ↔ x.eval i s = 1 ∧ y.eval i s = 1 :=
  band_value _ _

private theorem either_one (i : Values Core.Input) (s : Values (Core.Register 1)) (x y : Core.E 1 1) :
    (Core.either x y).eval i s = 1 ↔ x.eval i s = 1 ∨ y.eval i s = 1 :=
  either_value _ _

private theorem clear_value (i : Values Core.Input) (s : Values (Core.Register 1))
    (empty live : α) :
    (if (Core.either Core.resetting Core.releasing).eval i s = 1 then empty
      else if Core.starting.eval i s = 1 then empty else live) =
    if clears i s then empty else live := by
  simp only [clears, Core.clearedRuntime, decide_eq_true_eq, either_one]
  by_cases hr : Core.resetting.eval i s = 1#1 <;> by_cases hl : Core.releasing.eval i s = 1#1 <;>
    by_cases hs : Core.starting.eval i s = 1#1 <;> simp [hr, hl, hs]

private theorem increment_pointer : ∀ x : BitVec 1, x - 1#1 = x + 1#1 := by
  decide +kernel

private theorem increment_count : ∀ x : BitVec 4, x - 15#4 = x + 1#4 := by
  decide +kernel

private theorem write_slot (i : Values Core.Input) (s : Values (Core.Register 1)) (index : BitVec 1) :
    (Core.both Core.pushing (.equal (.reg .txTail) (.lit index))).eval i s = 1 ↔
    (pushes i s && index == s .txTail) = true := by
  simp only [both_one, Expr.eval, ofBool_value, pushes, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
  exact and_congr_right (fun _ => ⟨fun h => (of_decide_eq_true h).symm,
    fun h => decide_eq_true h.symm⟩)

private theorem ring_ext (q r : TxQueue.Ring α) (head : q.head = r.head) (tail : q.tail = r.tail)
    (count : q.count = r.count) (slot : q.slot = r.slot) : q = r := by
  cases q
  cases r
  simp_all

theorem ring_step (i : Values Core.Input) (s : Values (Core.Register 1)) :
    asRing ((Core.circuit 1).step i s) =
      (asRing s).step (clears i s) (pushes i s) (pops i s) (incoming i) (0#32, 32#6) := by
  apply ring_ext
  · simp only [asRing, Core.circuit, Circuit.step, Core.next, Core.nextRaw, Expr.eval]
    rw [clear_value]
    cases clears i s
    · simp [TxQueue.Ring.step, pops, Core.inc, Expr.eval, increment_pointer]
    · rfl
  · simp only [asRing, Core.circuit, Circuit.step, Core.next, Core.nextRaw, Expr.eval]
    rw [clear_value]
    cases clears i s
    · simp [TxQueue.Ring.step, pushes, Core.inc, Expr.eval, increment_pointer]
    · rfl
  · simp only [asRing, Core.circuit, Circuit.step, Core.next, Core.nextRaw, Expr.eval]
    rw [clear_value]
    cases clears i s
    · simp [TxQueue.Ring.step, TxQueue.stepCount, pushes, pops, Core.queueCount,
        Core.inc, Expr.eval, increment_count]
    · rfl
  · funext index
    cases hc : clears i s
    · have noClear : Core.clearedRuntime.eval i s ≠ 1 := of_decide_eq_false hc
      simp only [asRing, Core.circuit, Circuit.step, Core.next, Core.nextRaw, Expr.eval,
        TxQueue.Ring.step, noClear, Bool.false_eq_true, ↓reduceIte, write_slot, incoming]
      split <;> rename_i h <;> simp [h]
    · have clear : Core.clearedRuntime.eval i s = 1 := of_decide_eq_true hc
      simp [asRing, Core.circuit, Circuit.step, Core.next, Expr.eval, TxQueue.Ring.step, clear]

theorem controls_legal (i : Values Core.Input) (s : Values (Core.Register 1)) :
    (asRing s).Legal (pushes i s) (pops i s) := by
  constructor
  · intro admitted
    have push : Core.pushing.eval i s = 1 := of_decide_eq_true admitted
    simp only [Core.pushing, both_one] at push
    have room := push.2.2.1
    simpa [Core.txRoom, Core.depth, Expr.eval, ofBool_value, BitVec.lt_def, asRing] using room
  · intro admitted
    have pop : Core.loadingTX.eval i s = 1 := of_decide_eq_true admitted
    simp only [Core.loadingTX, Core.takingTX, Core.reserving, Core.credit, Core.txAvailable,
      both_one, either_one, Expr.eval, inv_value, ofBool_value] at pop
    change s .txCount ≠ 0
    have hasQueue := (pop.1.1.2.2.1.resolve_left (fun noTx => noTx pop.1.2)).resolve_left
      (fun shiftHasData => shiftHasData ((ofBool_value _).mpr pop.2))
    exact fun empty => hasQueue ((ofBool_value _).mpr (decide_eq_true empty))

theorem invariant_step (i : Values Core.Input) (s : Values (Core.Register 1))
    (h : RingInvariant s) : RingInvariant ((Core.circuit 1).step i s) := by
  unfold RingInvariant
  rw [ring_step]
  exact (asRing s).wellFormed_step _ _ _ _ _ h (controls_legal i s)

theorem full_pop_blocks_push (i : Values Core.Input) (s : Values (Core.Register 1))
    (full : s .txCount = 2) (pop : pops i s = true) : pushes i s = false := by
  have legal := controls_legal i s
  rw [pop] at legal
  exact (asRing s).full_pop_blocks_push _ full legal

theorem cold_resets (i : Values Core.Input) (s : Values (Core.Register 1))
    (cold : i .initialize = 1) : Core.resetting.eval i s = 1 :=
  (either_one _ _ _ _).mpr (Or.inl cold)

theorem cold_clears (i : Values Core.Input) (s : Values (Core.Register 1))
    (cold : i .initialize = 1) : clears i s = true :=
  decide_eq_true ((either_one _ _ _ _).mpr (Or.inl (cold_resets i s cold)))

theorem cold_invariant (i : Values Core.Input) (s : Values (Core.Register 1))
    (cold : i .initialize = 1) : RingInvariant ((Core.circuit 1).step i s) := by
  unfold RingInvariant
  rw [ring_step, cold_clears i s cold]
  exact (asRing s).wellFormed_clear _ _ _ _

end Pinwheel.Hardware.StreamingReady.TxShiftCore
