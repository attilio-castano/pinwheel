import Pinwheel.Hardware.Buffered.Linear

/-! Local safety properties of the actual circuit equations. Admission/image
correctness and complete software-to-hardware trace refinement remain separate
gates; these lemmas do not assume those claims. -/
namespace Pinwheel.Hardware.Buffered.Linear
open Pinwheel.Hardware

theorem cold_clears_ownership (i : Values Input) (s : Values Register)
    (h : i .initialize = 1) :
    (circuit.step i s) .valid = 0 ∧ (circuit.step i s) .retained = 0 ∧
    (circuit.step i s) .generation = 0 ∧ (circuit.step i s) .transfer = 0 := by
  simp [Circuit.step, circuit, next, clearOwner, resetting, cold, either, Expr.eval, h]

theorem sampler_pre_edge (i : Values Input) (s : Values Register)
    (h : resetting.eval i s = 0) :
    (circuit.step i s) .stage1 = i .rawInputs ∧
    (circuit.step i s) .stage2 = s .stage1 := by
  simp [Circuit.step, circuit, next, Expr.eval, h]

theorem warm_keeps_transfer_counter (i : Values Input) (s : Values Register)
    (hc : cold.eval i s = 0) (hs : starting.eval i s = 0) :
    (circuit.step i s) .transfer = s .transfer := by
  simp [Circuit.step, circuit, next, Expr.eval, hc, hs]

theorem generation_saturates (i : Values Input) (s : Values Register)
    (hc : cold.eval i s = 0) (hn : committing.eval i s = 0)
    (h : s .generation = 65535) : (circuit.step i s) .generation = 65535 := by
  simp [Circuit.step, circuit, next, increment, space, either, both, Expr.eval, hc, hn, h]

theorem transfer_saturates (i : Values Input) (s : Values Register)
    (hc : cold.eval i s = 0) (hn : starting.eval i s = 0)
    (h : s .transfer = 65535) : (circuit.step i s) .transfer = 65535 := by
  simp [Circuit.step, circuit, next, Expr.eval, hc, hn, h]

theorem increment16_no_wrap (x : BitVec 16) (h : x ≠ 65535) :
    (x - 65535).toNat = x.toNat + 1 := by
  have hnat : x.toNat ≠ 65535 := fun he => h (BitVec.eq_of_toNat_eq he)
  simp [BitVec.toNat_sub]
  have hx := x.isLt
  omega
  done

theorem increment6_bounded (x limit : BitVec 6)
    (hx : x.toNat < limit.toNat) (hl : limit.toNat ≤ 32) :
    (x - 63).toNat ≤ 32 := by
  simp [BitVec.toNat_sub]
  omega
  done

theorem tx_counter_held (i : Values Input) (s : Values Register)
    (ho : clearOwner.eval i s = 0) (hc : consuming.eval i s = 0)
    (hs : starting.eval i s = 0) :
    (circuit.step i s) .txConsumed = s .txConsumed := by
  simp [Circuit.step, circuit, next, Expr.eval, ho, hc, hs]

theorem rx_prefix_held (i : Values Input) (s : Values Register)
    (ho : clearOwner.eval i s = 0) (ha : appending.eval i s = 0)
    (hs : starting.eval i s = 0) :
    (circuit.step i s) .rxData = s .rxData ∧
    (circuit.step i s) .rxLength = s .rxLength := by
  simp [Circuit.step, circuit, next, Expr.eval, ho, ha, hs]

theorem tx_entry_advances_once (i : Values Input) (s : Values Register)
    (ho : clearOwner.eval i s = 0) (hc : consuming.eval i s = 1) :
    (circuit.step i s) .txConsumed = entryConsumed.eval i s - 63 := by
  simp [Circuit.step, circuit, next, increment, Expr.eval, ho, hc]

theorem rx_entry_advances_once (i : Values Input) (s : Values Register)
    (ho : clearOwner.eval i s = 0) (ha : appending.eval i s = 1) :
    (circuit.step i s) .rxLength = entryRxLength.eval i s - 63 := by
  simp [Circuit.step, circuit, next, increment, Expr.eval, ho, ha]

theorem consumed_bit_is_pre_edge (i : Values Input) (s : Values Register)
    (ho : clearOwner.eval i s = 0) (hc : consuming.eval i s = 1) :
    (circuit.step i s) .txData =
      (0#1) ++ (entryTx.eval i s).extractLsb' 1 31 := by
  simp [Circuit.step, circuit, next, Expr.eval, ho, hc]

theorem entry_failure_restores_idle (i : Values Input) (s : Values Register)
    (hc : cold.eval i s = 0) (hm : committing.eval i s = 0)
    (ho : clearOwner.eval i s = 0) (hf : stopping.eval i s = 1) :
    (circuit.step i s) .levels = s .idleLevels ∧
    (circuit.step i s) .enabled = s .idleEnabled := by
  simp [Circuit.step, circuit, next, either, Expr.eval, hc, hm, ho, hf]

theorem result_retained (i : Values Input) (s : Values Register)
    (ho : clearOwner.eval i s = 0) (hr : s .retained = 1) :
    (circuit.step i s) .retained = 1 := by
  simp [Circuit.step, circuit, next, Expr.eval, ho, hr]

theorem consuming_has_room (i : Values Input) (s : Values Register)
    (hc : consuming.eval i s = 1) :
    (entryConsumed.eval i s).toNat < (entryTxLength.eval i s).toNat := by
  by_cases hr : (entryConsumed.eval i s).toNat < (entryTxLength.eval i s).toNat
  · exact hr
  · simp only [consuming, both, underflow, Expr.eval, hr, decide_false, BitVec.ofBool_false] at hc
    simp [← BitVec.and_assoc] at hc
    simp only [show (1#1) = BitVec.allOnes 1 from rfl, BitVec.and_allOnes, BitVec.and_not_self] at hc
    exact False.elim ((by decide : (0 : BitVec 1) ≠ BitVec.allOnes 1) hc)
    done

theorem appending_has_room (i : Values Input) (s : Values Register)
    (ha : appending.eval i s = 1) :
    (entryRxLength.eval i s).toNat < (entryCapacity.eval i s).toNat := by
  by_cases hr : (entryRxLength.eval i s).toNat < (entryCapacity.eval i s).toNat
  · exact hr
  · simp only [appending, both, overflow, Expr.eval, hr, decide_false, BitVec.ofBool_false] at ha
    simp [← BitVec.and_assoc] at ha
    simp only [show (1#1) = BitVec.allOnes 1 from rfl, BitVec.and_allOnes, BitVec.and_not_self] at ha
    exact False.elim ((by decide : (0 : BitVec 1) ≠ BitVec.allOnes 1) ha)
    done

theorem tx_capacity_bound (i : Values Input) (s : Values Register)
    (ho : clearOwner.eval i s = 0) (hc : consuming.eval i s = 1)
    (hl : (entryTxLength.eval i s).toNat ≤ 32) :
    ((circuit.step i s) .txConsumed).toNat ≤ 32 := by
  rw [tx_entry_advances_once i s ho hc]
  exact increment6_bounded _ _ (consuming_has_room i s hc) hl
  done

theorem rx_capacity_bound (i : Values Input) (s : Values Register)
    (ho : clearOwner.eval i s = 0) (ha : appending.eval i s = 1)
    (hl : (entryCapacity.eval i s).toNat ≤ 32) :
    ((circuit.step i s) .rxLength).toNat ≤ 32 := by
  rw [rx_entry_advances_once i s ho ha]
  exact increment6_bounded _ _ (appending_has_room i s ha) hl
  done

theorem effects_only_on_entry (i : Values Input) (s : Values Register)
    (he : entering.eval i s = 0) :
    consuming.eval i s = 0 ∧ appending.eval i s = 0 := by
  simp [consuming, appending, runEntry, both, Expr.eval, he]

theorem unread_blocks_updates (i : Values Input) (s : Values Register)
    (hr : s .retained = 1) :
    writing.eval i s = 0 ∧ committing.eval i s = 0 ∧ starting.eval i s = 0 := by
  simp [writing, committing, starting, free, both, Expr.eval, hr]

theorem busy_blocks_updates (i : Values Input) (s : Values Register)
    (hb : busy.eval i s = 1) :
    writing.eval i s = 0 ∧ committing.eval i s = 0 ∧ starting.eval i s = 0 := by
  simp [writing, committing, starting, free, both, Expr.eval, hb]

theorem exhausted_transfer_rejects_start (i : Values Input) (s : Values Register)
    (h : s .transfer = 65535) : starting.eval i s = 0 := by
  simp [starting, space, both, Expr.eval, h]

theorem exhausted_generation_rejects_commit (i : Values Input) (s : Values Register)
    (h : s .generation = 65535) : committing.eval i s = 0 := by
  simp [committing, space, both, Expr.eval, h]

theorem stale_generation_cannot_release (i : Values Input) (s : Values Register)
    (h : i .expectedGeneration ≠ s .generation) : releasing.eval i s = 0 := by
  simp [releasing, both, Expr.eval, h]

theorem stale_transfer_cannot_release (i : Values Input) (s : Values Register)
    (h : i .expectedTransfer ≠ s .transfer) : releasing.eval i s = 0 := by
  simp [releasing, both, Expr.eval, h]

theorem warm_invalidates_ownership (i : Values Input) (s : Values Register)
    (h : resetting.eval i s = 1) :
    (circuit.step i s) .valid = 0 ∧ (circuit.step i s) .retained = 0 ∧
    (circuit.step i s) .mode = 0 := by
  simp [Circuit.step, circuit, next, clearOwner, either, Expr.eval, h]

end Pinwheel.Hardware.Buffered.Linear
