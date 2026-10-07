import Pinwheel.Hardware.Buffered.Reactive

/-! Local safety properties of the actual circuit equations. Admission/image
correctness and complete software-to-hardware trace refinement remain separate
gates; these lemmas do not assume those claims. -/
namespace Pinwheel.Hardware.Buffered.Reactive
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
    (circuit.step i s) .phase = 0 := by
  simp [Circuit.step, circuit, next, clearOwner, either, Expr.eval, h]

theorem dense_snapshot_index :
    (registers.mapIdx fun k ⟨_,r⟩ => decide (registerIndex r = k)).all id = true := by
  decide +kernel


theorem pack_selected_bit (n : Nat) (f : Fin n → E 1) (i : Values Input)
    (s : Values Register) (k : Fin n) :
    ((pack f).eval i s).getLsbD k.val = ((f k).eval i s).getLsbD 0 := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    cases n with
    | zero => exact Fin.elim0 k
    | succ n =>
      cases n with
      | zero => have hk : k = 0 := Fin.ext (by omega); subst k; rfl
      | succ n =>
        cases k using Fin.cases with
        | zero => simp only [pack, Expr.eval, Fin.val_zero, BitVec.getLsbD_append]; rfl
        | succ k =>
          have hnot : ¬ (k.val+1 < 1) := by omega
          simpa only [pack, Expr.eval, BitVec.getLsbD_append, Fin.val_succ,
            hnot, if_false, Nat.add_sub_cancel] using
            ih (n+1) (by omega) (fun j => f j.succ) k
          done

theorem capture_bit_at (bits : E 6) (old : E 16) (i : Values Input)
    (s : Values Register) (k : Fin 16) :
    ((captureBits bits old).eval i s).getLsbD k.val =
      ((.mux (both (.slice 0 1 (by decide) bits)
          (.equal (.slice 2 4 (by decide) bits) (.lit (BitVec.ofNat 4 k.val))))
        (inputBit (.slice 1 1 (by decide) bits))
        (.slice k.val 1 (by omega) old) : E 1).eval i s).getLsbD 0 := by
  exact pack_selected_bit 16 _ i s k

theorem one_and1 (x : BitVec 1) : 1 &&& x = x := by
  exact BitVec.allOnes_and

theorem terminal_capture_forwarding (i : Values Input) (s : Values Register) :
    branchBit.eval i s =
      (Execution.readTree 4 (fun k => .slice k.toNat 1 (by omega) exitScratch) branchSample).eval i s := by
  simp only [branchBit, Execution.readTree_correct, Expr.eval]
  apply (BitVec.eq_of_getLsbD_eq_iff).2
  intro j hj
  have hz : j = 0 := by omega
  subst j
  simp only [BitVec.getLsbD_extractLsb', Nat.add_zero]
  by_cases ht : terminalEdge.eval i s = 1
  · have hc := capture_bit_at (.reg .cachedTerminal) (.reg .scratch) i s
      ⟨(branchSample.eval i s).toNat, (branchSample.eval i s).isLt⟩
    simp only [exitScratch, both, Expr.eval, ht, one_and1, if_true]
    simp only [both, inputBit, Expr.eval, BitVec.ofNat_toNat] at hc
    simp only [inputBit, Expr.eval, BitVec.setWidth_eq] at hc ⊢
    rw [hc]
    simp
    rfl
    done
  · have hz := (BitVec.eq_zero_or_eq_one (terminalEdge.eval i s)).resolve_right ht
    simp [exitScratch, both, Expr.eval, hz]
    done

theorem wait_ready_dispatches (i : Values Input) (s : Values Register)
    (hp : s .phase = 2) (hr : waitReady.eval i s = 1) :
    dispatch.eval i s = 1 ∧ heldTimeout.eval i s = 0 := by
  simp [dispatch, heldTimeout, isPhase, both, either, Expr.eval, hp, hr]

theorem checked_failure_has_no_terminal_capture (i : Values Input) (s : Values Register)
    (hp : s .phase = 3) (hr : checkedReady.eval i s = 0) :
    heldFault.eval i s = 1 ∧ terminalEdge.eval i s = 0 ∧ dispatch.eval i s = 0 := by
  simp [heldFault, terminalEdge, dispatch, isPhase, both, either, Expr.eval, hp, hr]

theorem wait_exhaustion_times_out (i : Values Input) (s : Values Register)
    (hp : s .phase = 2) (hr : waitReady.eval i s = 0) (hn : s .remaining = 0) :
    heldTimeout.eval i s = 1 ∧ dispatch.eval i s = 0 := by
  simp [heldTimeout, dispatch, terminalEdge, isPhase, both, either, Expr.eval, hp, hr, hn]

theorem qualifier_blockage_restarts_interval (i : Values Input) (s : Values Register)
    (hc : clearOwner.eval i s = 0) (ht : stopping.eval i s = 0)
    (he : entering.eval i s = 0) (hp : s .phase = 4) (hr : checkedReady.eval i s = 0) :
    (circuit.step i s) .remaining = s .cachedDuration ∧
    (circuit.step i s) .waitLeft = s .waitLeft - 1 := by
  simp [Circuit.step, circuit, next, busy, isPhase, either, both, Expr.eval, hc, ht, he, hp, hr]

theorem qualifier_progress_replenishes_budget (i : Values Input) (s : Values Register)
    (hc : clearOwner.eval i s = 0) (ht : stopping.eval i s = 0)
    (he : entering.eval i s = 0) (hp : s .phase = 4) (hr : checkedReady.eval i s = 1) :
    (circuit.step i s) .remaining = s .remaining - 1 ∧
    (circuit.step i s) .waitLeft = s .cachedBudget := by
  simp [Circuit.step, circuit, next, busy, isPhase, either, both, Expr.eval, hc, ht, he, hp, hr]

theorem malformed_entry_does_not_capture (i : Values Input) (s : Values Register)
    (hl : legalEntry.eval i s = 0) (hs : starting.eval i s = 0) :
    entryScratch.eval i s = exitScratch.eval i s := by
  simp [entryScratch, runEntry, both, Expr.eval, hl, hs]

theorem stop_canonicalizes_location (i : Values Input) (s : Values Register)
    (ht : stopping.eval i s = 1) :
    (circuit.step i s) .pc = 0 ∧ (circuit.step i s) .virtualPC = 0 ∧
    (circuit.step i s) .outer = 0 ∧ (circuit.step i s) .inner = 0 := by
  simp [Circuit.step, circuit, next, either, Expr.eval, ht]

theorem dispatch_enters_same_edge (i : Values Input) (s : Values Register)
    (hr : resetting.eval i s = 0) (hd : dispatch.eval i s = 1) :
    entering.eval i s = 1 := by
  simp [entering, both, either, Expr.eval, hr, hd]

theorem absolute_endpoint_restores_location (i : Values Input) (s : Values Register)
    (ha : absoluteDispatch.eval i s = 1) :
    entryPC.eval i s = (endpoint.eval i s).extractLsb' 11 7 ∧
    entryOuter.eval i s = (endpoint.eval i s).extractLsb' 18 3 ∧
    entryInner.eval i s = (endpoint.eval i s).extractLsb' 21 3 := by
  simp [entryPC, entryOuter, entryInner, Expr.eval, ha]

theorem physical_increment_no_wrap (x : BitVec 7) (h : x.toNat < 64) :
    (x - 127).toNat = x.toNat + 1 := by
  simp [BitVec.toNat_sub]
  omega
  done

theorem virtual_increment_no_wrap (x : BitVec 10) :
    (((0#1) ++ x) - (2047 : BitVec 11)).toNat = x.toNat + 1 := by
  simp only [BitVec.toNat_sub]
  simp only [BitVec.toNat_append]
  simp
  have hx := x.isLt
  omega
  done

end Pinwheel.Hardware.Buffered.Reactive
