import Pinwheel.Hardware.Buffered.I2cUploadCommit

/-! The canonical I²C upload is admitted from arbitrary pre-reset hardware.
VALID, coverage, resident storage and candidate availability are conclusions.
Warm reset preserves the transfer counter and requires room for reset+COMMIT. -/
namespace Pinwheel.Hardware.Buffered.I2cCanonicalUpload
open Pinwheel.Hardware
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

def written (s : SramState.State) : SramState.State := rowRun (tableRun s 16) 50

theorem written_eq (s : SramState.State) : written s = s.run (tables ++ rows) := by
  unfold written tables rows
  rw [rowRun_eq, tableRun_eq]
  rfl
  done

theorem loading_eq (s : SramState.State) : s.run loading = (written s).step commitInput := by
  rw [written_eq]
  simp [loading, SramState.State.run, List.foldl_append]
  done

structure Written (s : SramState.State) : Prop where
  phase : (written s).core .phase = 0
  retained : (written s).core .retained = 0
  pending : (written s).core .pending = 1
  covered : ∀ k : Fin 64, k.val < 50 → ((written s).core .written).getLsbD k.val = true
  dictionary : (written s).registers .branchWritten = 65535
  generation : (written s).core .generation = s.core .generation

theorem written_ready (s : SramState.State)
    (phase : s.core .phase = 0) (retained : s.core .retained = 0) : Written s := by
  have table := tables_run s 16 phase retained
  have row := rows_run (tableRun s 16) 50 table.phase table.retained
    (table.pending (by decide)) (fun k => table.covered k k.isLt)
  exact ⟨row.phase, row.retained, row.pending, row.covered,
    dictionary_full _ row.dictionary, row.generation.trans table.generation⟩
  done

theorem table_prefix_accepted (s : SramState.State)
    (phase : s.core .phase = 0) (retained : s.core .retained = 0) (n : Nat) :
    Sram.tableWriting.eval ((tableRun s n).inputs (tableInput (BitVec.ofNat 4 n)))
      (tableRun s n).registers = 1 :=
  (table_writing _ _ (tables_run s n phase retained).phase (tables_run s n phase retained).retained).2

theorem row_prefix_accepted (s : SramState.State)
    (phase : s.core .phase = 0) (retained : s.core .retained = 0) (n : Nat) :
    Sram.rowWriting.eval ((rowRun (tableRun s 16) n).inputs (rowInput (BitVec.ofNat 6 n)))
      (rowRun (tableRun s 16) n).registers = 1 := by
  have table := tables_run s 16 phase retained
  have row := rows_run (tableRun s 16) n table.phase table.retained
    (table.pending (by decide)) (fun k => table.covered k k.isLt)
  exact (row_writing _ _ row.phase row.retained).2
  done

theorem loading_accepted (s : SramState.State)
    (phase : s.core .phase = 0) (retained : s.core .retained = 0)
    (space : s.core .generation ≠ 65535) :
    Sram.committing.eval ((written s).inputs commitInput) (written s).registers = 1 := by
  have ready := written_ready s phase retained
  apply commit_accepted _ ready.phase ready.retained ready.pending _ ready.covered ready.dictionary
  rw [ready.generation]
  exact space
  done

theorem loading_valid (s : SramState.State)
    (phase : s.core .phase = 0) (retained : s.core .retained = 0)
    (space : s.core .generation ≠ 65535) : (s.run loading).core .valid = 1 := by
  rw [loading_eq]
  exact commit_valid _ (loading_accepted s phase retained space)
  done

theorem loading_generation (s : SramState.State)
    (phase : s.core .phase = 0) (retained : s.core .retained = 0)
    (space : s.core .generation ≠ 65535) :
    ((s.run loading).core .generation).toNat = (s.core .generation).toNat + 1 := by
  rw [loading_eq, Lifecycle.commit_generation_sequence _ _ (loading_accepted s phase retained space),
    (written_ready s phase retained).generation]
  done

def batch (reset : Values Reactive.Input) : I2cReloadSession.Batch := ⟨reset, loading⟩

theorem cold_admitted (s : SramState.State) (reset : Values Reactive.Input)
    (cold : reset .initialize = 1) : I2cReloadSession.Admitted s (batch reset) := by
  have resetting : Reactive.resetting.eval reset s.core = 1 := by
    simp [Reactive.resetting, Reactive.cold, Reactive.either, Expr.eval, cold]
  have cleared := Lifecycle.reset_ownership s reset resetting
  have generation := (Lifecycle.cold_counters s reset cold).1
  refine ⟨Or.inl cold, loader_inputs, source_history _, ?_⟩
  exact loading_valid (s.step reset) cleared.2.2 cleared.2.1 (by simp [generation])
  done

theorem warm_space (s : SramState.State) (reset : Values Reactive.Input)
    (cold : reset .initialize = 0) (warm : reset .command = 7)
    (space : (s.core .generation).toNat ≤ 65533) : (s.step reset).core .generation ≠ 65535 := by
  have generation := Lifecycle.warm_generation s reset cold warm
  intro exhausted
  rw [exhausted] at generation
  change 65535 = min 65535 ((s.core .generation).toNat + 1) at generation
  omega
  done

theorem warm_admitted (s : SramState.State) (reset : Values Reactive.Input)
    (cold : reset .initialize = 0) (warm : reset .command = 7)
    (space : (s.core .generation).toNat ≤ 65533) : I2cReloadSession.Admitted s (batch reset) := by
  have resetting : Reactive.resetting.eval reset s.core = 1 := by
    simp [Reactive.resetting, Reactive.cold, Reactive.warm, Reactive.both,
      Reactive.either, Reactive.cmd, Expr.eval, cold, warm]
  have cleared := Lifecycle.reset_ownership s reset resetting
  refine ⟨Or.inr ⟨cold, warm⟩, loader_inputs, source_history _, ?_⟩
  exact loading_valid (s.step reset) cleared.2.2 cleared.2.1 (warm_space s reset cold warm space)
  done

theorem cold_result (s : SramState.State) (reset : Values Reactive.Input)
    (cold : reset .initialize = 1) : I2cReloadSession.Result s (batch reset) :=
  I2cReloadSession.result (cold_admitted s reset cold)

theorem warm_result (s : SramState.State) (reset : Values Reactive.Input)
    (cold : reset .initialize = 0) (warm : reset .command = 7)
    (space : (s.core .generation).toNat ≤ 65533) : I2cReloadSession.Result s (batch reset) :=
  I2cReloadSession.result (warm_admitted s reset cold warm space)

theorem cold_generation (s : SramState.State) (reset : Values Reactive.Input)
    (cold : reset .initialize = 1) :
    (((batch reset).after s).core .generation).toNat = 1 := by
  have admitted := cold_admitted s reset cold
  have cleared := Lifecycle.reset_ownership s reset admitted.resetting
  have generation := (Lifecycle.cold_counters s reset cold).1
  have result := loading_generation (s.step reset) cleared.2.2 cleared.2.1 (by simp [generation])
  rw [generation] at result
  exact result.trans (by decide)
  done

theorem warm_generation (s : SramState.State) (reset : Values Reactive.Input)
    (cold : reset .initialize = 0) (warm : reset .command = 7)
    (space : (s.core .generation).toNat ≤ 65533) :
    (((batch reset).after s).core .generation).toNat = (s.core .generation).toNat + 2 := by
  have admitted := warm_admitted s reset cold warm space
  have cleared := Lifecycle.reset_ownership s reset admitted.resetting
  have result := loading_generation (s.step reset) cleared.2.2 cleared.2.1 (warm_space s reset cold warm space)
  rw [Lifecycle.warm_generation s reset cold warm] at result
  change (((s.step reset).run loading).core .generation).toNat = _
  omega
  done

theorem written_invalid (s : SramState.State)
    (phase : s.core .phase = 0) (retained : s.core .retained = 0) :
    (written s).core .valid = 0 := by
  have table := tables_run s 16 phase retained
  have row := rows_run (tableRun s 16) 49 table.phase table.retained
    (table.pending (by decide)) (fun k => table.covered k k.isLt)
  have writing := (row_writing (rowRun (tableRun s 16) 49) (BitVec.ofNat 6 49) row.phase row.retained).1
  change Sram.circuit.step ((rowRun (tableRun s 16) 49).inputs (rowInput (BitVec.ofNat 6 49)))
    (rowRun (tableRun s 16) 49).registers (.core .valid) = 0
  rw [SramCoverage.valid_step]
  simp [writing]
  done

theorem loading_exhausted (s : SramState.State)
    (phase : s.core .phase = 0) (retained : s.core .retained = 0)
    (full : s.core .generation = 65535) :
    Sram.committing.eval ((written s).inputs commitInput) (written s).registers = 0 ∧
      (s.run loading).core .valid = 0 := by
  have fullWritten : (written s).core .generation = 65535 := (written_ready s phase retained).generation.trans full
  have blocked : Sram.committing.eval ((written s).inputs commitInput) (written s).registers = 0 := by
    rw [Lifecycle.committing_effective]
    exact Reactive.exhausted_generation_rejects_commit _ _ fullWritten
  refine ⟨blocked, ?_⟩
  rw [loading_eq]
  change Sram.circuit.step ((written s).inputs commitInput) (written s).registers (.core .valid) = 0
  rw [SramCoverage.valid_step]
  have invalid := written_invalid s phase retained
  change (written s).registers (.core .valid) = 0#1 at invalid
  simp [blocked, invalid]
  done

theorem warm_exhausted (s : SramState.State) (reset : Values Reactive.Input)
    (cold : reset .initialize = 0) (warm : reset .command = 7)
    (full : 65534 ≤ (s.core .generation).toNat) :
    ((batch reset).after s).core .valid = 0 := by
  have resetFull : (s.step reset).core .generation = 65535 := by
    apply BitVec.eq_of_toNat_eq
    rw [Lifecycle.warm_generation s reset cold warm]
    change min 65535 ((s.core .generation).toNat + 1) = 65535
    omega
  have resetting : Reactive.resetting.eval reset s.core = 1 := by
    simp [Reactive.resetting, Reactive.cold, Reactive.warm, Reactive.both,
      Reactive.either, Reactive.cmd, Expr.eval, cold, warm]
  have cleared := Lifecycle.reset_ownership s reset resetting
  exact (loading_exhausted (s.step reset) cleared.2.2 cleared.2.1 resetFull).2
  done

end Pinwheel.Hardware.Buffered.I2cCanonicalUpload
