import Pinwheel.Hardware.Buffered.I2cReload
import Pinwheel.Hardware.Buffered.LifecycleUpload

/-! Reset and accepted upload batches reinstall the source image without
assuming cleared SRAM. The loader trace cannot hide a START or another reset.
Actual accepted COMMIT edges determine the finite generation increment. -/
namespace Pinwheel.Hardware.Buffered.I2cReloadSession
open Pinwheel.Hardware

theorem loading_run (s : SramState.State) (ledger : SramLoading.Ledger)
    (inputs : List (Values Reactive.Input)) :
    (SramLoading.run s ledger inputs).1 = s.run inputs := by
  induction inputs generalizing s ledger
  case nil => rfl
  case cons i rest ih => exact ih (s.step i) (ledger.step s i)

structure Batch where
  reset : Values Reactive.Input
  loading : List (Values Reactive.Input)

def Batch.after (batch : Batch) (s : SramState.State) : SramState.State :=
  (s.step batch.reset).run batch.loading

def Batch.inputs (batch : Batch) : List (Values Reactive.Input) :=
  @batch.reset :: batch.loading

theorem Batch.after_eq_run (batch : Batch) (s : SramState.State) :
    batch.after s = s.run batch.inputs := rfl

structure Admitted (s : SramState.State) (batch : Batch) : Prop where
  reset : batch.reset .initialize = 1 ∨
    (batch.reset .initialize = 0 ∧ batch.reset .command = 7)
  loader : ∀ i ∈ batch.loading, LifecycleUpload.Input i
  source : I2cLoading.SourceHistory (s.step batch.reset) batch.loading
  valid : (batch.after s).registers (.core .valid) = 1

theorem Admitted.resetting {s : SramState.State} {batch : Batch}
    (h : Admitted s batch) : Reactive.resetting.eval batch.reset s.core = 1 := by
  rcases h.reset with cold | ⟨cold, warm⟩
  · simp [Reactive.resetting, Reactive.cold, Reactive.either, Expr.eval, cold]
  · simp [Reactive.resetting, Reactive.cold, Reactive.warm, Reactive.both,
      Reactive.either, Reactive.cmd, Expr.eval, cold, warm]

theorem Admitted.installed {s : SramState.State} {batch : Batch}
    (h : Admitted s batch) :
    Refinement.InstalledSram I2cSource.source I2cCertificate.layout (batch.after s) := by
  have installed := I2cReload.reset_installed s batch.reset h.resetting batch.loading h.source
  rw [loading_run] at installed
  exact installed h.valid

theorem Admitted.idle {s : SramState.State} {batch : Batch}
    (h : Admitted s batch) :
    (batch.after s).core .phase = 0 ∧ (batch.after s).core .retained = 0 := by
  have reset := Lifecycle.reset_ownership s batch.reset h.resetting
  have loaded := LifecycleUpload.run (s.step batch.reset) batch.loading h.loader reset.2.2 reset.2.1
  exact ⟨loaded.1, loaded.2.1⟩

theorem Admitted.transfer {s : SramState.State} {batch : Batch}
    (h : Admitted s batch) :
    (batch.after s).core .transfer =
      if batch.reset .initialize = 1#1 then 0 else s.core .transfer := by
  have reset := Lifecycle.reset_ownership s batch.reset h.resetting
  have loaded := LifecycleUpload.run (s.step batch.reset) batch.loading h.loader reset.2.2 reset.2.1
  change ((s.step batch.reset).run batch.loading).core .transfer = _
  rw [loaded.2.2.1]
  rcases h.reset with cold | ⟨cold, warm⟩
  · rw [(Lifecycle.cold_counters s batch.reset cold).2]
    simp [cold]
  · rw [Lifecycle.warm_transfer s batch.reset cold warm]
    simp [cold]

theorem Admitted.generation {s : SramState.State} {batch : Batch}
    (h : Admitted s batch) :
    ((batch.after s).core .generation).toNat =
      (if batch.reset .initialize = 1#1 then 0 else min 65535 ((s.core .generation).toNat + 1)) +
        LifecycleUpload.commitCount (s.step batch.reset) batch.loading := by
  have reset := Lifecycle.reset_ownership s batch.reset h.resetting
  have loaded := LifecycleUpload.run (s.step batch.reset) batch.loading h.loader reset.2.2 reset.2.1
  change (((s.step batch.reset).run batch.loading).core .generation).toNat = _
  rw [loaded.2.2.2]
  rcases h.reset with cold | ⟨cold, warm⟩
  · rw [(Lifecycle.cold_counters s batch.reset cold).1]
    simp [cold]
  · rw [Lifecycle.warm_generation s batch.reset cold warm]
    simp [cold]

structure Result (s : SramState.State) (batch : Batch) : Prop where
  installed : Refinement.InstalledSram I2cSource.source I2cCertificate.layout (batch.after s)
  phase : (batch.after s).core .phase = 0
  retained : (batch.after s).core .retained = 0
  transfer : (batch.after s).core .transfer =
    if batch.reset .initialize = 1#1 then 0 else s.core .transfer
  generation : ((batch.after s).core .generation).toNat =
    (if batch.reset .initialize = 1#1 then 0 else min 65535 ((s.core .generation).toNat + 1)) +
      LifecycleUpload.commitCount (s.step batch.reset) batch.loading

theorem result {s : SramState.State} {batch : Batch} (h : Admitted s batch) : Result s batch :=
  ⟨h.installed, h.idle.1, h.idle.2, h.transfer, h.generation⟩

end Pinwheel.Hardware.Buffered.I2cReloadSession
