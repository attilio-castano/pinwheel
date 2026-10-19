import Pinwheel.Hardware.Buffered.I2cLoading

/-! Canonical I²C residency and actual candidate-response readiness, derived
from initialized accepted loading. -/
namespace Pinwheel.Hardware.Buffered.I2cLoading
open Pinwheel.Hardware

theorem source_resident (s : SramState.State) (t : SramLoading.Ledger)
    (h : Known t) (he : SramCorrespondence.Established s t)
    (hv : s.registers (.core .valid) = 1) :
    SramExecution.Resident s I2cSource.rows I2cSource.dictionary := by
  rcases he.resident hv with ⟨metadata, dictionary, arrays, start⟩
  exact ⟨fun k hk => (metadata k hk).trans
      (congrArg (BitVec.extractLsb' 64 28) (known_live_row s t h he hv k hk)),
    fun k => (dictionary k).trans (congrFun (known_dictionary s t h he hv) k),
    fun port k hk => (arrays port k hk).trans
      (congrArg (BitVec.extractLsb' 0 64) (known_live_row s t h he hv k hk)),
    fun hk => (start hk).trans
      (congrArg (BitVec.extractLsb' 0 64) (known_live_row s t h he hv 0 hk))⟩

theorem source_ready (s : SramState.State) (t : SramLoading.Ledger)
    (h : Known t) (he : SramCorrespondence.Established s t)
    (hv : s.registers (.core .valid) = 1)
    (ready : SramExecution.Ready s t.rows) :
    SramExecution.Ready s I2cSource.rows := by
  intro port
  by_cases hk : SramExecution.live (s.registers (.core .count))
      (SramExecution.candidateAddresses s.registers port) = true
  · simpa only [SramCandidates.project, hk, if_true,
      known_live_row s t h he hv _ hk] using ready port
  · simp only [SramCandidates.project, hk, Bool.false_eq_true, if_false]
  done

theorem initialized_source_resident (s : SramState.State)
    (i : Values Reactive.Input) (hi : i .initialize = 1)
    (loading : List (Values Reactive.Input)) (hs : SourceHistory (s.step i) loading)
    (hv : (SramLoading.run (s.step i) SramLoading.Ledger.initial loading).1.registers (.core .valid) = 1) :
    let after := SramLoading.run (s.step i) SramLoading.Ledger.initial loading
    SramExecution.Resident after.1 I2cSource.rows I2cSource.dictionary :=
  source_resident _ _ (known_run (s.step i) SramLoading.Ledger.initial loading known_initial hs)
    (SramCorrespondence.initialized_established s i hi loading) hv

theorem initialized_source_ready (s : SramState.State)
    (i : Values Reactive.Input) (hi : i .initialize = 1)
    (loading : List (Values Reactive.Input)) (hs : SourceHistory (s.step i) loading)
    (hv : (SramLoading.run (s.step i) SramLoading.Ledger.initial loading).1.registers (.core .valid) = 1) :
    let after := SramLoading.run (s.step i) SramLoading.Ledger.initial loading
    SramExecution.Ready after.1 I2cSource.rows :=
  source_ready _ _ (known_run (s.step i) SramLoading.Ledger.initial loading known_initial hs)
    (SramCorrespondence.initialized_established s i hi loading) hv
    (SramCorrespondence.initialized_ready s i hi loading hv)

end Pinwheel.Hardware.Buffered.I2cLoading
