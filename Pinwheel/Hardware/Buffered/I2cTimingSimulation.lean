import Pinwheel.Hardware.Buffered.I2cTimingLoading
import Pinwheel.Hardware.Buffered.GenericSessionReuse

/-! Initialized packed-SRAM execution and repeated reuse for every duration
and wait-budget value of the four-byte I²C source. -/
namespace Pinwheel.Hardware.Buffered.I2cTiming
open Pinwheel.Hardware Pinwheel.Program Refinement

theorem initialized_run (duration budget : Fin 256) (s : SramState.State)
    (cold : Values Reactive.Input) (coldInit : cold .initialize = 1)
    (loading : List (Values Reactive.Input))
    (history : Loading.SourceHistory duration budget (s.step cold) loading)
    (valid : (SramLoading.run (s.step cold) SramLoading.Ledger.initial loading).1.registers (.core .valid) = 1)
    (start : Values Reactive.Input)
    (starting : Reactive.starting.eval start
      (SramLoading.run (s.step cold) SramLoading.Ledger.initial loading).1.core = 1)
    (incoming : Nat → BitVec 2) (edges : Nat) :
    let after := SramLoading.run (s.step cold) SramLoading.Ledger.initial loading
    RelatedSram (source duration budget) (layout duration budget) (start .txData)
      ((after.1.step start).run (SpiStart.clocks incoming edges))
      (Program.Buffered.run (source duration budget) capacity
        (GenericStart.started (source duration budget) after.1.core start) incoming edges) :=
  ((Loading.initialized_installed duration budget s cold coldInit loading history valid).start start starting).run
    incoming edges

theorem initialized_reuse (duration budget : Fin 256) (s : SramState.State)
    (cold : Values Reactive.Input) (coldInit : cold .initialize = 1)
    (loading : List (Values Reactive.Input))
    (history : Loading.SourceHistory duration budget (s.step cold) loading)
    (valid : (SramLoading.run (s.step cold) SramLoading.Ledger.initial loading).1.registers (.core .valid) = 1)
    (rounds : List GenericSession.Round)
    (admitted : GenericSession.AdmittedTrace
      (SramLoading.run (s.step cold) SramLoading.Ledger.initial loading).1 rounds) :
    let after := (SramLoading.run (s.step cold) SramLoading.Ledger.initial loading).1
    GenericSession.Results (source duration budget) (layout duration budget) after rounds ∧
      InstalledSram (source duration budget) (layout duration budget) (GenericSession.run after rounds) ∧
      (GenericSession.run after rounds).core .generation = after.core .generation ∧
      ((GenericSession.run after rounds).core .transfer).toNat = (after.core .transfer).toNat + rounds.length ∧
      (after.core .transfer).toNat + rounds.length ≤ 65535 := by
  have installed := Loading.initialized_installed duration budget s cold coldInit loading history valid
  have trace := GenericSession.trace_result admitted installed
  exact ⟨trace.1, trace.2.1, trace.2.2.1, trace.2.2.2, GenericSession.trace_bound admitted installed⟩

end Pinwheel.Hardware.Buffered.I2cTiming
