import Pinwheel.Hardware.Buffered.I2cStart
import Pinwheel.Hardware.Buffered.GenericSimulation

/-! Every command-zero execution prefix of the initialized fixed I²C image
refines its Buffered source, including digital SRAM residency/readiness,
sampler timing, partial transfer prefixes, and retained fault outcomes. -/
namespace Pinwheel.Hardware.Buffered.I2cSimulation
open Pinwheel.Hardware Pinwheel.Program

theorem initialized_run (s : SramState.State)
    (cold : Values Reactive.Input) (coldInit : cold .initialize = 1)
    (loading : List (Values Reactive.Input))
    (source : I2cLoading.SourceHistory (s.step cold) loading)
    (valid : (SramLoading.run (s.step cold) SramLoading.Ledger.initial loading).1.registers
      (.core .valid) = 1)
    (start : Values Reactive.Input)
    (starting : Reactive.starting.eval start
      (SramExecution.core (SramLoading.run (s.step cold) SramLoading.Ledger.initial loading).1.registers) = 1)
    (incoming : Nat → BitVec 2) (edges : Nat) :
    let after := SramLoading.run (s.step cold) SramLoading.Ledger.initial loading
    Refinement.RelatedSram I2cSource.source I2cCertificate.layout (start .txData)
      ((after.1.step start).run (SpiStart.clocks incoming edges))
      (Program.Buffered.run I2cSource.source Refinement.capacity
        (GenericStart.started I2cSource.source (SramExecution.core after.1.registers) start)
        incoming edges) := by
  let after := SramLoading.run (s.step cold) SramLoading.Ledger.initial loading
  have initial := I2cStart.initialized_start s cold coldInit loading source valid start starting
  obtain ⟨rows, dictionary, resident, ready, related⟩ := initial
  have runtime := SpiStart.clocks_executing incoming edges
  have invariants := SramExecution.runtime_invariants (after.1.step start)
    (SpiStart.clocks incoming edges) rows dictionary resident ready runtime
  refine ⟨rows, dictionary, invariants.1, invariants.2, ?_⟩
  rw [SramExecution.runtime_run (after.1.step start) (SpiStart.clocks incoming edges)
    rows dictionary resident ready runtime]
  exact Refinement.related_run related incoming edges

end Pinwheel.Hardware.Buffered.I2cSimulation
