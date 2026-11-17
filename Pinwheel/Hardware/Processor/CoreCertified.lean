import Pinwheel.Hardware.Processor.CoreCircuitOutputs

/-! Whole-controller cycle refinement. Valid raw states may retain arbitrary
inactive instruction/trap metadata. Reset recovers every raw register image,
including reserved phase 7, to the fixed architectural initial state.

These theorems cover the core's 37 registers and 30 output ports. Instruction
provider truth, deferred response ownership/reset cancellation, and RAM/MMIO
effects are separate composition obligations. Artifact transport additionally
requires an explicit correspondence certificate for the actual imported RTL.
-/
namespace Pinwheel.Hardware.Processor.CoreCircuit

open CoreInterface

/-- Exact physical step and complete observation correspondence. -/
def implementation : DecodedImplementation circuit CoreInterface.spec where
  Valid := Valid
  view := view
  preserved := preserved
  step_eq := step_eq
  output_eq i raw h {_} o := output_eq i raw h o

/-- No pre-reset validity premise: synchronous reset clears all physical core
registers. External memories and providers have their own reset obligations. -/
theorem reset_recovery (i : Values Input) (raw : Values Register) (h : i reset = 1) :
    Valid (circuit.step i raw) ∧ view (circuit.step i raw) = CoreModel.initial := by
  rw [reset_values i raw h]
  exact ⟨zero_valid, zero_view⟩

def resetCertificate : implementation.Reset reset where
  initial _ := CoreModel.initial
  reset_valid i raw h := (reset_recovery i raw h).1
  reset_view i raw h := (reset_recovery i raw h).2

/-- Coverage is not limited to states reachable from a particular program or
zero register image. Every valid logical controller state has a physical image. -/
theorem initial_coverage (state : CoreModel.State) (h : CoreModel.Valid state) :
    ∃ raw : Values Register, Valid raw ∧ view raw = state :=
  ⟨encode state, valid_encode state h, view_encode state h⟩

theorem trace_eq (raw : Values Register) (h : Valid raw) (traffic : List (Values Input)) :
    circuit.component.trace raw traffic = CoreInterface.spec.trace (view raw) traffic :=
  implementation.trace_eq raw h traffic

theorem run_eq (raw : Values Register) (h : Valid raw) (traffic : List (Values Input)) :
    view (circuit.component.run raw traffic) = CoreInterface.spec.run (view raw) traffic :=
  implementation.run_eq raw h traffic

theorem run_valid (raw : Values Register) (h : Valid raw) (traffic : List (Values Input)) :
    Valid (circuit.component.run raw traffic) :=
  implementation.run_valid raw h traffic

theorem encoded_trace (state : CoreModel.State) (h : CoreModel.Valid state)
    (traffic : List (Values Input)) :
    circuit.component.trace (encode state) traffic = CoreInterface.spec.trace state traffic := by
  rw [trace_eq _ (valid_encode state h), view_encode state h]

theorem encoded_run (state : CoreModel.State) (h : CoreModel.Valid state)
    (traffic : List (Values Input)) :
    view (circuit.component.run (encode state) traffic) = CoreInterface.spec.run state traffic := by
  rw [run_eq _ (valid_encode state h), view_encode state h]

theorem trace_after_reset (i : Values Input) (raw : Values Register) (h : i reset = 1)
    (traffic : List (Values Input)) :
    circuit.component.trace (circuit.step i raw) traffic = CoreInterface.spec.trace CoreModel.initial traffic :=
  resetCertificate.trace_after_reset implementation reset i raw h traffic

theorem run_after_reset (i : Values Input) (raw : Values Register) (h : i reset = 1)
    (traffic : List (Values Input)) :
    view (circuit.component.run (circuit.step i raw) traffic) = CoreInterface.spec.run CoreModel.initial traffic :=
  resetCertificate.run_after_reset implementation reset i raw h traffic

variable {rtl : Timed.Component (Values Input) (Values Register) (Values Output)}

/-- A supplied correspondence must cover the actual artifact's complete typed
state and output interface; this module does not manufacture that certificate. -/
theorem artifact_trace_eq (artifact : Artifact.Correspondence circuit rtl)
    (raw : Values Register) (h : Valid raw) (traffic : List (Values Input)) :
    rtl.trace raw traffic = CoreInterface.spec.trace (view raw) traffic :=
  implementation.artifact_trace_eq artifact raw h traffic

theorem artifact_run_eq (artifact : Artifact.Correspondence circuit rtl)
    (raw : Values Register) (h : Valid raw) (traffic : List (Values Input)) :
    view (rtl.run raw traffic) = CoreInterface.spec.run (view raw) traffic :=
  implementation.artifact_run_eq artifact raw h traffic

theorem artifact_trace_after_reset (artifact : Artifact.Correspondence circuit rtl)
    (i : Values Input) (raw : Values Register) (h : i reset = 1) (traffic : List (Values Input)) :
    rtl.trace (rtl.step i raw) traffic = CoreInterface.spec.trace CoreModel.initial traffic :=
  resetCertificate.artifact_trace_after_reset implementation reset artifact i raw h traffic

theorem artifact_run_after_reset (artifact : Artifact.Correspondence circuit rtl)
    (i : Values Input) (raw : Values Register) (h : i reset = 1) (traffic : List (Values Input)) :
    view (rtl.run (rtl.step i raw) traffic) = CoreInterface.spec.run CoreModel.initial traffic :=
  resetCertificate.artifact_run_after_reset implementation reset artifact i raw h traffic

end Pinwheel.Hardware.Processor.CoreCircuit
