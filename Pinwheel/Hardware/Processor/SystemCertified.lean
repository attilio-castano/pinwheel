import Pinwheel.Hardware.Processor.SystemCircuitCoverage

/-! Complete finite-run and explicit artifact transport for the connected
ROM/RAM/MMIO system. All raw reset states recover while retaining RAM words/Q.
Artifact claims remain conditional on correspondence for the actual RTL.
Serial wire timing and loader-mode discipline are separate wrappers. -/
namespace Pinwheel.Hardware.Processor.SystemCircuit

variable (layout : AddressMap.Layout rw aw) (rom : SystemModel.Rom rw)
  (romFits : rw ≤ 30) (ramFits : aw ≤ 30)

/-- The typed 37-port specification has exactly the connected model's state
transition; pin encoding adds no hidden logical state or execution step. -/
theorem spec_run (state : SystemModel.State aw) (traffic : List (Values Input)) :
    (spec layout rom).run state traffic =
      (SystemModel.component layout rom).run state (traffic.map decode) := by
  induction traffic generalizing state with
  | nil => rfl
  | cons i rest ih => exact ih ((spec layout rom).step i state)

theorem trace_eq (raw : Values (Register aw)) (h : Valid layout rom raw) (traffic : List (Values Input)) :
    (circuit layout rom romFits ramFits).component.trace raw traffic = (spec layout rom).trace (view raw) traffic :=
  (implementation layout rom romFits ramFits).trace_eq raw h traffic

theorem run_eq (raw : Values (Register aw)) (h : Valid layout rom raw) (traffic : List (Values Input)) :
    view ((circuit layout rom romFits ramFits).component.run raw traffic) = (spec layout rom).run (view raw) traffic :=
  (implementation layout rom romFits ramFits).run_eq raw h traffic

theorem run_valid (raw : Values (Register aw)) (h : Valid layout rom raw) (traffic : List (Values Input)) :
    Valid layout rom ((circuit layout rom romFits ramFits).component.run raw traffic) :=
  (implementation layout rom romFits ramFits).run_valid raw h traffic

theorem trace_after_reset (i : Values Input) (raw : Values (Register aw)) (h : i reset = 1)
    (traffic : List (Values Input)) :
    (circuit layout rom romFits ramFits).component.trace ((circuit layout rom romFits ramFits).step i raw) traffic = (spec layout rom).trace (resetState raw) traffic :=
  (resetCertificate layout rom romFits ramFits).trace_after_reset (implementation layout rom romFits ramFits) reset i raw h traffic

theorem run_after_reset (i : Values Input) (raw : Values (Register aw)) (h : i reset = 1)
    (traffic : List (Values Input)) :
    view ((circuit layout rom romFits ramFits).component.run ((circuit layout rom romFits ramFits).step i raw) traffic) = (spec layout rom).run (resetState raw) traffic :=
  (resetCertificate layout rom romFits ramFits).run_after_reset (implementation layout rom romFits ramFits) reset i raw h traffic

theorem encoded_trace (state : SystemModel.State aw) (h : SystemModel.Valid layout rom state)
    (ramInactive : Values (Memory.ByteAdapterCircuit.Metadata aw)) (fetchInactive : Values Fetch)
    (traffic : List (Values Input)) :
    (circuit layout rom romFits ramFits).component.trace (encode state ramInactive fetchInactive) traffic =
      (spec layout rom).trace state traffic := by
  rw [trace_eq layout rom romFits ramFits _ (valid_encode layout rom state h ramInactive fetchInactive),
    view_encode state h.core ramInactive fetchInactive]

theorem encoded_run (state : SystemModel.State aw) (h : SystemModel.Valid layout rom state)
    (ramInactive : Values (Memory.ByteAdapterCircuit.Metadata aw)) (fetchInactive : Values Fetch)
    (traffic : List (Values Input)) :
    view ((circuit layout rom romFits ramFits).component.run (encode state ramInactive fetchInactive) traffic) =
      (SystemModel.component layout rom).run state (traffic.map decode) := by
  rw [run_eq layout rom romFits ramFits _ (valid_encode layout rom state h ramInactive fetchInactive),
    view_encode state h.core ramInactive fetchInactive, spec_run]

variable {rtl : Timed.Component (Values Input) (Values (Register aw)) (Values Output)}

/-- A supplied correspondence must cover the actual artifact's complete typed
state and output interface; this module does not manufacture that certificate. -/
theorem artifact_trace_eq (artifact : Artifact.Correspondence (circuit layout rom romFits ramFits) rtl)
    (raw : Values (Register aw)) (h : Valid layout rom raw) (traffic : List (Values Input)) :
    rtl.trace raw traffic = (spec layout rom).trace (view raw) traffic :=
  (implementation layout rom romFits ramFits).artifact_trace_eq artifact raw h traffic

theorem artifact_run_eq (artifact : Artifact.Correspondence (circuit layout rom romFits ramFits) rtl)
    (raw : Values (Register aw)) (h : Valid layout rom raw) (traffic : List (Values Input)) :
    view (rtl.run raw traffic) = (spec layout rom).run (view raw) traffic :=
  (implementation layout rom romFits ramFits).artifact_run_eq artifact raw h traffic

theorem artifact_trace_after_reset (artifact : Artifact.Correspondence (circuit layout rom romFits ramFits) rtl)
    (i : Values Input) (raw : Values (Register aw)) (h : i reset = 1) (traffic : List (Values Input)) :
    rtl.trace (rtl.step i raw) traffic = (spec layout rom).trace (resetState raw) traffic :=
  (resetCertificate layout rom romFits ramFits).artifact_trace_after_reset (implementation layout rom romFits ramFits) reset artifact i raw h traffic

theorem artifact_run_after_reset (artifact : Artifact.Correspondence (circuit layout rom romFits ramFits) rtl)
    (i : Values Input) (raw : Values (Register aw)) (h : i reset = 1) (traffic : List (Values Input)) :
    view (rtl.run (rtl.step i raw) traffic) = (spec layout rom).run (resetState raw) traffic :=
  (resetCertificate layout rom romFits ramFits).artifact_run_after_reset (implementation layout rom romFits ramFits) reset artifact i raw h traffic


end Pinwheel.Hardware.Processor.SystemCircuit
