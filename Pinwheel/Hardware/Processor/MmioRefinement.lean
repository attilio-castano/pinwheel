import Pinwheel.Hardware.Processor.MmioCircuitProofs

/-! Actual-response event transport through an explicit complete RTL artifact
certificate. Raw selector3 remains covered by the functional wrapper; only
admitted selectors transport into the typed MMIO event model. This module does
not supply an artifact certificate or prove serial-wire frontend behavior. -/
namespace Pinwheel.Hardware.Processor.MmioRefinement

open MmioInterface MmioCircuit Timed

abbrev Physical := Component (Values Input) (Values Register) (Values Output)

def observedResponse (rtl : Physical) (i : Values Input) (s : Values Register) : Option MmioModel.Response :=
  if rtl.observe i s responseValid = 1 then
    decodeResponse (rtl.observe i s responseCode) (rtl.observe i s responseData) else none

def events (rtl : Physical) (i : Values Input) (s : Values Register) : List MmioModel.Event :=
  if (decode i).reset then [.reset] else
    (decode i).operation.toList.map (fun request => .cpu request (i gpioInput)
      ((observedResponse rtl i s).getD (.fault .registerHole))) ++
    MmioModel.autonomousEvents (decode i) (view s) (MmioModel.cpuState (decode i) (view s))

variable {rtl : Physical}

theorem observedResponse_eq (proof : Artifact.Correspondence circuit rtl)
    (i : Values Input) (s : Values Register) :
    observedResponse rtl i s = MmioCircuit.observedResponse i s := by
  simp only [observedResponse, MmioCircuit.observedResponse, proof.output_eq]

theorem events_eq (proof : Artifact.Correspondence circuit rtl)
    (i : Values Input) (s : Values Register) : events rtl i s = physicalEvents i s := by
  simp only [events, physicalEvents, observedResponse_eq proof]

def refinement (proof : Artifact.Correspondence circuit rtl) :
    EventRefinement rtl MmioModel.eventSpec (events rtl) (fun i _ => Admitted i) :=
  eventRefinement.ofLockstep proof.refinement (events rtl) (fun i _ => Admitted i)
    (by intro i r s h; cases h; exact events_eq proof i r)
    (by intros; assumption)

theorem related_iff (proof : Artifact.Correspondence circuit rtl)
    (s : Values Register) (logical : MmioModel.State) :
    (refinement proof).Rel s logical ↔ view s = logical := by
  simp only [refinement, EventRefinement.ofLockstep, Artifact.Correspondence.refinement, eventRefinement]
  simp

theorem coverage (proof : Artifact.Correspondence circuit rtl) :
    (refinement proof).InitialCoverage (fun _ => True) (fun _ => True) where
  nonempty := ⟨encode MmioModel.initial, trivial⟩
  covered s _ := ⟨view s, trivial, (related_iff proof s (view s)).mpr rfl⟩

theorem trace_path (proof : Artifact.Correspondence circuit rtl)
    (s : Values Register) (traffic : List (Values Input))
    (legal : rtl.Legal (fun i _ => Admitted i) s traffic) :
    MmioModel.eventSpec.Path (view s) (rtl.eventTrace (events rtl) s traffic) (view (rtl.run s traffic)) := by
  obtain ⟨last, path, related⟩ := (refinement proof).trace s (view s) traffic
    ((related_iff proof s (view s)).mpr rfl) legal
  have equality := (related_iff proof _ _).mp related
  simpa [equality] using path

theorem replay_trace (proof : Artifact.Correspondence circuit rtl)
    (s : Values Register) (traffic : List (Values Input))
    (legal : rtl.Legal (fun i _ => Admitted i) s traffic) :
    MmioModel.replay (view s) (rtl.eventTrace (events rtl) s traffic) = some (view (rtl.run s traffic)) :=
  replay_of_path (trace_path proof s traffic legal)

theorem reset_events (rtl : Physical) (i : Values Input) (s : Values Register) (hr : i reset = 1) :
    events rtl i s = [.reset] := by simp [events, decode, hr]

theorem replay_after_reset (proof : Artifact.Correspondence circuit rtl)
    (i : Values Input) (s : Values Register) (hr : i reset = 1)
    (traffic : List (Values Input))
    (legal : rtl.Legal (fun j _ => Admitted j) (rtl.step i s) traffic) :
    MmioModel.replay MmioModel.initial
      (rtl.eventTrace (events rtl) (rtl.step i s) traffic) =
      some (view (rtl.run (rtl.step i s) traffic)) := by
  have result := replay_trace proof (rtl.step i s) traffic legal
  rw [proof.step_eq, MmioCircuit.reset_view i s hr] at result
  simpa only [proof.step_eq] using result

end Pinwheel.Hardware.Processor.MmioRefinement
