import Pinwheel.Hardware.Processor.SerialCircuitProofs

/-! Event replay from actual imported MMIO response and UART pulse outputs.
Transport requires a complete correspondence certificate for the imported
artifact and the serial ownership/counter invariant after initialization. -/
namespace Pinwheel.Hardware.Processor.SerialRefinement

open SerialInterface SerialCircuit Timed

abbrev Physical (d : Uart.Timing) := Component (Values Input) (Values (Register d)) (Values Output)

def observedResponse (rtl : Physical d) (i : Values Input) (s : Values (Register d)) : Option MmioModel.Response :=
  if rtl.observe i s (.left MmioInterface.responseValid) = 1 then
    MmioCircuit.decodeResponse (rtl.observe i s (.left MmioInterface.responseCode))
      (rtl.observe i s (.left MmioInterface.responseData)) else none

def observedMmioPins (rtl : Physical d) (i : Values Input) (s : Values (Register d)) : Values MmioInterface.Input
  | _, .at ⟨7,_⟩ => rtl.observe i s (.right Uart.Physical.txComplete)
  | _, .at ⟨8,_⟩ => rtl.observe i s (.right Uart.Physical.rxValid)
  | _, .at ⟨9,_⟩ => rtl.observe i s (.right Uart.Physical.rxData)
  | _, .at ⟨10,_⟩ => rtl.observe i s (.right Uart.Physical.framingError)
  | _, p => cpuPins i p

def events (rtl : Physical d) (i : Values Input) (s : Values (Register d)) : List MmioModel.Event :=
  let p : Values MmioInterface.Input := observedMmioPins rtl i s
  let m := MmioInterface.decode p
  if m.reset then [.reset] else
    m.operation.toList.map (fun request => .cpu request (p MmioInterface.gpioInput)
      ((observedResponse rtl i s).getD (.fault .registerHole))) ++
    MmioModel.autonomousEvents m (view s).mmio (MmioModel.cpuState m (view s).mmio)

variable {rtl : Physical d}

theorem observedResponse_eq (proof : Artifact.Correspondence (circuit d) rtl)
    (i : Values Input) (s : Values (Register d)) :
    observedResponse rtl i s = SerialCircuit.observedResponse d i s := by
  simp only [observedResponse,SerialCircuit.observedResponse,proof.output_eq]

theorem observedMmioPins_eq (proof : Artifact.Correspondence (circuit d) rtl)
    (i : Values Input) (s : Values (Register d)) (p : MmioInterface.Input b) :
    observedMmioPins rtl i s p = boundMmioPins d i s p := by
  match p with
  | .at ⟨0,_⟩ | .at ⟨1,_⟩ | .at ⟨2,_⟩ | .at ⟨3,_⟩ | .at ⟨4,_⟩ | .at ⟨5,_⟩ | .at ⟨6,_⟩ => rfl
  | .at ⟨7,_⟩ => exact congrFun (congrFun (proof.output_eq i s) 1) (.right Uart.Physical.txComplete)
  | .at ⟨8,_⟩ => exact congrFun (congrFun (proof.output_eq i s) 1) (.right Uart.Physical.rxValid)
  | .at ⟨9,_⟩ => exact congrFun (congrFun (proof.output_eq i s) 8) (.right Uart.Physical.rxData)
  | .at ⟨10,_⟩ => exact congrFun (congrFun (proof.output_eq i s) 1) (.right Uart.Physical.framingError)
  | .at ⟨k+11,h⟩ => exact False.elim (by change k+11 < 11 at h; omega)

theorem events_eq (proof : Artifact.Correspondence (circuit d) rtl)
    (i : Values Input) (s : Values (Register d)) : events rtl i s = physicalEvents d i s := by
  have pins_eq := funext fun b => funext fun p => observedMmioPins_eq proof i s (b := b) p
  simp only [events,physicalEvents,observedResponse_eq proof,pins_eq]

def refinement (proof : Artifact.Correspondence (circuit d) rtl) :
    EventRefinement rtl MmioModel.eventSpec (events rtl) (fun i _ => Admitted i) :=
  (SerialCircuit.eventRefinement d).ofLockstep proof.refinement (events rtl) (fun i _ => Admitted i)
    (by intro i r s h; cases h; exact events_eq proof i r)
    (by intros; assumption)

theorem related_iff (proof : Artifact.Correspondence (circuit d) rtl)
    (s : Values (Register d)) (logical : MmioModel.State) :
    (refinement proof).Rel s logical ↔ Valid d s ∧ (view s).mmio = logical := by
  simp only [refinement,EventRefinement.ofLockstep,Artifact.Correspondence.refinement,SerialCircuit.eventRefinement]
  simp

theorem coverage (proof : Artifact.Correspondence (circuit d) rtl) :
    (refinement proof).InitialCoverage (Valid d) (fun _ => True) where
  nonempty := ⟨encode d SerialModel.initial,encode_valid _ (SerialModel.initial_valid d)⟩
  covered s h := ⟨(view s).mmio,trivial,(related_iff proof s (view s).mmio).mpr ⟨h,rfl⟩⟩

theorem trace_path (proof : Artifact.Correspondence (circuit d) rtl)
    (s : Values (Register d)) (hs : Valid d s) (traffic : List (Values Input))
    (legal : rtl.Legal (fun i _ => Admitted i) s traffic) :
    MmioModel.eventSpec.Path (view s).mmio (rtl.eventTrace (events rtl) s traffic)
      (view (rtl.run s traffic)).mmio := by
  obtain ⟨last,path,related⟩ := (refinement proof).trace s (view s).mmio traffic
    ((related_iff proof s (view s).mmio).mpr ⟨hs,rfl⟩) legal
  have equality := ((related_iff proof _ _).mp related).2
  simpa [equality] using path

theorem replay_trace (proof : Artifact.Correspondence (circuit d) rtl)
    (s : Values (Register d)) (hs : Valid d s) (traffic : List (Values Input))
    (legal : rtl.Legal (fun i _ => Admitted i) s traffic) :
    MmioModel.replay (view s).mmio (rtl.eventTrace (events rtl) s traffic) =
      some (view (rtl.run s traffic)).mmio :=
  MmioCircuit.replay_of_path (trace_path proof s hs traffic legal)

theorem reset_events (rtl : Physical d) (i : Values Input) (s : Values (Register d)) (hr : i reset = 1) :
    events rtl i s = [.reset] := by
  have reset_eq : (MmioInterface.decode (observedMmioPins rtl i s)).reset = true := by
    change (i reset == 1) = true
    simp [hr]
  simp only [events,reset_eq,ite_true]

theorem replay_after_reset (proof : Artifact.Correspondence (circuit d) rtl)
    (i : Values Input) (s : Values (Register d)) (hr : i reset = 1)
    (traffic : List (Values Input))
    (legal : rtl.Legal (fun j _ => Admitted j) (rtl.step i s) traffic) :
    MmioModel.replay MmioModel.initial
      (rtl.eventTrace (events rtl) (rtl.step i s) traffic) =
      some (view (rtl.run (rtl.step i s) traffic)).mmio := by
  have hs : Valid d (rtl.step i s) := by
    rw [proof.step_eq]
    exact reset_valid i s hr
  have result := replay_trace proof (rtl.step i s) hs traffic legal
  rw [proof.step_eq,SerialCircuit.reset_view i s hr] at result
  simpa only [proof.step_eq,SerialModel.initial] using result

end Pinwheel.Hardware.Processor.SerialRefinement
