import Pinwheel.Hardware.Memory.TransferHostCircuitProofs
import Pinwheel.Hardware.RunRefinement

/-! A separately certified ownership candidate. Idle phase selects host memory
inputs even on an accepted start. At that boundary both pending slots are empty
and the offered start already suppresses host requests, so both memory choices
perform an idle transition. The original constructor remains unchanged.
-/
namespace Pinwheel.Hardware.Memory.TransferHostOwnershipCandidate

open TransferHostInterface

abbrev Register := TransferHostCircuit.Register
abbrev registers := TransferHostCircuit.registers
abbrev encode (s : TransferModel.State a wi wo) : Values (Register a wi wo) := TransferHostCircuit.encode s

def sourceInput (m : Hardware.Stream.Map wi wo) (p : StreamInterface.Input a wi b) :
    Expr (Input a wi wo) (Register a wi wo) b :=
  .mux (TransferHostCircuit.phase 0) (TransferHostCircuit.sourceHostInput p)
    (TransferHostCircuit.sourceControllerInput m p)

def destinationInput (m : Hardware.Stream.Map wi wo) (p : StreamInterface.Input a wo b) :
    Expr (Input a wi wo) (Register a wi wo) b :=
  .mux (TransferHostCircuit.phase 0) (TransferHostCircuit.destinationHostInput p)
    (TransferHostCircuit.destinationControllerInput m p)

def sourcePins (m : Hardware.Stream.Map wi wo) (i : Values (Input a wi wo))
    (s : Values (Register a wi wo)) : Values (StreamInterface.Input a wi) :=
  fun p => (sourceInput m p).eval i s

def destinationPins (m : Hardware.Stream.Map wi wo) (i : Values (Input a wi wo))
    (s : Values (Register a wi wo)) : Values (StreamInterface.Input a wo) :=
  fun p => (destinationInput m p).eval i s

def circuit (m : Hardware.Stream.Map wi wo) : Circuit (Input a wi wo) (Register a wi wo) (Output wi wo) where
  next := fun {b} r => match b, r with
    | _, .left r => (TransferHostCircuit.circuit m).next (.left r)
    | _, .right (.left r) => ((StreamFlops.circuit a wi).next r).bind (sourceInput m) (fun r => .reg (.right (.left r)))
    | _, .right (.right r) => ((StreamFlops.circuit a wo).next r).bind (destinationInput m) (fun r => .reg (.right (.right r)))
  output := (TransferHostCircuit.circuit m).output

theorem source_step (m : Hardware.Stream.Map wi wo) (i : Values (Input a wi wo))
    (s : Values (Register a wi wo)) (r : StreamFlops.Register a wi b) :
    (circuit m).step i s (.right (.left r)) =
      (StreamFlops.circuit a wi).step (sourcePins m i s) (TransferHostCircuit.sourceValues s) r :=
  Expr.eval_bind (sourceInput m) (fun r => .reg (.right (.left r))) ((StreamFlops.circuit a wi).next r) i s

theorem destination_step (m : Hardware.Stream.Map wi wo) (i : Values (Input a wi wo))
    (s : Values (Register a wi wo)) (r : StreamFlops.Register a wo b) :
    (circuit m).step i s (.right (.right r)) =
      (StreamFlops.circuit a wo).step (destinationPins m i s) (TransferHostCircuit.destinationValues s) r :=
  Expr.eval_bind (destinationInput m) (fun r => .reg (.right (.right r))) ((StreamFlops.circuit a wo).next r) i s

/-- An idle request and an already empty response slot preserve every register,
independently of reset, readiness, or inactive write/address/data values. -/
theorem idle_empty (i : Values (StreamInterface.Input a w)) (s : Values (StreamFlops.Register a w))
    (hv : i StreamInterface.valid = 0) (hp : s StreamFlops.pending = 0) :
    (fun {b} (r : StreamFlops.Register a w b) => (StreamFlops.circuit a w).step i s r) = @s := by
  have h : StreamModel.step (StreamInterface.decode i) (StreamFlops.view s) = StreamFlops.view s := by
    rcases BitVec.eq_zero_or_eq_one (i StreamInterface.reset) with hr | hr <;>
      simp [StreamModel.step, StreamModel.command, StreamModel.ready, SinglePort.step,
        StreamInterface.decode, StreamFlops.view, hv, hp, hr]
  have he := StreamFlops.encode_view ((StreamFlops.circuit a w).step i s)
  rw [StreamFlops.step_view, h, StreamFlops.encode_view] at he
  exact he.symm

theorem accepted_facts (i : Values (Input a wi wo)) (s : Values (Register a wi wo))
    (h : TransferHostCircuit.acceptedStart.eval i s = 1) :
    i reset = 0 ∧ s (.left .phase) = 0 ∧ i startValid = 1 ∧
      s (.right (.left StreamFlops.pending)) = 0 ∧ s (.right (.right StreamFlops.pending)) = 0 := by
  rcases BitVec.eq_zero_or_eq_one (i reset) with hr | hr <;>
    rcases BitVec.eq_zero_or_eq_one (i startValid) with hv | hv <;>
    rcases BitVec.eq_zero_or_eq_one (s (.right (.left StreamFlops.pending))) with hs | hs <;>
    rcases BitVec.eq_zero_or_eq_one (s (.right (.right StreamFlops.pending))) with hd | hd <;>
    by_cases hp : s (.left .phase) = 0#2
  all_goals simp [TransferHostCircuit.acceptedStart, TransferHostCircuit.canStart,
    TransferHostCircuit.sourcePending, TransferHostCircuit.destinationPending,
    TransferHostCircuit.phase, Expr.eval, hr, hv, hs, hd, hp] at h
  exact ⟨hr, hp, hv, hs, hd⟩

theorem unchanged_selector (i : Values (Input a wi wo)) (s : Values (Register a wi wo))
    (h : TransferHostCircuit.acceptedStart.eval i s = 0) :
    TransferHostCircuit.hostMode.eval i s = (TransferHostCircuit.phase 0).eval i s := by
  simp only [TransferHostCircuit.hostMode, Expr.eval, h]
  exact BitVec.and_allOnes

theorem idle_controller_requests (m : Hardware.Stream.Map wi wo) (i : Values (Input a wi wo))
    (s : Values (Register a wi wo)) (hp : s (.left .phase) = 0#2) :
    (TransferHostCircuit.sourceControllerInput m StreamInterface.valid).eval i s = 0 ∧
      (TransferHostCircuit.destinationControllerInput m StreamInterface.valid).eval i s = 0 := by
  simp [TransferHostCircuit.sourceControllerInput, TransferHostCircuit.destinationControllerInput,
    StreamInterface.valid, TransferHostCircuit.controllerOutput_eval, Circuit.observe, TransferCircuit.circuit,
    TransferInterface.sourceRequestValid, TransferInterface.destinationRequestValid, TransferCircuit.gated,
    TransferCircuit.isPhase, TransferCircuit.destinationValid, Expr.eval, TransferHostCircuit.controlValues, hp]
  exact ⟨fun _ => rfl, fun _ => rfl⟩

theorem source_step_eq (m : Hardware.Stream.Map wi wo) (i : Values (Input a wi wo))
    (s : Values (Register a wi wo)) (r : StreamFlops.Register a wi b) :
    (circuit m).step i s (.right (.left r)) =
      (TransferHostCircuit.circuit m).step i s (.right (.left r)) := by
  rw [source_step, TransferHostCircuit.source_step]
  rcases BitVec.eq_zero_or_eq_one (TransferHostCircuit.acceptedStart.eval i s) with ha | ha
  · have he : (fun {b} (p : StreamInterface.Input a wi b) => sourcePins m i s p) =
        (fun {b} (p : StreamInterface.Input a wi b) => TransferHostCircuit.sourcePins m i s p) := by
      funext b p
      simp only [sourcePins, sourceInput, TransferHostCircuit.sourcePins, TransferHostCircuit.sourceInput,
        Expr.eval, unchanged_selector i s ha]
    rw [he]
  · rcases accepted_facts i s ha with ⟨hr, hp, hv, hs, hd⟩
    have hc := (idle_controller_requests m i s hp).1
    have hnew : sourcePins m i s StreamInterface.valid = 0 := by
      simp [sourcePins, sourceInput, TransferHostCircuit.phase, Expr.eval, hp,
        TransferHostCircuit.sourceHostInput, StreamInterface.valid, hv]
    have hold : TransferHostCircuit.sourcePins m i s StreamInterface.valid = 0 := by
      simp [TransferHostCircuit.sourcePins, TransferHostCircuit.sourceInput, TransferHostCircuit.hostMode,
        Expr.eval, ha, hc]
    have hn := congrFun (congrFun (idle_empty (sourcePins m i s) (TransferHostCircuit.sourceValues s) hnew hs) b) r
    have ho := congrFun (congrFun (idle_empty (TransferHostCircuit.sourcePins m i s)
      (TransferHostCircuit.sourceValues s) hold hs) b) r
    exact hn.trans ho.symm

theorem destination_step_eq (m : Hardware.Stream.Map wi wo) (i : Values (Input a wi wo))
    (s : Values (Register a wi wo)) (r : StreamFlops.Register a wo b) :
    (circuit m).step i s (.right (.right r)) =
      (TransferHostCircuit.circuit m).step i s (.right (.right r)) := by
  rw [destination_step, TransferHostCircuit.destination_step]
  rcases BitVec.eq_zero_or_eq_one (TransferHostCircuit.acceptedStart.eval i s) with ha | ha
  · have he : (fun {b} (p : StreamInterface.Input a wo b) => destinationPins m i s p) =
        (fun {b} (p : StreamInterface.Input a wo b) => TransferHostCircuit.destinationPins m i s p) := by
      funext b p
      simp only [destinationPins, destinationInput, TransferHostCircuit.destinationPins, TransferHostCircuit.destinationInput,
        Expr.eval, unchanged_selector i s ha]
    rw [he]
  · rcases accepted_facts i s ha with ⟨hr, hp, hv, hs, hd⟩
    have hc := (idle_controller_requests m i s hp).2
    have hnew : destinationPins m i s StreamInterface.valid = 0 := by
      simp [destinationPins, destinationInput, TransferHostCircuit.phase, Expr.eval, hp,
        TransferHostCircuit.destinationHostInput, StreamInterface.valid, hv]
    have hold : TransferHostCircuit.destinationPins m i s StreamInterface.valid = 0 := by
      simp [TransferHostCircuit.destinationPins, TransferHostCircuit.destinationInput, TransferHostCircuit.hostMode,
        Expr.eval, ha, hc]
    have hn := congrFun (congrFun (idle_empty (destinationPins m i s) (TransferHostCircuit.destinationValues s) hnew hd) b) r
    have ho := congrFun (congrFun (idle_empty (TransferHostCircuit.destinationPins m i s)
      (TransferHostCircuit.destinationValues s) hold hd) b) r
    exact hn.trans ho.symm

/-- Full raw-state correspondence: no controller invariant, initialized memory,
or reachable-state premise is needed for the ownership optimization. -/
theorem step_eq (m : Hardware.Stream.Map wi wo) (i : Values (Input a wi wo))
    (s : Values (Register a wi wo)) (r : Register a wi wo b) :
    (circuit m).step i s r = (TransferHostCircuit.circuit m).step i s r := by
  cases r with
  | left r => rfl
  | right r => cases r with
    | left r => exact source_step_eq m i s r
    | right r => exact destination_step_eq m i s r

theorem output_eq (m : Hardware.Stream.Map wi wo) (i : Values (Input a wi wo))
    (s : Values (Register a wi wo)) (o : Output wi wo b) :
    (circuit m).observe i s o = (TransferHostCircuit.circuit m).observe i s o := rfl

theorem correspondence (m : Hardware.Stream.Map wi wo) :
    Artifact.Correspondence (TransferHostCircuit.circuit (a := a) m) (circuit m).component where
  step_eq i s := funext fun b => funext fun r => step_eq m i s (b := b) r
  output_eq _ _ := rfl

def implementation (m : Hardware.Stream.Map wi wo) :
    Implementation (circuit (a := a) m) (TransferHostInterface.spec m) where
  Valid := fun s => s.control.Valid
  encode := encode
  preserved i s hs := (TransferHostCircuit.implementation m).preserved i s hs
  step_eq i s hs {_} r := (step_eq m i (encode s) r).trans (TransferHostCircuit.step_eq m i s hs r)
  output_eq i s _ {_} o := TransferHostCircuit.output_eq m i s o

theorem trace_eq (m : Hardware.Stream.Map wi wo) (s : Values (Register a wi wo))
    (inputs : List (Values (Input a wi wo))) :
    (circuit m).component.trace s inputs = (TransferHostCircuit.circuit m).component.trace s inputs :=
  (correspondence m).refinement.trace_eq _ _ rfl inputs

theorem run_eq (m : Hardware.Stream.Map wi wo) (s : Values (Register a wi wo))
    (inputs : List (Values (Input a wi wo))) :
    @Eq (Values (Register a wi wo)) ((circuit m).component.run s inputs)
      ((TransferHostCircuit.circuit m).component.run s inputs) :=
  (correspondence m).run_eq s inputs

theorem trace_correct (m : Hardware.Stream.Map wi wo) (s : TransferModel.State a wi wo)
    (h : s.control.Valid) (inputs : List (Values (Input a wi wo))) :
    (circuit m).component.trace (encode s) inputs = (TransferHostInterface.spec m).trace s inputs :=
  (implementation m).trace_eq s h inputs

theorem encoded_final_state (m : Hardware.Stream.Map wi wo) (s : TransferModel.State a wi wo)
    (h : s.control.Valid) (inputs : List (Values (Input a wi wo))) :
    @Eq (Values (Register a wi wo)) ((circuit m).component.run (encode s) inputs)
      (encode ((TransferHostInterface.spec m).run s inputs)) :=
  (implementation m).run_eq s h inputs

theorem reset_eq (m : Hardware.Stream.Map wi wo) (i : Values (Input a wi wo))
    (s : Values (Register a wi wo)) (hr : i reset = 1) (r : Register a wi wo b) :
    (circuit m).step i s r = encode (TransferHostCircuit.resetState s) r :=
  (step_eq m i s r).trans (TransferHostCircuit.reset_eq m i s hr r)

theorem recovery_eq (m : Hardware.Stream.Map wi wo) (i : Values (Input a wi wo))
    (s : Values (Register a wi wo)) (hr : i reset = 0) (hp : s (.left .phase) = 3)
    (r : Register a wi wo b) :
    (circuit m).step i s r = encode (TransferHostCircuit.recoveryState s) r :=
  (step_eq m i s r).trans (TransferHostCircuit.recovery_eq m i s hr hp r)

theorem trace_after_reset (m : Hardware.Stream.Map wi wo) (i : Values (Input a wi wo))
    (s : Values (Register a wi wo)) (hr : i reset = 1) (inputs : List (Values (Input a wi wo))) :
    (circuit m).component.trace ((circuit m).step i s) inputs =
      (TransferHostInterface.spec m).trace (TransferHostCircuit.resetState s) inputs := by
  rw [trace_eq]
  have h := funext fun b => funext fun r => step_eq m i s (b := b) r
  rw [h]
  exact TransferHostCircuit.trace_after_reset m i s hr inputs

theorem reset_final_state (m : Hardware.Stream.Map wi wo) (i : Values (Input a wi wo))
    (s : Values (Register a wi wo)) (hr : i reset = 1) (inputs : List (Values (Input a wi wo))) :
    @Eq (Values (Register a wi wo)) ((circuit m).component.run ((circuit m).step i s) inputs)
      (encode ((TransferHostInterface.spec m).run (TransferHostCircuit.resetState s) inputs)) := by
  have h := funext fun b => funext fun r => reset_eq m i s hr (b := b) r
  rw [h]
  apply encoded_final_state
  simp [TransferHostCircuit.resetState, TransferModel.initialState, TransferModel.initialControl,
    TransferModel.Control.Valid, TransferModel.emptyConfig]

theorem trace_after_recovery (m : Hardware.Stream.Map wi wo) (i : Values (Input a wi wo))
    (s : Values (Register a wi wo)) (hr : i reset = 0) (hp : s (.left .phase) = 3)
    (inputs : List (Values (Input a wi wo))) :
    (circuit m).component.trace ((circuit m).step i s) inputs =
      (TransferHostInterface.spec m).trace (TransferHostCircuit.recoveryState s) inputs := by
  rw [trace_eq]
  have h := funext fun b => funext fun r => step_eq m i s (b := b) r
  rw [h]
  exact TransferHostCircuit.trace_after_recovery m i s hr hp inputs

end Pinwheel.Hardware.Memory.TransferHostOwnershipCandidate
