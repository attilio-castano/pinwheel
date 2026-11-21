import Pinwheel.Hardware.Memory.TransferHostCircuit
import Pinwheel.Hardware.Memory.StreamFlopsProofs
import Pinwheel.Hardware.Memory.TransferCircuitProofs

namespace Pinwheel.Hardware.Memory.TransferHostCircuit

open TransferHostInterface

set_option backward.isDefEq.respectTransparency false

@[simp] theorem controlValues_encode (s : TransferModel.State a wi wo) :
    @controlValues a wi wo (encode s) = @TransferCircuit.encode a s.control := rfl
@[simp] theorem sourceValues_encode (s : TransferModel.State a wi wo) :
    @sourceValues a wi wo (encode s) = @StreamFlops.encode a wi s.source := rfl
@[simp] theorem destinationValues_encode (s : TransferModel.State a wi wo) :
    @destinationValues a wi wo (encode s) = @StreamFlops.encode a wo s.destination := rfl

theorem controller_step (m : Hardware.Stream.Map wi wo) (i : Values (Input a wi wo))
    (s : Values (Register a wi wo)) (r : TransferCircuit.Register a b) :
    (circuit m).step i s (.left r) =
      (TransferCircuit.circuit m).step (controllerPins i s) (controlValues s) r :=
  Expr.eval_bind controllerInput (fun r => .reg (.left r)) ((TransferCircuit.circuit m).next r) i s

theorem source_step (m : Hardware.Stream.Map wi wo) (i : Values (Input a wi wo))
    (s : Values (Register a wi wo)) (r : StreamFlops.Register a wi b) :
    (circuit m).step i s (.right (.left r)) =
      (StreamFlops.circuit a wi).step (sourcePins m i s) (sourceValues s) r :=
  Expr.eval_bind (sourceInput m) (fun r => .reg (.right (.left r))) ((StreamFlops.circuit a wi).next r) i s

theorem destination_step (m : Hardware.Stream.Map wi wo) (i : Values (Input a wi wo))
    (s : Values (Register a wi wo)) (r : StreamFlops.Register a wo b) :
    (circuit m).step i s (.right (.right r)) =
      (StreamFlops.circuit a wo).step (destinationPins m i s) (destinationValues s) r :=
  Expr.eval_bind (destinationInput m) (fun r => .reg (.right (.right r))) ((StreamFlops.circuit a wo).next r) i s

theorem controllerOutput_eval (m : Hardware.Stream.Map wi wo) (i : Values (Input a wi wo))
    (s : Values (Register a wi wo)) (o : TransferInterface.Output a wo b) :
    (controllerOutput m o).eval i s =
      (TransferCircuit.circuit m).observe (controllerPins i s) (controlValues s) o :=
  Expr.eval_bind controllerInput (fun r => .reg (.left r)) ((TransferCircuit.circuit m).output o) i s

theorem sourceHostOutput_eval (i : Values (Input a wi wo)) (s : Values (Register a wi wo))
    (o : StreamInterface.Output wi b) :
    (sourceHostOutput o).eval i s =
      (StreamFlops.circuit a wi).observe (sourceHostValues i s) (sourceValues s) o :=
  Expr.eval_bind sourceHostInput (fun r => .reg (.right (.left r))) ((StreamFlops.circuit a wi).output o) i s

theorem destinationHostOutput_eval (i : Values (Input a wi wo)) (s : Values (Register a wi wo))
    (o : StreamInterface.Output wo b) :
    (destinationHostOutput o).eval i s =
      (StreamFlops.circuit a wo).observe (destinationHostValues i s) (destinationValues s) o :=
  Expr.eval_bind destinationHostInput (fun r => .reg (.right (.right r))) ((StreamFlops.circuit a wo).output o) i s

theorem canStart_eval (i : Values (Input a wi wo)) (s : TransferModel.State a wi wo) :
    canStart.eval i (encode s) = BitVec.ofBool (TransferHostModel.startReady (decode i) s) := by
  rcases BitVec.eq_zero_or_eq_one (i reset) with hr | hr <;>
    cases hp : s.control.phase <;> cases hs : s.source.pending <;> cases hd : s.destination.pending
  all_goals simp [canStart, phase, sourcePending, destinationPending, Expr.eval, encode,
    TransferCircuit.encode, TransferCircuit.phaseBits, StreamFlops.encode, StreamFlops.pending,
    TransferHostModel.startReady, decode, hr, hp, hs, hd]
  all_goals rfl

theorem acceptedStart_eval (i : Values (Input a wi wo)) (s : TransferModel.State a wi wo) :
    acceptedStart.eval i (encode s) = BitVec.ofBool (TransferHostModel.acceptedStart (decode i) s) := by
  rw [acceptedStart, Expr.eval, canStart_eval]
  rcases BitVec.eq_zero_or_eq_one (i startValid) with hi | hi <;>
    cases hc : TransferHostModel.startReady (decode i) s
  all_goals simp only [TransferHostModel.acceptedStart, hc, Expr.eval]
  all_goals simp [decode, hi]

theorem hostMode_eval (i : Values (Input a wi wo)) (s : TransferModel.State a wi wo) :
    hostMode.eval i (encode s) =
      BitVec.ofBool (s.control.phase == .idle && !TransferHostModel.acceptedStart (decode i) s) := by
  rw [hostMode, Expr.eval, Expr.eval, acceptedStart_eval]
  cases hp : s.control.phase <;> cases ha : TransferHostModel.acceptedStart (decode i) s
  all_goals simp [phase, Expr.eval, encode, TransferCircuit.encode, TransferCircuit.phaseBits, hp]
  all_goals rfl

theorem sourceHost_decode (i : Values (Input a wi wo)) (s : Values (Register a wi wo)) :
    StreamInterface.decode (sourceHostValues i s) = TransferHostModel.sourceInput (decode i) := by
  rcases BitVec.eq_zero_or_eq_one (i startValid) with hi | hi <;>
    rcases BitVec.eq_zero_or_eq_one (i sourceValid) with hv | hv
  all_goals simp [StreamInterface.decode, sourceHostValues, sourceHostInput, Expr.eval,
    StreamInterface.reset, StreamInterface.valid, StreamInterface.write, StreamInterface.address,
    StreamInterface.data, StreamInterface.ready, TransferHostModel.sourceInput, decode, sourceHostPins,
    StreamInterface.Pins.values, hi, hv]
  all_goals rfl

theorem destinationHost_decode (i : Values (Input a wi wo)) (s : Values (Register a wi wo)) :
    StreamInterface.decode (destinationHostValues i s) = TransferHostModel.destinationInput (decode i) := by
  rcases BitVec.eq_zero_or_eq_one (i startValid) with hi | hi <;>
    rcases BitVec.eq_zero_or_eq_one (i destinationValid) with hv | hv
  all_goals simp [StreamInterface.decode, destinationHostValues, destinationHostInput, Expr.eval,
    StreamInterface.reset, StreamInterface.valid, StreamInterface.write, StreamInterface.address,
    StreamInterface.data, StreamInterface.ready, TransferHostModel.destinationInput, decode, destinationHostPins,
    StreamInterface.Pins.values, hi, hv]
  all_goals rfl

/-- On reset, the physical feedback deliberately masks response/ready bits.
The controller ignores those bits on reset; equality with logical feedback is
therefore stated only off reset, and raw reset recovery is proved separately. -/
theorem controller_decode (i : Values (Input a wi wo)) (s : TransferModel.State a wi wo)
    (hr : i reset = 0) :
    TransferInterface.decode (controllerPins i (encode s)) =
      TransferModel.feedback (TransferHostModel.controllerInput (decode i) s) s := by
  rcases BitVec.eq_zero_or_eq_one (i startValid) with hi | hi <;>
    cases hp : s.control.phase <;> cases hs : s.source.pending <;> cases hd : s.destination.pending
  all_goals simp [TransferInterface.decode, controllerPins, controllerInput, acceptedStart, canStart,
    memoryReset, phase, sourcePending, destinationPending, controllerResponseReady, controllerResponseValid,
    Expr.eval, Expr.bor, encode, TransferCircuit.encode, TransferCircuit.phaseBits,
    StreamFlops.encode, StreamFlops.pending, CommandFlops.encode, CommandFlops.q,
    TransferInterface.reset, TransferInterface.startValid, TransferInterface.sourceBase,
    TransferInterface.destinationBase, TransferInterface.length, TransferInterface.sourceRequestReady,
    TransferInterface.sourceResponseValid, TransferInterface.sourceResponseData, TransferInterface.destinationRequestReady,
    TransferModel.feedback, TransferHostModel.controllerInput, TransferHostModel.startReady,
    decode, StreamModel.ready, StreamModel.offer, hr, hi, hp, hs, hd]
  all_goals rfl

theorem sourceController_values (m : Hardware.Stream.Map wi wo) (i : Values (Input a wi wo))
    (s : Values (Register a wi wo)) :
    (fun {b} (p : StreamInterface.Input a wi b) => (sourceControllerInput m p).eval i s) =
      @TransferCircuit.sourceMemoryPins a wo wi
        ((TransferCircuit.circuit m).observe (controllerPins i s) (controlValues s)) := by
  funext b p
  cases p with
  | «at» k =>
    match k with
    | ⟨0, _⟩ | ⟨1, _⟩ | ⟨2, _⟩ | ⟨3, _⟩ | ⟨4, _⟩ | ⟨5, _⟩ =>
      simp [sourceControllerInput, TransferCircuit.sourceMemoryPins, StreamInterface.Pins.values,
        controllerOutput_eval, Expr.eval] <;> rfl
    | ⟨k+6, h⟩ => exact False.elim (by change k+6 < 6 at h; omega)

theorem destinationController_values (m : Hardware.Stream.Map wi wo) (i : Values (Input a wi wo))
    (s : Values (Register a wi wo)) :
    (fun {b} (p : StreamInterface.Input a wo b) => (destinationControllerInput m p).eval i s) =
      @TransferCircuit.destinationMemoryPins a wo
        ((TransferCircuit.circuit m).observe (controllerPins i s) (controlValues s)) := by
  funext b p
  cases p with
  | «at» k =>
    match k with
    | ⟨0, _⟩ | ⟨1, _⟩ | ⟨2, _⟩ | ⟨3, _⟩ | ⟨4, _⟩ | ⟨5, _⟩ =>
      simp [destinationControllerInput, TransferCircuit.destinationMemoryPins, StreamInterface.Pins.values,
        controllerOutput_eval, Expr.eval] <;> rfl
    | ⟨k+6, h⟩ => exact False.elim (by change k+6 < 6 at h; omega)

theorem sourcePins_eq (m : Hardware.Stream.Map wi wo) (i : Values (Input a wi wo))
    (s : Values (Register a wi wo)) :
    (fun {b} (p : StreamInterface.Input a wi b) => sourcePins m i s p) =
      (fun {b} (p : StreamInterface.Input a wi b) =>
        if hostMode.eval i s = 1 then sourceHostValues i s p else
          TransferCircuit.sourceMemoryPins ((TransferCircuit.circuit m).observe (controllerPins i s) (controlValues s)) p) := by
  funext b p
  by_cases h : hostMode.eval i s = 1
  · simp [sourcePins, sourceInput, Expr.eval, sourceHostValues, h]
  · simp only [sourcePins, sourceInput, Expr.eval, h, if_false]
    exact congrFun (congrFun (sourceController_values m i s) b) p

theorem destinationPins_eq (m : Hardware.Stream.Map wi wo) (i : Values (Input a wi wo))
    (s : Values (Register a wi wo)) :
    (fun {b} (p : StreamInterface.Input a wo b) => destinationPins m i s p) =
      (fun {b} (p : StreamInterface.Input a wo b) =>
        if hostMode.eval i s = 1 then destinationHostValues i s p else
          TransferCircuit.destinationMemoryPins ((TransferCircuit.circuit m).observe (controllerPins i s) (controlValues s)) p) := by
  funext b p
  by_cases h : hostMode.eval i s = 1
  · simp [destinationPins, destinationInput, Expr.eval, destinationHostValues, h]
  · simp only [destinationPins, destinationInput, Expr.eval, h, if_false]
    exact congrFun (congrFun (destinationController_values m i s) b) p

theorem controllerMemoryReset_eval (m : Hardware.Stream.Map wi wo) (i : Values (Input a wi wo))
    (s : Values (Register a wi wo)) :
    (controllerOutput m TransferInterface.memoryReset).eval i s = memoryReset.eval i s := rfl

theorem sourcePins_reset (m : Hardware.Stream.Map wi wo) (i : Values (Input a wi wo))
    (s : Values (Register a wi wo)) (hr : i reset = 1) : sourcePins m i s StreamInterface.reset = 1 := by
  simp [sourcePins, sourceInput, sourceHostInput, sourceControllerInput, StreamInterface.reset,
    Expr.eval, controllerMemoryReset_eval, memoryReset, Expr.bor, hr]

theorem destinationPins_reset (m : Hardware.Stream.Map wi wo) (i : Values (Input a wi wo))
    (s : Values (Register a wi wo)) (hr : i reset = 1) : destinationPins m i s StreamInterface.reset = 1 := by
  simp [destinationPins, destinationInput, destinationHostInput, destinationControllerInput, StreamInterface.reset,
    Expr.eval, controllerMemoryReset_eval, memoryReset, Expr.bor, hr]

def resetState (s : Values (Register a wi wo)) : TransferModel.State a wi wo :=
  TransferModel.initialState (StreamFlops.view (sourceValues s)).memory
    (StreamFlops.view (destinationValues s)).memory

/-- State-dependent reset recovery from arbitrary controller, memory, Q, and
pending bits. There is deliberately no fixed initial memory image. -/
theorem reset_eq (m : Hardware.Stream.Map wi wo) (i : Values (Input a wi wo))
    (s : Values (Register a wi wo)) (hr : i reset = 1) (r : Register a wi wo b) :
    (circuit m).step i s r = encode (resetState s) r := by
  cases r with
  | left r =>
    rw [controller_step]
    exact TransferCircuit.reset_eq m (controllerPins i s) (controlValues s) hr r
  | right r =>
    cases r with
    | left r =>
      rw [source_step]
      exact congrFun (congrFun (StreamFlops.reset_eq (sourcePins m i s) (sourceValues s)
        (sourcePins_reset m i s hr)) b) r
    | right r =>
      rw [destination_step]
      exact congrFun (congrFun (StreamFlops.reset_eq (destinationPins m i s) (destinationValues s)
        (destinationPins_reset m i s hr)) b) r

theorem reset_source_memory (m : Hardware.Stream.Map wi wo) (i : Values (Input a wi wo))
    (s : Values (Register a wi wo)) (hr : i reset = 1) (r : CommandFlops.Register a wi b) :
    (circuit m).step i s (.right (.left (.left r))) = s (.right (.left (.left r))) := by
  rw [source_step]
  exact StreamFlops.reset_memory (sourcePins m i s) (sourceValues s) (sourcePins_reset m i s hr) r

theorem reset_destination_memory (m : Hardware.Stream.Map wi wo) (i : Values (Input a wi wo))
    (s : Values (Register a wi wo)) (hr : i reset = 1) (r : CommandFlops.Register a wo b) :
    (circuit m).step i s (.right (.right (.left r))) = s (.right (.right (.left r))) := by
  rw [destination_step]
  exact StreamFlops.reset_memory (destinationPins m i s) (destinationValues s) (destinationPins_reset m i s hr) r

private theorem sourceMemoryPins_decode (rst : Bool) (o : TransferModel.Output a wo) :
    StreamInterface.decode (TransferCircuit.sourceMemoryPins (wi := wi) (TransferInterface.outputValues rst o)) =
      (⟨rst, o.sourceRead.map StreamModel.Request.read, o.sourceResponseReady⟩ : StreamModel.Input a wi) := by
  cases rst <;> cases h : o.sourceRead <;> cases hr : o.sourceResponseReady
  all_goals simp [StreamInterface.decode, TransferCircuit.sourceMemoryPins, StreamInterface.Pins.values,
    TransferInterface.outputValues, TransferInterface.memoryReset, TransferInterface.sourceRequestValid,
    TransferInterface.sourceRequestAddress, TransferInterface.sourceResponseReady,
    StreamInterface.reset, StreamInterface.valid, StreamInterface.write, StreamInterface.address,
    StreamInterface.ready, h, hr]

private theorem destinationMemoryPins_decode (rst : Bool) (o : TransferModel.Output a wo) :
    StreamInterface.decode (TransferCircuit.destinationMemoryPins (TransferInterface.outputValues rst o)) =
      (⟨rst, o.destinationWrite.map (fun (address, value) => StreamModel.Request.write address value), true⟩ : StreamModel.Input a wo) := by
  cases rst <;> cases h : o.destinationWrite
  all_goals simp [StreamInterface.decode, TransferCircuit.destinationMemoryPins, StreamInterface.Pins.values,
    TransferInterface.outputValues, TransferInterface.memoryReset, TransferInterface.destinationRequestValid,
    TransferInterface.destinationRequestAddress, TransferInterface.destinationRequestData,
    StreamInterface.reset, StreamInterface.valid, StreamInterface.write, StreamInterface.address,
    StreamInterface.data, StreamInterface.ready, h]
  all_goals rfl

theorem controller_outputs (m : Hardware.Stream.Map wi wo) (i : Values (Input a wi wo))
    (s : TransferModel.State a wi wo) (hr : i reset = 0) :
    (fun {b} (o : TransferInterface.Output a wo b) =>
      (TransferCircuit.circuit m).observe (controllerPins i (encode s)) (controlValues (encode s)) o) =
    (fun {b} (o : TransferInterface.Output a wo b) => TransferInterface.outputValues (decode i).reset
      (TransferModel.observe m (TransferModel.feedback (TransferHostModel.controllerInput (decode i) s) s) s.control) o) := by
  funext b o
  rw [controlValues_encode, TransferCircuit.output_eq]
  change TransferInterface.outputValues (TransferInterface.decode (controllerPins i (encode s))).reset
    (TransferModel.observe m (TransferInterface.decode (controllerPins i (encode s))) s.control) o = _
  rw [controller_decode i s hr]
  rfl

theorem sourcePins_decode (m : Hardware.Stream.Map wi wo) (i : Values (Input a wi wo))
    (s : TransferModel.State a wi wo) (hr : i reset = 0) :
    StreamInterface.decode (sourcePins m i (encode s)) =
      if s.control.phase == .idle && !TransferHostModel.acceptedStart (decode i) s then
        TransferHostModel.sourceInput (decode i)
      else TransferModel.sourceInput m (TransferHostModel.controllerInput (decode i) s) s := by
  rw [sourcePins_eq, hostMode_eval]
  cases hm : s.control.phase == .idle && !TransferHostModel.acceptedStart (decode i) s
  · simp only [BitVec.ofBool_false, show (0 : BitVec 1) ≠ 1 from by decide, if_false, Bool.false_eq_true]
    rw [controller_outputs m i s hr]
    exact sourceMemoryPins_decode (decode i).reset _
  · simp only [BitVec.ofBool_true, if_true]
    exact sourceHost_decode i (encode s)

theorem destinationPins_decode (m : Hardware.Stream.Map wi wo) (i : Values (Input a wi wo))
    (s : TransferModel.State a wi wo) (hr : i reset = 0) :
    StreamInterface.decode (destinationPins m i (encode s)) =
      if s.control.phase == .idle && !TransferHostModel.acceptedStart (decode i) s then
        TransferHostModel.destinationInput (decode i)
      else TransferModel.destinationInput m (TransferHostModel.controllerInput (decode i) s) s := by
  rw [destinationPins_eq, hostMode_eval]
  cases hm : s.control.phase == .idle && !TransferHostModel.acceptedStart (decode i) s
  · simp only [BitVec.ofBool_false, show (0 : BitVec 1) ≠ 1 from by decide, if_false, Bool.false_eq_true]
    rw [controller_outputs m i s hr]
    exact destinationMemoryPins_decode (decode i).reset _
  · simp only [BitVec.ofBool_true, if_true]
    exact destinationHost_decode i (encode s)

@[simp] theorem resetState_encode (s : TransferModel.State a wi wo) :
    resetState (encode s) = TransferModel.initialState s.source.memory s.destination.memory := by
  simp [resetState]

theorem step_eq (m : Hardware.Stream.Map wi wo) (i : Values (Input a wi wo))
    (s : TransferModel.State a wi wo) (hs : s.control.Valid) (r : Register a wi wo b) :
    (circuit m).step i (encode s) r = encode ((TransferHostInterface.spec m).step i s) r := by
  rcases BitVec.eq_zero_or_eq_one (i reset) with hr | hr
  · have hreset : (decode i).reset = false := by simp [decode, hr]
    cases r with
    | left r =>
      rw [controller_step, controlValues_encode, TransferCircuit.step_eq m _ _ hs]
      change TransferCircuit.encode (TransferModel.step (TransferInterface.decode (controllerPins i (encode s))) s.control) r =
        TransferCircuit.encode ((TransferHostModel.step m (decode i) s).control) r
      rw [controller_decode i s hr]
      unfold TransferHostModel.step
      split <;> rfl
    | right r =>
      cases r with
      | left r =>
        rw [source_step, sourceValues_encode, StreamFlops.step_eq]
        change StreamFlops.encode (StreamModel.step (StreamInterface.decode (sourcePins m i (encode s))) s.source) r =
          StreamFlops.encode ((TransferHostModel.step m (decode i) s).source) r
        rw [sourcePins_decode m i s hr]
        cases hp : s.control.phase <;> cases ha : TransferHostModel.acceptedStart (decode i) s
        all_goals simp [TransferHostModel.step, TransferModel.closedStep, hreset, hp, ha] <;> rfl
      | right r =>
        rw [destination_step, destinationValues_encode, StreamFlops.step_eq]
        change StreamFlops.encode (StreamModel.step (StreamInterface.decode (destinationPins m i (encode s))) s.destination) r =
          StreamFlops.encode ((TransferHostModel.step m (decode i) s).destination) r
        rw [destinationPins_decode m i s hr]
        cases hp : s.control.phase <;> cases ha : TransferHostModel.acceptedStart (decode i) s
        all_goals simp [TransferHostModel.step, TransferModel.closedStep, hreset, hp, ha] <;> rfl
  · rw [reset_eq m i (encode s) hr, resetState_encode]
    change _ = encode (TransferHostModel.step m (decode i) s) r
    rw [TransferHostModel.reset_state m (decode i) s (by simp [decode, hr])]

theorem sourceHostOutput_eq (i : Values (Input a wi wo)) (s : TransferModel.State a wi wo)
    (o : StreamInterface.Output wi b) :
    (sourceHostOutput o).eval i (encode s) = StreamInterface.outputValues
      ((StreamModel.component a wi).observe (TransferHostModel.sourceInput (decode i)) s.source) o := by
  rw [sourceHostOutput_eval, sourceValues_encode, StreamFlops.output_eq]
  change StreamInterface.outputValues ((StreamModel.component a wi).observe
    (StreamInterface.decode (sourceHostValues i (encode s))) s.source) o = _
  rw [sourceHost_decode]

theorem destinationHostOutput_eq (i : Values (Input a wi wo)) (s : TransferModel.State a wi wo)
    (o : StreamInterface.Output wo b) :
    (destinationHostOutput o).eval i (encode s) = StreamInterface.outputValues
      ((StreamModel.component a wo).observe (TransferHostModel.destinationInput (decode i)) s.destination) o := by
  rw [destinationHostOutput_eval, destinationValues_encode, StreamFlops.output_eq]
  change StreamInterface.outputValues ((StreamModel.component a wo).observe
    (StreamInterface.decode (destinationHostValues i (encode s))) s.destination) o = _
  rw [destinationHost_decode]

theorem output_eq (m : Hardware.Stream.Map wi wo) (i : Values (Input a wi wo))
    (s : TransferModel.State a wi wo) (o : Output wi wo b) :
    (circuit m).observe i (encode s) o = (TransferHostInterface.spec m).observe i s o := by
  cases o with
  | «at» k =>
    match k with
    | ⟨0, _⟩ | ⟨1, _⟩ | ⟨2, _⟩ | ⟨3, _⟩ | ⟨4, _⟩ | ⟨5, _⟩ |
      ⟨6, _⟩ | ⟨7, _⟩ | ⟨8, _⟩ | ⟨9, _⟩ =>
      all_goals simp only [Circuit.observe, circuit, Expr.eval]
      all_goals simp only [canStart_eval, controllerOutput_eval,
        controlValues_encode, TransferCircuit.output_eq, sourceHostOutput_eq, destinationHostOutput_eq]
      all_goals rcases BitVec.eq_zero_or_eq_one (i reset) with hr | hr <;>
        rcases BitVec.eq_zero_or_eq_one (i startValid) with hi | hi <;> cases hp : s.control.phase
      all_goals simp [TransferHostInterface.spec, outputValues, TransferHostModel.observe,
        TransferHostModel.sourceInput, TransferHostModel.destinationInput, TransferHostModel.startReady,
        StreamInterface.outputValues, StreamInterface.inReady, StreamInterface.outValid, StreamInterface.outData,
        StreamModel.component, StreamModel.machine, Hardware.Stream.Machine.component,
        TransferInterface.spec, TransferInterface.outputValues, TransferInterface.busy, TransferInterface.done,
        TransferInterface.error, TransferInterface.decode, TransferInterface.reset, TransferModel.observe,
        controllerPins, controllerInput, Expr.eval, phase, encode, TransferCircuit.encode,
        TransferCircuit.phaseBits, decode, hr, hi, hp]
      all_goals first | rfl | exact BitVec.allOnes_and
    | ⟨k+10, h⟩ => exact False.elim (by change k+10 < 10 at h; omega)

/-- Only controller validity is required. All memory contents, Q values, and
adapter pending bits are arbitrary; a transfer Session is a stronger contract
used separately for completion and transformed-copy correctness. -/
def implementation (m : Hardware.Stream.Map wi wo) :
    Implementation (circuit (a := a) m) (TransferHostInterface.spec m) where
  Valid := fun s => s.control.Valid
  encode := encode
  preserved i s h := TransferHostModel.control_valid m (decode i) s h
  step_eq i s h {_} r := step_eq m i s h r
  output_eq i s _ {_} o := output_eq m i s o

theorem trace_correct (m : Hardware.Stream.Map wi wo) (s : TransferModel.State a wi wo)
    (h : s.control.Valid) (inputs : List (Values (Input a wi wo))) :
    (circuit m).component.trace (encode s) inputs = (TransferHostInterface.spec m).trace s inputs :=
  (implementation m).trace_eq s h inputs

theorem trace_after_reset (m : Hardware.Stream.Map wi wo) (i : Values (Input a wi wo))
    (s : Values (Register a wi wo)) (hr : i reset = 1) (inputs : List (Values (Input a wi wo))) :
    (circuit m).component.trace ((circuit m).step i s) inputs =
      (TransferHostInterface.spec m).trace (resetState s) inputs := by
  have h := funext fun b => funext fun r => reset_eq m i s hr (b := b) r
  rw [h]
  apply trace_correct
  simp [resetState, TransferModel.initialState, TransferModel.initialControl,
    TransferModel.Control.Valid, TransferModel.emptyConfig]

theorem sourcePins_recovery (m : Hardware.Stream.Map wi wo) (i : Values (Input a wi wo))
    (s : Values (Register a wi wo)) (hp : s (.left .phase) = 3) :
    sourcePins m i s StreamInterface.reset = 1 := by
  simp [sourcePins, sourceInput, sourceControllerInput, StreamInterface.reset, hostMode,
    phase, Expr.eval, hp, controllerMemoryReset_eval, memoryReset, Expr.bor]

theorem destinationPins_recovery (m : Hardware.Stream.Map wi wo) (i : Values (Input a wi wo))
    (s : Values (Register a wi wo)) (hp : s (.left .phase) = 3) :
    destinationPins m i s StreamInterface.reset = 1 := by
  simp [destinationPins, destinationInput, destinationControllerInput, StreamInterface.reset, hostMode,
    phase, Expr.eval, hp, controllerMemoryReset_eval, memoryReset, Expr.bor]

def recoveryState (s : Values (Register a wi wo)) : TransferModel.State a wi wo :=
  { resetState s with control := { TransferModel.initialControl a with error := true } }

/-- Reserved-phase recovery cancels both pending responses without changing
words or Q. The next valid idle state reports an error, with reset priority. -/
theorem recovery_eq (m : Hardware.Stream.Map wi wo) (i : Values (Input a wi wo))
    (s : Values (Register a wi wo)) (hr : i reset = 0) (hp : s (.left .phase) = 3)
    (r : Register a wi wo b) : (circuit m).step i s r = encode (recoveryState s) r := by
  cases r with
  | left r =>
    rw [controller_step]
    exact TransferCircuit.recovery_eq m (controllerPins i s) (controlValues s) hr hp r
  | right r =>
    cases r with
    | left r =>
      rw [source_step]
      exact congrFun (congrFun (StreamFlops.reset_eq (sourcePins m i s) (sourceValues s)
        (sourcePins_recovery m i s hp)) b) r
    | right r =>
      rw [destination_step]
      exact congrFun (congrFun (StreamFlops.reset_eq (destinationPins m i s) (destinationValues s)
        (destinationPins_recovery m i s hp)) b) r

theorem reset_outputs (m : Hardware.Stream.Map wi wo) (i : Values (Input a wi wo))
    (s : Values (Register a wi wo)) (hr : i reset = 1) (o : Output wi wo b) :
    (circuit m).observe i s o = 0 := by
  have hs := StreamFlops.reset_outputs (sourceHostValues i s) (sourceValues s) hr
  have hd := StreamFlops.reset_outputs (destinationHostValues i s) (destinationValues s) hr
  cases o with
  | «at» k =>
    match k with
    | ⟨0, _⟩ =>
      change canStart.eval i s = (0 : BitVec 1)
      simp [canStart, Expr.eval, hr]
    | ⟨1, _⟩ =>
      change (controllerOutput m TransferInterface.busy).eval i s = (0 : BitVec 1)
      rw [controllerOutput_eval, TransferCircuit.reset_outputs m _ _ hr]
      rfl
    | ⟨2, _⟩ =>
      change (controllerOutput m TransferInterface.done).eval i s = (0 : BitVec 1)
      rw [controllerOutput_eval, TransferCircuit.reset_outputs m _ _ hr]
      rfl
    | ⟨3, _⟩ =>
      change (controllerOutput m TransferInterface.error).eval i s = (0 : BitVec 1)
      rw [controllerOutput_eval, TransferCircuit.reset_outputs m _ _ hr]
      rfl
    | ⟨4, _⟩ =>
      change (if (phase 0).eval i s = 1 then ~~~(i startValid) &&& (sourceHostOutput StreamInterface.inReady).eval i s else 0) = (0 : BitVec 1)
      rw [sourceHostOutput_eval, hs.1]
      simp
    | ⟨5, _⟩ =>
      change (if (phase 0).eval i s = 1 then (sourceHostOutput StreamInterface.outValid).eval i s else 0) = (0 : BitVec 1)
      rw [sourceHostOutput_eval, hs.2.1]
      simp
    | ⟨6, _⟩ =>
      change (if (phase 0).eval i s = 1 then (sourceHostOutput StreamInterface.outData).eval i s else 0) = (0 : BitVec wi)
      rw [sourceHostOutput_eval, hs.2.2]
      simp
    | ⟨7, _⟩ =>
      change (if (phase 0).eval i s = 1 then ~~~(i startValid) &&& (destinationHostOutput StreamInterface.inReady).eval i s else 0) = (0 : BitVec 1)
      rw [destinationHostOutput_eval, hd.1]
      simp
    | ⟨8, _⟩ =>
      change (if (phase 0).eval i s = 1 then (destinationHostOutput StreamInterface.outValid).eval i s else 0) = (0 : BitVec 1)
      rw [destinationHostOutput_eval, hd.2.1]
      simp
    | ⟨9, _⟩ =>
      change (if (phase 0).eval i s = 1 then (destinationHostOutput StreamInterface.outData).eval i s else 0) = (0 : BitVec wo)
      rw [destinationHostOutput_eval, hd.2.2]
      simp
    | ⟨k+10, h⟩ => exact False.elim (by change k+10 < 10 at h; omega)

theorem recovery_outputs (m : Hardware.Stream.Map wi wo) (i : Values (Input a wi wo))
    (s : Values (Register a wi wo)) (hp : s (.left .phase) = 3) (o : Output wi wo b) :
    (circuit m).observe i s o = 0 := by
  cases o with
  | «at» k =>
    match k with
    | ⟨0, _⟩ =>
      change canStart.eval i s = (0 : BitVec 1)
      simp [canStart, phase, Expr.eval, hp]
    | ⟨1, _⟩ =>
      change (controllerOutput m TransferInterface.busy).eval i s = (0 : BitVec 1)
      rw [controllerOutput_eval, TransferCircuit.recovery_outputs m _ _ hp]
      rfl
    | ⟨2, _⟩ =>
      change (controllerOutput m TransferInterface.done).eval i s = (0 : BitVec 1)
      rw [controllerOutput_eval, TransferCircuit.recovery_outputs m _ _ hp]
      rfl
    | ⟨3, _⟩ =>
      change (controllerOutput m TransferInterface.error).eval i s = (0 : BitVec 1)
      rw [controllerOutput_eval, TransferCircuit.recovery_outputs m _ _ hp]
      rfl
    | ⟨4, _⟩ =>
      change (if (phase 0).eval i s = 1 then ~~~(i startValid) &&& (sourceHostOutput StreamInterface.inReady).eval i s else 0) = (0 : BitVec 1)
      simp [phase, Expr.eval, hp]
    | ⟨5, _⟩ =>
      change (if (phase 0).eval i s = 1 then (sourceHostOutput StreamInterface.outValid).eval i s else 0) = (0 : BitVec 1)
      simp [phase, Expr.eval, hp]
    | ⟨6, _⟩ =>
      change (if (phase 0).eval i s = 1 then (sourceHostOutput StreamInterface.outData).eval i s else 0) = (0 : BitVec wi)
      simp [phase, Expr.eval, hp]
    | ⟨7, _⟩ =>
      change (if (phase 0).eval i s = 1 then ~~~(i startValid) &&& (destinationHostOutput StreamInterface.inReady).eval i s else 0) = (0 : BitVec 1)
      simp [phase, Expr.eval, hp]
    | ⟨8, _⟩ =>
      change (if (phase 0).eval i s = 1 then (destinationHostOutput StreamInterface.outValid).eval i s else 0) = (0 : BitVec 1)
      simp [phase, Expr.eval, hp]
    | ⟨9, _⟩ =>
      change (if (phase 0).eval i s = 1 then (destinationHostOutput StreamInterface.outData).eval i s else 0) = (0 : BitVec wo)
      simp [phase, Expr.eval, hp]
    | ⟨k+10, h⟩ => exact False.elim (by change k+10 < 10 at h; omega)

theorem trace_after_recovery (m : Hardware.Stream.Map wi wo) (i : Values (Input a wi wo))
    (s : Values (Register a wi wo)) (hr : i reset = 0) (hp : s (.left .phase) = 3)
    (inputs : List (Values (Input a wi wo))) :
    (circuit m).component.trace ((circuit m).step i s) inputs =
      (TransferHostInterface.spec m).trace (recoveryState s) inputs := by
  have h := funext fun b => funext fun r => recovery_eq m i s hr hp (b := b) r
  rw [h]
  apply trace_correct
  simp [recoveryState, TransferModel.initialControl, TransferModel.Control.Valid, TransferModel.emptyConfig]

end Pinwheel.Hardware.Memory.TransferHostCircuit
