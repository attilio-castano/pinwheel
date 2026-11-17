import Pinwheel.Hardware.Processor.SerialCircuit
import Pinwheel.Hardware.Processor.MmioCircuitProofs
import Pinwheel.Hardware.Uart.CircuitProofs

namespace Pinwheel.Hardware.Processor.SerialInterface
set_option backward.isDefEq.respectTransparency false

theorem ofBool_beq (b : Bool) : (BitVec.ofBool b == 1) = b := by cases b <;> rfl

theorem cpu_decode (i : Values Input) : MmioInterface.decode (cpuPins i) = SerialModel.cpuInput (decode i) := rfl

theorem mmio_decode (d : Uart.Timing) (i : Values Input) (s : SerialModel.State) :
    MmioInterface.decode (mmioPins d i s) = SerialModel.mmioInput d (decode i) s := by
  let o := Uart.observe d (SerialModel.uartInput (decode i) s) s.uart
  change MmioModel.Input.mk (i reset == 1) (decode i).operation (i gpioInput)
    (BitVec.ofBool o.complete == 1)
    (if BitVec.ofBool o.arrival.isSome = 1 then some (o.arrival.getD 0) else none)
    (BitVec.ofBool o.framingError == 1) =
    ⟨i reset == 1,(decode i).operation,i gpioInput,o.complete,o.arrival,o.framingError⟩
  rw [ofBool_beq,ofBool_beq]
  cases o.arrival <;> rfl

theorem mmio_admitted (d : Uart.Timing) (i : Values Input) (s : SerialModel.State) :
    MmioInterface.Admitted (mmioPins d i s) ↔ Admitted i := Iff.rfl

end Pinwheel.Hardware.Processor.SerialInterface

namespace Pinwheel.Hardware.Processor.SerialCircuit
open SerialInterface
set_option backward.isDefEq.respectTransparency false

theorem cpu_input_eval (i : Values Input) (s : Values (Register d)) (p : MmioInterface.Input b) :
    (cpuInput p).eval i s = cpuPins i p := by
  match p with
  | .at ⟨0,_⟩ | .at ⟨1,_⟩ | .at ⟨2,_⟩ | .at ⟨3,_⟩ | .at ⟨4,_⟩ | .at ⟨5,_⟩ |
    .at ⟨6,_⟩ | .at ⟨7,_⟩ | .at ⟨8,_⟩ | .at ⟨9,_⟩ | .at ⟨10,_⟩ => rfl
  | .at ⟨k+11,h⟩ => change k+11 < 11 at h; omega

theorem start_eval (i : Values Input) (s : Values (Register d)) :
    txStart.eval i s = MmioCircuit.txStart.eval (cpuPins i) (mmioState s) := by
  simp only [txStart,Expr.eval_bind,cpu_input_eval,Expr.eval]
  rfl

theorem uart_decode (i : Values Input) (s : Values (Register d)) :
    Uart.Physical.decode (uartPins i s) = SerialModel.uartInput (decode i) (view s) := by
  have cpu := congrArg MmioModel.State.tx (MmioCircuit.cpuView_eq (cpuPins i) (mmioState s))
  rw [cpu_decode] at cpu
  change (MmioCircuit.cpuView (cpuPins i) (mmioState s)).tx =
    (SerialModel.cpuState (decode i) (view s)).tx at cpu
  change Uart.Input.mk _ _ _ = Uart.Input.mk _ _ _
  congr 1
  change (if _ = 1 then some _ else none) = (SerialModel.cpuState (decode i) (view s)).tx
  rw [← cpu]
  rcases BitVec.eq_zero_or_eq_one (MmioCircuit.txStart.eval (cpuPins i) (mmioState s)) with hs | hs
  all_goals rcases BitVec.eq_zero_or_eq_one (mmioState s MmioCircuit.txActiveReg) with ht | ht
  all_goals change s (mmio MmioCircuit.txActiveReg) = _ at ht
  all_goals simp [uartPins,Uart.Physical.txValid,Uart.Physical.txData,uartInput,Stream.eval_bor,Expr.eval,
    start_eval,MmioCircuit.cpuView,MmioCircuit.view,mmioState,cpuPins,MmioInterface.data,hs,ht]

theorem uart_output_eval (i : Values Input) (s : Values (Register d))
    (hs : Uart.Structural.Valid d (uartState s)) (o : Uart.Physical.Output b) :
    (uartOutput d o).eval i s =
      Uart.Physical.outputValues (Uart.observe d (SerialModel.uartInput (decode i) (view s)) (view s).uart) o := by
  simp only [uartOutput,Expr.eval_bind,Expr.eval]
  change (Uart.Structural.circuit d).observe (uartPins i s) (uartState s) o = _
  rw [Uart.Structural.output_eq d _ _ hs]
  simp only [Uart.Physical.spec,uart_decode]
  rfl

theorem mmio_input_eval (i : Values Input) (s : Values (Register d))
    (hs : Uart.Structural.Valid d (uartState s)) (p : MmioInterface.Input b) :
    boundMmioPins d i s p = SerialInterface.mmioPins d i (view s) p := by
  match p with
  | .at ⟨0,_⟩ | .at ⟨1,_⟩ | .at ⟨2,_⟩ | .at ⟨3,_⟩ | .at ⟨4,_⟩ | .at ⟨5,_⟩ |
    .at ⟨6,_⟩ => rfl
  | .at ⟨7,_⟩ => exact uart_output_eval i s hs Uart.Physical.txComplete
  | .at ⟨8,_⟩ => exact uart_output_eval i s hs Uart.Physical.rxValid
  | .at ⟨9,_⟩ => exact uart_output_eval i s hs Uart.Physical.rxData
  | .at ⟨10,_⟩ => exact uart_output_eval i s hs Uart.Physical.framingError
  | .at ⟨k+11,h⟩ => change k+11 < 11 at h; omega

/-- Exact component register equations, including retained inactive metadata.
These hold for every raw state, before imposing the UART counter invariant. -/
theorem step_mmio (i : Values Input) (s : Values (Register d)) (r : MmioCircuit.Register b) :
    (circuit d).step i s (mmio r) = MmioCircuit.circuit.step (boundMmioPins d i s) (mmioState s) r := by
  simp only [Circuit.step,circuit,mmio,Expr.eval_bind,Expr.eval]
  rfl

theorem step_uart (i : Values Input) (s : Values (Register d)) (r : Uart.Structural.Register d b) :
    (circuit d).step i s (uart r) = (Uart.Structural.circuit d).step (uartPins i s) (uartState s) r := by
  simp only [Circuit.step,circuit,uart,Expr.eval_bind,Expr.eval]
  rfl

theorem mmio_state_step (i : Values Input) (s : Values (Register d)) :
    @Eq (Values MmioCircuit.Register) (mmioState ((circuit d).step i s))
      (MmioCircuit.circuit.step (boundMmioPins d i s) (mmioState s)) := by
  funext b r
  exact step_mmio i s r

theorem uart_state_step (i : Values Input) (s : Values (Register d)) :
    @Eq (Values (Uart.Structural.Register d)) (uartState ((circuit d).step i s))
      ((Uart.Structural.circuit d).step (uartPins i s) (uartState s)) := by
  funext b r
  exact step_uart i s r

theorem output_mmio (i : Values Input) (s : Values (Register d)) (o : MmioInterface.Output b) :
    (circuit d).observe i s (.left o) = MmioCircuit.circuit.observe (boundMmioPins d i s) (mmioState s) o := by
  simp only [Circuit.observe,circuit,Expr.eval_bind,Expr.eval]
  rfl

theorem view_step (i : Values Input) (s : Values (Register d))
    (hs : Uart.Structural.Valid d (uartState s)) :
    view ((circuit d).step i s) = SerialModel.step d (decode i) (view s) := by
  change SerialModel.State.mk _ _ = SerialModel.State.mk _ _
  congr 1
  · rw [mmio_state_step,MmioCircuit.view_step]
    have hp := funext fun b => funext fun p => mmio_input_eval i s hs (b := b) p
    rw [hp]
    simp only [MmioInterface.spec,SerialInterface.mmio_decode]
    rfl
  · rw [uart_state_step,Uart.Structural.view_step d _ _ hs]
    simp only [Uart.Physical.spec,uart_decode]
    rfl

theorem output_eq (i : Values Input) (s : Values (Register d))
    (hs : Uart.Structural.Valid d (uartState s)) (o : Output b) :
    (circuit d).observe i s o = outputValues d i (view s) o := by
  cases o with
  | left o =>
    rw [output_mmio,MmioCircuit.output_eq]
    have hp := funext fun b => funext fun p => mmio_input_eval i s hs (b := b) p
    rw [hp]
    rfl
  | right o => exact uart_output_eval i s hs o

theorem valid_step (i : Values Input) (s : Values (Register d)) (hs : Valid d s) :
    Valid d ((circuit d).step i s) := by
  constructor
  · rw [uart_state_step]
    exact Uart.Structural.valid_step d _ _
  · rw [view_step i s hs.1]
    exact SerialModel.step_owned d (decode i) (view s) hs.2

theorem reset_eq (i : Values Input) (s : Values (Register d)) (hr : i reset = 1) (r : Register d b) :
    (circuit d).step i s r = 0 := by
  cases r with
  | left r => exact (step_mmio i s r).trans (MmioCircuit.reset_eq _ _ hr r)
  | right r => exact (step_uart i s r).trans (Uart.Structural.reset_eq d _ _ hr r)

theorem reset_view (i : Values Input) (s : Values (Register d)) (hr : i reset = 1) :
    view ((circuit d).step i s) = SerialModel.initial := by
  change SerialModel.State.mk _ _ = _
  rw [mmio_state_step,uart_state_step,MmioCircuit.reset_view _ _ hr,Uart.Structural.reset_view d _ _ hr]
  rfl

theorem reset_valid (i : Values Input) (s : Values (Register d)) (hr : i reset = 1) :
    Valid d ((circuit d).step i s) := by
  constructor
  · rw [uart_state_step]
    exact Uart.Structural.valid_step d _ _
  · rw [reset_view i s hr]
    exact (SerialModel.initial_valid d).1

def resetValues : Values Output := Stream.Joint.values (fun _ => 0)
  (Uart.Physical.outputValues ⟨true,false,false,none,false⟩)

theorem reset_outputs (i : Values Input) (s : Values (Register d)) (hr : i reset = 1) (o : Output b) :
    (circuit d).observe i s o = resetValues o := by
  cases o with
  | left o => exact (output_mmio i s o).trans (MmioCircuit.reset_outputs _ _ hr o)
  | right o =>
    change (uartOutput d o).eval i s = _
    simp only [uartOutput,Expr.eval_bind,Expr.eval]
    exact Uart.Structural.reset_outputs d (uartPins i s) (uartState s) hr o

theorem view_valid (s : Values (Register d)) (hs : Valid d s) : SerialModel.Valid d (view s) :=
  ⟨hs.2,Uart.Structural.view_valid d _ hs.1⟩

theorem view_encode (s : SerialModel.State) (hs : Uart.Valid d s.uart) : view (encode d s) = s := by
  change SerialModel.State.mk (MmioCircuit.view (MmioCircuit.encode s.mmio))
    (Uart.Structural.view (Uart.Structural.encode d s.uart)) = s
  rw [MmioCircuit.view_encode,Uart.Structural.view_encode d s.uart hs]

theorem encode_valid (s : SerialModel.State) (hs : SerialModel.Valid d s) : Valid d (encode d s) := by
  constructor
  · exact Uart.Structural.encode_valid d s.uart hs.2
  · rw [view_encode s hs.2]
    exact hs.1

theorem coverage (s : SerialModel.State) (hs : SerialModel.Valid d s) :
    ∃ raw : Values (Register d), Valid d raw ∧ view raw = s :=
  ⟨encode d s,encode_valid s hs,view_encode s hs.2⟩

def implementation (d : Uart.Timing) : DecodedImplementation (circuit d) (spec d) where
  Valid := Valid d
  view := view
  preserved := valid_step
  step_eq i s h := view_step i s h.1
  output_eq i s h {_} o := output_eq i s h.1 o

def resetCertificate (d : Uart.Timing) : (implementation d).Reset reset where
  initial _ := SerialModel.initial
  reset_valid := reset_valid
  reset_view := reset_view

theorem trace_eq (s : Values (Register d)) (hs : Valid d s) (traffic : List (Values Input)) :
    (circuit d).component.trace s traffic = (spec d).trace (view s) traffic :=
  (implementation d).trace_eq s hs traffic

theorem run_eq (s : Values (Register d)) (hs : Valid d s) (traffic : List (Values Input)) :
    view ((circuit d).component.run s traffic) = (spec d).run (view s) traffic :=
  (implementation d).run_eq s hs traffic

theorem trace_after_reset (i : Values Input) (s : Values (Register d)) (hr : i reset = 1)
    (traffic : List (Values Input)) :
    (circuit d).component.trace ((circuit d).step i s) traffic = (spec d).trace SerialModel.initial traffic :=
  (resetCertificate d).trace_after_reset (implementation d) reset i s hr traffic

theorem run_after_reset (i : Values Input) (s : Values (Register d)) (hr : i reset = 1)
    (traffic : List (Values Input)) :
    view ((circuit d).component.run ((circuit d).step i s) traffic) = (spec d).run SerialModel.initial traffic :=
  (resetCertificate d).run_after_reset (implementation d) reset i s hr traffic

theorem bound_admitted (i : Values Input) (s : Values (Register d)) :
    MmioInterface.Admitted (boundMmioPins d i s) ↔ Admitted i := Iff.rfl

def observedResponse (d : Uart.Timing) (i : Values Input) (s : Values (Register d)) : Option MmioModel.Response :=
  if (circuit d).observe i s (.left MmioInterface.responseValid) = 1 then
    MmioCircuit.decodeResponse ((circuit d).observe i s (.left MmioInterface.responseCode))
      ((circuit d).observe i s (.left MmioInterface.responseData)) else none

theorem observedResponse_mmio (i : Values Input) (s : Values (Register d)) :
    observedResponse d i s = MmioCircuit.observedResponse (boundMmioPins d i s) (mmioState s) := by
  simp only [observedResponse,MmioCircuit.observedResponse,output_mmio]

theorem observedResponse_eq (i : Values Input) (s : Values (Register d))
    (hs : Uart.Structural.Valid d (uartState s)) :
    observedResponse d i s = MmioInterface.response (SerialInterface.mmioPins d i (view s)) (view s).mmio := by
  rw [observedResponse_mmio,MmioCircuit.observedResponse_eq]
  have hp := funext fun b => funext fun p => mmio_input_eval i s hs (b := b) p
  rw [hp]
  rfl

/-- Code3's fault is observable for every raw state, including malformed UART
counters; it is never transported as a legitimate typed MMIO request. -/
theorem invalid_response (i : Values Input) (s : Values (Register d))
    (hr : i reset ≠ 1) (hi : invalid i) : observedResponse d i s = some (.fault .registerHole) := by
  rw [observedResponse_mmio,MmioCircuit.observedResponse_eq]
  exact MmioInterface.invalid_response _ _ hr hi

theorem invalid_operation (i : Values Input) (hi : invalid i) : (decode i).operation = none :=
  MmioInterface.invalid_operation (cpuPins i) hi

theorem observedResponse_admitted (i : Values Input) (s : Values (Register d))
    (hs : Uart.Structural.Valid d (uartState s)) (hi : Admitted i) :
    observedResponse d i s = (SerialModel.observe d (decode i) (view s)).response := by
  rw [observedResponse_eq i s hs,MmioInterface.response_admitted _ _ ((mmio_admitted d i _).mpr hi)]
  simp only [SerialInterface.mmio_decode]
  rfl

/-- Fixed extraction uses the actual response pins and actual UART-driven MMIO
pins. The admitted-input boundary is required only for typed event transport. -/
def physicalEvents (d : Uart.Timing) (i : Values Input) (s : Values (Register d)) : List MmioModel.Event :=
  let p : Values MmioInterface.Input := boundMmioPins d i s
  let m := MmioInterface.decode p
  if m.reset then [.reset] else
    m.operation.toList.map (fun r => .cpu r (p MmioInterface.gpioInput)
      ((observedResponse d i s).getD (.fault .registerHole))) ++
    MmioModel.autonomousEvents m (view s).mmio (MmioModel.cpuState m (view s).mmio)

theorem physicalEvents_mmio (i : Values Input) (s : Values (Register d)) :
    physicalEvents d i s = MmioCircuit.physicalEvents (boundMmioPins d i s) (mmioState s) := by
  simp only [physicalEvents,MmioCircuit.physicalEvents,observedResponse_mmio]
  rfl

theorem physicalEvents_eq (i : Values Input) (s : Values (Register d))
    (hs : Uart.Structural.Valid d (uartState s)) (hi : Admitted i) :
    physicalEvents d i s = SerialModel.deviceEvents d (decode i) (view s) := by
  rw [physicalEvents_mmio,MmioCircuit.physicalEvents_eq _ _ ((bound_admitted i s).mpr hi)]
  have hp := funext fun b => funext fun p => mmio_input_eval i s hs (b := b) p
  rw [hp,SerialInterface.mmio_decode]
  rfl

def eventRefinement (d : Uart.Timing) : Timed.EventRefinement (circuit d).component MmioModel.eventSpec
    (physicalEvents d) (fun i _ => Admitted i) where
  Rel raw logical := Valid d raw ∧ (view raw).mmio = logical
  edge i s logical related hi := by
    rcases related with ⟨hs,rfl⟩
    refine ⟨(view ((circuit d).step i s)).mmio, ?_,valid_step i s hs,rfl⟩
    rw [physicalEvents_eq i s hs.1 hi,view_step i s hs.1]
    exact MmioModel.replay_path (MmioModel.replay_events (SerialModel.mmioInput d (decode i) (view s)) (view s).mmio)

theorem event_coverage (d : Uart.Timing) :
    (eventRefinement d).InitialCoverage (Valid d) (fun _ => True) where
  nonempty := ⟨encode d SerialModel.initial,encode_valid _ (SerialModel.initial_valid d)⟩
  covered raw h := ⟨(view raw).mmio,trivial,h,rfl⟩

theorem event_replay_history (s : Values (Register d)) (hs : Valid d s) (traffic : List (Values Input))
    (legal : (circuit d).component.Legal (fun i _ => Admitted i) s traffic) :
    MmioModel.replay (view s).mmio ((circuit d).component.eventTrace (physicalEvents d) s traffic) =
      some (view ((circuit d).component.run s traffic)).mmio := by
  obtain ⟨last,path,related⟩ := (eventRefinement d).trace s (view s).mmio traffic ⟨hs,rfl⟩ legal
  have result := MmioCircuit.replay_of_path path
  change Valid d _ ∧ (view _).mmio = last at related
  simpa only [related.2] using result

theorem reset_events (i : Values Input) (s : Values (Register d)) (hr : i reset = 1) :
    physicalEvents d i s = [.reset] := by
  simp only [physicalEvents]
  have hm : (MmioInterface.decode (boundMmioPins d i s)).reset = true := by
    change (i reset == 1) = true
    simp [hr]
  simp only [hm,ite_true]

theorem events_after_reset (i : Values Input) (s : Values (Register d)) (hr : i reset = 1)
    (traffic : List (Values Input))
    (legal : (circuit d).component.Legal (fun j _ => Admitted j) ((circuit d).step i s) traffic) :
    MmioModel.replay MmioModel.initial
      ((circuit d).component.eventTrace (physicalEvents d) ((circuit d).step i s) traffic) =
      some (view ((circuit d).component.run ((circuit d).step i s) traffic)).mmio := by
  have result := event_replay_history ((circuit d).step i s) (reset_valid i s hr) traffic legal
  rw [reset_view i s hr] at result
  exact result

end Pinwheel.Hardware.Processor.SerialCircuit
