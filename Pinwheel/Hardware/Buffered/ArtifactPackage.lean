import Pinwheel.Hardware.Buffered.SerialPackage
import Pinwheel.Hardware.Memory.SinglePort

/-! Conditional composition of independently interpreted frontend/controller
components with two explicit single-port digital memory contracts. Actual RTL
wiring certificates are a separate obligation; this module does not claim that
defining the matching composition interprets a particular Verilog wrapper. -/
namespace Pinwheel.Hardware.Buffered.ArtifactPackage
open Pinwheel.Hardware

structure Behavior (I R O : Nat → Type) where
  step : Values I → Values R → Values R
  observe : Values I → Values R → Values O

def Behavior.ofCircuit (circuit : Circuit I R O) : Behavior I R O :=
  ⟨fun i r => circuit.step i r, fun i r => circuit.observe i r⟩

structure Components where
  frontend : Behavior Serial.Input Serial.Register Serial.Output
  controller : Behavior Sram.Input Sram.Register Sram.Output

structure Correct (components : Components) : Prop where
  frontend_step : ∀ (i : Values Serial.Input) (r : Values Serial.Register) {w}
    (port : Serial.Register w), components.frontend.step i r port = Serial.circuit.step i r port
  frontend_observe : ∀ (i : Values Serial.Input) (r : Values Serial.Register) {w}
    (port : Serial.Output w), components.frontend.observe i r port = Serial.circuit.observe i r port
  controller_step : ∀ (i : Values Sram.Input) (r : Values Sram.Register) {w}
    (port : Sram.Register w), components.controller.step i r port = Sram.circuit.step i r port
  controller_observe : ∀ (i : Values Sram.Input) (r : Values Sram.Register) {w}
    (port : Sram.Output w), components.controller.observe i r port = Sram.circuit.observe i r port

def command (controller : Behavior Sram.Input Sram.Register Sram.Output)
    (i : Values Sram.Input) (r : Values Sram.Register) (port : Bool) :
    Memory.SinglePort.Command 6 64 :=
  if controller.observe i r (.port .write) = 1 then
    .write (controller.observe i r (.port (.address port))) (controller.observe i r (.port .data))
  else if controller.observe i r (.port .read) = 1 then
    .read (controller.observe i r (.port (.address port)))
  else .idle

private theorem no_write (contents : Memory.Contents 6 64) (address : BitVec 6)
    (data : BitVec 64) : contents.write ⟨false, address, data⟩ = contents :=
  Memory.write_disabled _ _ rfl

theorem memory_step {M : Type} (memory : Memory.SinglePort.Contract M 6 64)
    (i : Values Sram.Input) (r : Values Sram.Register) (arrays : Fin 2 → M) :
    (fun port => memory.view (memory.advance
      (command (.ofCircuit Sram.circuit) i r (decide (port = 1))) (arrays port))) =
      Memory.Sram.step (Sram.arrayRequest i r) (fun port => memory.view (arrays port)) := by
  funext port
  rw [memory.correct]
  by_cases write : (Sram.request .write).eval i r = 1
  case pos =>
    simp only [command, Behavior.ofCircuit, Circuit.observe, Sram.circuit, Sram.output, write,
      ↓reduceIte, Memory.SinglePort.step, Memory.Sram.step, Memory.Sram.State.step,
      Sram.arrayRequest, decide_true, Sram.request_address_write _ i r write]
    done
  case neg =>
    have zero : (Sram.request .write).eval i r = 0 := by bv_omega
    have read : (Sram.request .read).eval i r = 1 := by
      simpa [zero] using Sram.request_read_write_exclusive i r
    simp only [command, Behavior.ofCircuit, Circuit.observe, Sram.circuit, Sram.output, write, read,
      ↓reduceIte, Memory.SinglePort.step, Memory.Sram.step, Memory.Sram.State.step,
      Sram.arrayRequest, decide_false, no_write, Bool.false_eq_true]
    done

structure State (M : Type) where
  frontend : Values Serial.Register
  controller : Values Sram.Register
  arrays : Fin 2 → M

def State.view {M : Type} (memory : Memory.SinglePort.Contract M 6 64) (s : State M) :
    SerialPackage.State :=
  ⟨s.frontend, ⟨s.controller, fun port => memory.view (s.arrays port)⟩⟩

def State.coreInputs {M : Type} (components : Components) (s : State M)
    (p : SerialPackage.Pins) : Values Reactive.Input :=
  fun port => components.frontend.observe (p.inputs (fun _ => 0)).values s.frontend (.core port)

def State.controllerInputs {M : Type} (components : Components)
    (memory : Memory.SinglePort.Contract M 6 64) (s : State M)
    (p : SerialPackage.Pins) : Values Sram.Input
  | _, .base port => s.coreInputs components p port
  | _, .q port => (memory.view (s.arrays (SramState.port port))).q

def State.status {M : Type} (components : Components)
    (memory : Memory.SinglePort.Contract M 6 64) (s : State M)
    (p : SerialPackage.Pins) : Values Reactive.Output :=
  fun port => components.controller.observe (s.controllerInputs components memory p) s.controller (.base port)

def State.frontendInputs {M : Type} (components : Components)
    (memory : Memory.SinglePort.Contract M 6 64) (s : State M)
    (p : SerialPackage.Pins) : Values Serial.Input :=
  (p.inputs (s.status components memory p)).values

def State.step {M : Type} (components : Components)
    (memory : Memory.SinglePort.Contract M 6 64) (s : State M)
    (p : SerialPackage.Pins) : State M :=
  ⟨components.frontend.step (s.frontendInputs components memory p) s.frontend,
    components.controller.step (s.controllerInputs components memory p) s.controller,
    fun port => memory.advance (command components.controller
      (s.controllerInputs components memory p) s.controller (decide (port = 1))) (s.arrays port)⟩

def State.observe {M : Type} (components : Components)
    (memory : Memory.SinglePort.Contract M 6 64) (s : State M)
    (p : SerialPackage.Pins) : {w : Nat} → SerialPackage.Output w → BitVec w
  | _, .miso => components.frontend.observe (s.frontendInputs components memory p) s.frontend .miso
  | _, .ready => components.frontend.observe (s.frontendInputs components memory p) s.frontend .ready
  | _, .busy => s.status components memory p .busy
  | _, .levels => s.status components memory p .levels
  | _, .enabled => s.status components memory p .enabled

def State.run {M : Type} (components : Components)
    (memory : Memory.SinglePort.Contract M 6 64) (s : State M)
    (pins : List SerialPackage.Pins) : State M :=
  pins.foldl (fun state pin => state.step components memory pin) s

theorem State.coreInputs_eq {M : Type} {components : Components} (correct : Correct components)
    (memory : Memory.SinglePort.Contract M 6 64) (s : State M) (p : SerialPackage.Pins) :
    (s.coreInputs components p : Values Reactive.Input) =
      ((s.view memory).coreInputs p : Values Reactive.Input) := by
  funext w port
  simp only [State.coreInputs, correct.frontend_observe, SerialPackage.State.coreInputs,
    Circuit.observe, Serial.circuit, Serial.output, State.view]
  done

theorem State.controllerInputs_eq {M : Type} {components : Components} (correct : Correct components)
    (memory : Memory.SinglePort.Contract M 6 64) (s : State M) (p : SerialPackage.Pins) :
    (s.controllerInputs components memory p : Values Sram.Input) =
      ((s.view memory).controller.inputs ((s.view memory).coreInputs p) : Values Sram.Input) := by
  funext w port
  cases port
  all_goals simp only [State.controllerInputs, SramState.State.inputs,
    State.coreInputs_eq correct memory s p, State.view]
  done

theorem State.status_eq {M : Type} {components : Components} (correct : Correct components)
    (memory : Memory.SinglePort.Contract M 6 64) (s : State M) (p : SerialPackage.Pins) :
    (s.status components memory p : Values Reactive.Output) =
      ((s.view memory).status p : Values Reactive.Output) := by
  funext w port
  simp only [State.status, correct.controller_observe, State.controllerInputs_eq correct,
    SerialPackage.State.status, SramState.State.observe, State.view]
  done

theorem State.frontendInputs_eq {M : Type} {components : Components} (correct : Correct components)
    (memory : Memory.SinglePort.Contract M 6 64) (s : State M) (p : SerialPackage.Pins) :
    (s.frontendInputs components memory p : Values Serial.Input) =
      (((s.view memory).inputs p).values : Values Serial.Input) := by
  simp only [State.frontendInputs, State.status_eq correct, SerialPackage.State.inputs]
  done

theorem Correct.frontend_step_values {components : Components} (correct : Correct components)
    (i : Values Serial.Input) (r : Values Serial.Register) :
    (components.frontend.step i r : Values Serial.Register) =
      (Serial.circuit.step i r : Values Serial.Register) :=
  funext fun _ => funext fun port => correct.frontend_step i r port

theorem Correct.controller_step_values {components : Components} (correct : Correct components)
    (i : Values Sram.Input) (r : Values Sram.Register) :
    (components.controller.step i r : Values Sram.Register) =
      (Sram.circuit.step i r : Values Sram.Register) :=
  funext fun _ => funext fun port => correct.controller_step i r port

theorem Correct.command_eq {components : Components} (correct : Correct components)
    (i : Values Sram.Input) (r : Values Sram.Register) (port : Bool) :
    command components.controller i r port = command (.ofCircuit Sram.circuit) i r port := by
  simp only [command, correct.controller_observe, Behavior.ofCircuit]
  rfl
  done

theorem State.view_step {M : Type} {components : Components} (correct : Correct components)
    (memory : Memory.SinglePort.Contract M 6 64) (s : State M) (p : SerialPackage.Pins) :
    (s.step components memory p).view memory = (s.view memory).step p := by
  simp only [State.step, State.frontendInputs_eq correct, State.controllerInputs_eq correct,
    correct.frontend_step_values, correct.controller_step_values, correct.command_eq,
    State.view, memory_step, SerialPackage.State.step, SramState.State.step]
  done

theorem State.view_observe {M : Type} {components : Components} (correct : Correct components)
    (memory : Memory.SinglePort.Contract M 6 64) (s : State M) (p : SerialPackage.Pins)
    (output : SerialPackage.Output w) :
    s.observe components memory p output = (s.view memory).observe p output := by
  cases output
  all_goals simp only [State.observe, State.frontendInputs_eq correct, correct.frontend_observe,
    State.status_eq correct, SerialPackage.State.observe]
  all_goals rfl
  done

theorem State.view_run {M : Type} {components : Components} (correct : Correct components)
    (memory : Memory.SinglePort.Contract M 6 64) (s : State M) (pins : List SerialPackage.Pins) :
    (s.run components memory pins).view memory = (s.view memory).run pins := by
  induction pins generalizing s
  case nil => rfl
  case cons pin rest ih =>
    change (State.run components memory (s.step components memory pin) rest).view memory =
      ((s.view memory).step pin).run rest
    rw [ih, State.view_step correct]
    done
  done

end Pinwheel.Hardware.Buffered.ArtifactPackage
