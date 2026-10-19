import Pinwheel.Hardware.Buffered.SerialCorrespondence
import Pinwheel.Hardware.Buffered.SramState

/-! The sampled-pin product of the actual serial frontend and actual closed-loop
digital SRAM controller. Both components step once from their pre-edge states.
Core-facing serial ports do not depend on status, so the status feedback has no
combinational cycle. This models the frozen wrapper wiring; it is not an RTL
emitter or analog-memory equivalence claim. -/
namespace Pinwheel.Hardware.Buffered.SerialPackage
open Pinwheel.Hardware

structure Pins where
  cold : Bool := false
  sck : Bool := false
  mosi : Bool := false
  csn : Bool := true
  rawInputs : BitVec 2 := 0
  deriving DecidableEq, Repr

def Pins.inputs (p : Pins) (status : Values Reactive.Output) : Serial.Inputs :=
  ⟨p.cold, p.sck, p.mosi, p.csn, p.rawInputs, status⟩

structure State where
  frontend : Values Serial.Register
  controller : SramState.State

theorem coreInput_status_independent (p : Pins) (r : Values Serial.Register)
    (status₁ status₂ : Values Reactive.Output) (port : Reactive.Input w) :
    (Serial.coreInput port).eval (p.inputs status₁).values r =
      (Serial.coreInput port).eval (p.inputs status₂).values r := by
  cases port <;> rfl
  done

def State.coreInputs (s : State) (p : Pins) : Values Reactive.Input :=
  fun port => (Serial.coreInput port).eval (p.inputs (fun _ => 0)).values s.frontend

def State.status (s : State) (p : Pins) : Values Reactive.Output :=
  fun output => s.controller.observe (s.coreInputs p) output

def State.inputs (s : State) (p : Pins) : Serial.Inputs := p.inputs (s.status p)

theorem State.coreInputs_connected (s : State) (p : Pins) (port : Reactive.Input w) :
    Serial.circuit.observe (s.inputs p).values s.frontend (.core port) = s.coreInputs p port :=
  coreInput_status_independent p s.frontend (s.status p) (fun _ => 0) port

def State.step (s : State) (p : Pins) : State :=
  ⟨Serial.circuit.step (s.inputs p).values s.frontend,
    s.controller.step (s.coreInputs p)⟩

inductive Output : Nat → Type where
  | miso : Output 1 | ready : Output 1 | busy : Output 1
  | levels : Output 3 | enabled : Output 3

def State.observe (s : State) (p : Pins) : {w : Nat} → Output w → BitVec w
  | _, .miso => Serial.circuit.observe (s.inputs p).values s.frontend .miso
  | _, .ready => Serial.circuit.observe (s.inputs p).values s.frontend .ready
  | _, .busy => s.status p .busy
  | _, .levels => s.status p .levels
  | _, .enabled => s.status p .enabled

def State.run (s : State) (pins : List Pins) : State := pins.foldl State.step s

/-- One core input per sampled edge, including every request/read serial bit. -/
def State.commands (s : State) : List Pins → List (Values Reactive.Input)
  | [] => []
  | p :: rest => s.coreInputs p :: (s.step p).commands rest

def State.frontendInputs (s : State) : List Pins → List Serial.Inputs
  | [] => []
  | p :: rest => s.inputs p :: (s.step p).frontendInputs rest

theorem State.commands_length (s : State) (pins : List Pins) :
    (s.commands pins).length = pins.length := by
  induction pins generalizing s with
  | nil => rfl
  | cons p rest ih => exact congrArg Nat.succ (ih (s.step p))
  done

theorem State.run_controller (s : State) (pins : List Pins) :
    (s.run pins).controller = s.controller.run (s.commands pins) := by
  induction pins generalizing s with
  | nil => rfl
  | cons p rest ih => exact ih (s.step p)
  done

theorem State.run_frontend (s : State) (pins : List Pins) :
    @(s.run pins).frontend = @Serial.actualRun s.frontend (s.frontendInputs pins) := by
  induction pins generalizing s with
  | nil => rfl
  | cons p rest ih => exact ih (s.step p)
  done

theorem State.rawInputs_connected (s : State) (p : Pins) :
    s.coreInputs p .rawInputs = p.rawInputs := rfl

def State.record (s : State) : Serial.State := Serial.State.fromValues s.frontend

theorem State.record_values (s : State) : @Serial.State.values s.record = @s.frontend :=
  Serial.State.values_fromValues s.frontend

private theorem fromValues_values (s : Serial.State) :
    Serial.State.fromValues s.values = s := by
  cases s
  simp [Serial.State.fromValues, Serial.State.values]
  have hb (b : Bool) : (BitVec.ofBool b == 1#1) = b := by cases b <;> rfl
  simp only [hb, and_self]
  done

theorem State.record_step (s : State) (p : Pins) :
    (s.step p).record = s.record.step (s.inputs p) := by
  have h := Serial.State.step_values s.record (s.inputs p)
  rw [s.record_values] at h
  change Serial.State.fromValues (Serial.circuit.step (s.inputs p).values s.frontend) = _
  rw [← h, fromValues_values]
  done

theorem State.record_coreInputs (s : State) (p : Pins) (port : Reactive.Input w) :
    s.coreInputs p port = s.record.coreInput (s.inputs p) port := by
  have h := Serial.coreInput_correct s.record (s.inputs p) port
  rw [s.record_values] at h
  exact (s.coreInputs_connected p port).symm.trans h
  done

theorem State.record_observe (s : State) (p : Pins) (o : Serial.Output w) :
    Serial.circuit.observe (s.inputs p).values s.frontend o = s.record.observe (s.inputs p) o := by
  have h := Serial.State.observe_values s.record (s.inputs p) o
  rwa [s.record_values] at h
  done

/-- Rejection is sampled from the command's actual pre-edge controller output. -/
theorem State.dispatch_rejection (s : State) (p : Pins)
    (cold : p.cold = false) (dispatch : s.record.dispatch = true)
    (delivers : Serial.deliver (s.inputs p) s.record = true) :
    (s.step p).record.rejected = (s.status p .rejected == 1) := by
  rw [s.record_step]
  simp only [State.inputs, Pins.inputs, cold] at delivers
  simp [Serial.State.step, State.inputs, Pins.inputs, cold, dispatch, delivers]
  done

/-- Capture follows the dispatch register, independently of current serial SCK. -/
theorem State.dispatch_capture (s : State) (p : Pins) (cold : p.cold = false) :
    (s.step p).record.capture = s.record.dispatch := by
  rw [s.record_step]
  simp [Serial.State.step, State.inputs, Pins.inputs, cold]
  done

/-- The captured response uses this edge's live pre-state status and the
previously latched rejection; the controller still steps on the same edge. -/
theorem State.capture_response (s : State) (p : Pins)
    (cold : p.cold = false) (capture : s.record.capture = true) :
    (s.step p).record.response = s.record.capturedResponse (s.inputs p) ∧
    (s.step p).record.ready = true ∧
    (s.step p).controller = s.controller.step (s.coreInputs p) := by
  rw [s.record_step]
  simp [Serial.State.step, State.inputs, Pins.inputs, State.step, cold, capture]
  done

end Pinwheel.Hardware.Buffered.SerialPackage
