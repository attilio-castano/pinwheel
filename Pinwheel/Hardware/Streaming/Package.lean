import Pinwheel.Hardware.Streaming.Frontend

/-! Shared pre-edge composition for the new quad frontend and bounded core.
The digital program bank and queues are represented by Core.Register; this
package has no implicit SRAM macro or electrical memory assumption. -/
namespace Pinwheel.Hardware.Streaming.Package
open Pinwheel.Hardware

structure Pins where
  «initialize» : BitVec 1 := 0
  csn : BitVec 1 := 1
  sck : BitVec 1 := 0
  mosi : BitVec 4 := 0
  rawInputs : BitVec 2 := 0

def Pins.inputs (p : Pins) (status : Values Core.Output) : Values Frontend.Input
  | _, .initialize => p.initialize
  | _, .csn => p.csn
  | _, .sck => p.sck
  | _, .mosi => p.mosi
  | _, .rawInputs => p.rawInputs
  | _, .status o => status o

structure Behavior (I R O : Nat → Type) where
  step : Values I → Values R → Values R
  observe : Values I → Values R → Values O

def Behavior.ofCircuit (c : Circuit I R O) : Behavior I R O := ⟨c.step,c.observe⟩

structure Components (a : Nat) where
  frontend : Behavior Frontend.Input Frontend.Register Frontend.Output
  core : Behavior Core.Input (Core.Register a) Core.Output

def Components.typed (a : Nat) : Components a :=
  ⟨.ofCircuit Frontend.circuit,.ofCircuit (Core.circuit a)⟩

structure Correct (c : Components a) : Prop where
  frontend_step : ∀ (i : Values Frontend.Input) (s : Values Frontend.Register) {w}
    (r : Frontend.Register w), c.frontend.step i s r = Frontend.circuit.step i s r
  frontend_observe : ∀ (i : Values Frontend.Input) (s : Values Frontend.Register) {w}
    (o : Frontend.Output w), c.frontend.observe i s o = Frontend.circuit.observe i s o
  core_step : ∀ (i : Values Core.Input) (s : Values (Core.Register a)) {w}
    (r : Core.Register a w), c.core.step i s r = (Core.circuit a).step i s r
  core_observe : ∀ (i : Values Core.Input) (s : Values (Core.Register a)) {w}
    (o : Core.Output w), c.core.observe i s o = (Core.circuit a).observe i s o

theorem Correct.eq_typed {c : Components a} (h : Correct c) : c = Components.typed a := by
  have fstep : c.frontend.step = (Behavior.ofCircuit Frontend.circuit).step :=
    funext fun i => funext fun s => funext fun _ => funext fun r => h.frontend_step i s r
  have fobserve : c.frontend.observe = (Behavior.ofCircuit Frontend.circuit).observe :=
    funext fun i => funext fun s => funext fun _ => funext fun o => h.frontend_observe i s o
  have cstep : c.core.step = (Behavior.ofCircuit (Core.circuit a)).step :=
    funext fun i => funext fun s => funext fun _ => funext fun r => h.core_step i s r
  have cobserve : c.core.observe = (Behavior.ofCircuit (Core.circuit a)).observe :=
    funext fun i => funext fun s => funext fun _ => funext fun o => h.core_observe i s o
  cases c with
  | mk frontend core =>
    cases frontend
    cases core
    simp_all only [Components.typed,Behavior.ofCircuit]
  done

structure State (a : Nat) where
  frontend : Values Frontend.Register
  core : Values (Core.Register a)

def State.coreInputs (s : State a) (c : Components a) (p : Pins) : Values Core.Input :=
  fun port => c.frontend.observe (p.inputs (fun _ => 0)) s.frontend (.core port)

/-- All core commands are independent of frontend status inputs, so the actual
feedback wiring has no combinational cycle. Status is still sampled for the
frontend's next state and receipts. -/
theorem coreInput_independent (p : Pins) (s : Values Frontend.Register)
    (left right : Values Core.Output) (port : Core.Input w) :
    Frontend.circuit.observe (p.inputs left) s (.core port) =
      Frontend.circuit.observe (p.inputs right) s (.core port) := by
  cases port <;> rfl
  done

def State.status (s : State a) (c : Components a) (p : Pins) : Values Core.Output :=
  c.core.observe (s.coreInputs c p) s.core

def State.frontendInputs (s : State a) (c : Components a) (p : Pins) : Values Frontend.Input :=
  p.inputs (s.status c p)

def State.step (s : State a) (c : Components a) (p : Pins) : State a :=
  ⟨c.frontend.step (s.frontendInputs c p) s.frontend,
   c.core.step (s.coreInputs c p) s.core⟩

inductive Output : Nat → Type where
  | miso : Output 4 | ready : Output 1 | busy : Output 1
  | levels : Output 3 | enabled : Output 3

def State.observe (s : State a) (c : Components a) (p : Pins) : Values Output
  | _, .miso => c.frontend.observe (s.frontendInputs c p) s.frontend .miso
  | _, .ready => c.frontend.observe (s.frontendInputs c p) s.frontend .ready
  | _, .busy => s.status c p .busy
  | _, .levels => s.status c p .levels
  | _, .enabled => s.status c p .enabled

def State.run (s : State a) (c : Components a) (pins : List Pins) : State a :=
  pins.foldl (fun s p => s.step c p) s

theorem State.step_correct {c : Components a} (h : Correct c) (s : State a) (p : Pins) :
    s.step c p = s.step (.typed a) p := by
  rw [h.eq_typed]
  done

theorem State.observe_correct {c : Components a} (h : Correct c) (s : State a) (p : Pins)
    (o : Output w) : s.observe c p o = s.observe (.typed a) p o := by
  rw [h.eq_typed]
  done

theorem State.run_correct {c : Components a} (h : Correct c) (s : State a) (pins : List Pins) :
    s.run c pins = s.run (.typed a) pins := by
  rw [h.eq_typed]
  done

end Pinwheel.Hardware.Streaming.Package
