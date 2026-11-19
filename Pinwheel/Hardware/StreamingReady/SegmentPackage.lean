import Pinwheel.Hardware.StreamingReady.SegmentStore
import Pinwheel.Hardware.StreamingReady.CausalSession

/-! Compose the sequencer with the existing quad frontend and physical pads.
    The public feedback law spans writes, START, capture, drain and RELEASE. -/
namespace Pinwheel.Hardware.StreamingReady.SegmentPackage

open Pinwheel.Hardware CausalSession
open Pinwheel.Program.StreamingReady (Session.Pins)

structure State (a : Nat) where
  frontend : Values Streaming.Frontend.Register
  core : Values (SegmentCore.Register a)

def State.project (s : State a) : Package.State a := ⟨s.frontend, SegmentCore.project s.core⟩

def State.coreInputs (s : State a) (pins : Package.Pins) : Values Core.Input :=
  s.project.coreInputs (Package.Components.typed a) pins

def State.status (registered : Bool) (s : State a) (pins : Package.Pins) : Values Core.Output :=
  (SegmentCore.circuit a registered).observe (s.coreInputs pins) s.core

def State.step (registered : Bool) (s : State a) (pins : Package.Pins) : State a :=
  ⟨Streaming.Frontend.circuit.step (pins.inputs (s.status registered pins)) s.frontend,
   (SegmentCore.circuit a registered).step (s.coreInputs pins) s.core⟩

def State.observe (registered : Bool) (s : State a) (pins : Package.Pins) : Values Package.Output
  | _, .miso => Streaming.Frontend.circuit.observe (pins.inputs (s.status registered pins)) s.frontend .miso
  | _, .ready => Streaming.Frontend.circuit.observe (pins.inputs (s.status registered pins)) s.frontend .ready
  | _, .busy => s.status registered pins .busy
  | _, .levels => s.status registered pins .levels
  | _, .enabled => s.status registered pins .enabled

def backend (a : Nat) (registered : Bool) : Backend (State a) where
  step state pins :=
    state.step registered ((TinyWiring.canonical a).enginePins (PublicPins.embed pins))
  observe state pins :=
    let p := PublicPins.embed pins
    (TinyWiring.canonical a).pads p (state.observe registered ((TinyWiring.canonical a).enginePins p))

def Related (direct cached : State a) : Prop :=
  @direct.frontend = @cached.frontend ∧ SegmentStore.Related direct.core cached.core

private theorem inputs_eq (l r : State a) (same : Related l r) (pins : Package.Pins) :
    @State.coreInputs a l pins = @State.coreInputs a r pins := by
  funext w port
  simp only [State.coreInputs, Streaming.Package.State.coreInputs, State.project, same.1]

private theorem status_eq (l r : State a) (same : Related l r) (pins : Package.Pins) :
    @State.status a false l pins = @State.status a true r pins := by
  unfold State.status
  rw [inputs_eq l r same pins]
  exact SegmentStore.observe (r.coreInputs pins) l.core r.core same.2

theorem simulation (a : Nat) : Simulates (backend a false) (backend a true) Related := by
  constructor
  · intro l r same pins
    let p := PublicPins.embed pins
    let input := (TinyWiring.canonical a).enginePins p
    have outputs : @State.observe a false l input = @State.observe a true r input := by
      funext w output
      cases output <;> simp only [State.observe, status_eq l r same input, same.1]
    exact congrArg (fun values : Values Package.Output => (TinyWiring.canonical a).pads p values) outputs
  · intro l r same pins
    let input := (TinyWiring.canonical a).enginePins (PublicPins.embed pins)
    refine ⟨?_, ?_⟩
    · change @Circuit.step _ _ _ Streaming.Frontend.circuit (input.inputs (l.status false input)) l.frontend =
        @Circuit.step _ _ _ Streaming.Frontend.circuit (input.inputs (r.status true input)) r.frontend
      rw [status_eq l r same input, same.1]
    · change SegmentStore.Related ((SegmentCore.circuit a false).step (l.coreInputs input) l.core)
        ((SegmentCore.circuit a true).step (r.coreInputs input) r.core)
      rw [inputs_eq l r same input]
      exact SegmentStore.step _ _ _ same.2

/-- Independently reacting environments see the same timed pad and host
    observations through every segmented branch and transport command. -/
theorem run_eq (env : Environment E) (direct cached : State a) (same : Related direct cached)
    (initial : E) (clocks : Nat) :
    let before := (backend a false).run env direct initial clocks
    let after := (backend a true).run env cached initial clocks
    Related before.final after.final ∧ before.environment = after.environment ∧ before.edges = after.edges :=
  (simulation a).run_eq env direct cached same initial clocks

end Pinwheel.Hardware.StreamingReady.SegmentPackage
