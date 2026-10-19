import Pinwheel.Hardware.StreamingReady.Core
import Pinwheel.Hardware.Streaming.Package

/-! The sampled-ready package reuses the exact frontend and physical state
inventory. Its correctness contract targets the new core, never the earlier
streaming typed components. -/
namespace Pinwheel.Hardware.StreamingReady.Package
open Pinwheel.Hardware

abbrev Pins := Streaming.Package.Pins
abbrev Behavior := Streaming.Package.Behavior
abbrev Components := Streaming.Package.Components
abbrev State := Streaming.Package.State
abbrev Output := Streaming.Package.Output

namespace Output
abbrev miso := Streaming.Package.Output.miso
abbrev ready := Streaming.Package.Output.ready
abbrev busy := Streaming.Package.Output.busy
abbrev levels := Streaming.Package.Output.levels
abbrev enabled := Streaming.Package.Output.enabled
end Output

abbrev Pins.inputs (p : Pins) (status : Values Core.Output) : Values Streaming.Frontend.Input :=
  Streaming.Package.Pins.inputs p status
abbrev Behavior.ofCircuit (c : Circuit I R O) : Behavior I R O := Streaming.Package.Behavior.ofCircuit c

def Components.typed (a : Nat) : Components a :=
  ⟨.ofCircuit Streaming.Frontend.circuit,.ofCircuit (Core.circuit a)⟩

structure Correct (c : Components a) : Prop where
  frontend_step : ∀ (i : Values Streaming.Frontend.Input) (s : Values Streaming.Frontend.Register) {w}
    (r : Streaming.Frontend.Register w), c.frontend.step i s r = Streaming.Frontend.circuit.step i s r
  frontend_observe : ∀ (i : Values Streaming.Frontend.Input) (s : Values Streaming.Frontend.Register) {w}
    (o : Streaming.Frontend.Output w), c.frontend.observe i s o = Streaming.Frontend.circuit.observe i s o
  core_step : ∀ (i : Values Core.Input) (s : Values (Core.Register a)) {w}
    (r : Core.Register a w), c.core.step i s r = (Core.circuit a).step i s r
  core_observe : ∀ (i : Values Core.Input) (s : Values (Core.Register a)) {w}
    (o : Core.Output w), c.core.observe i s o = (Core.circuit a).observe i s o

theorem Correct.eq_typed {c : Components a} (h : Correct c) : c = Components.typed a := by
  have fstep : c.frontend.step = (Behavior.ofCircuit Streaming.Frontend.circuit).step :=
    funext fun i => funext fun s => funext fun _ => funext fun r => h.frontend_step i s r
  have fobserve : c.frontend.observe = (Behavior.ofCircuit Streaming.Frontend.circuit).observe :=
    funext fun i => funext fun s => funext fun _ => funext fun o => h.frontend_observe i s o
  have cstep : c.core.step = (Behavior.ofCircuit (Core.circuit a)).step :=
    funext fun i => funext fun s => funext fun _ => funext fun r => h.core_step i s r
  have cobserve : c.core.observe = (Behavior.ofCircuit (Core.circuit a)).observe :=
    funext fun i => funext fun s => funext fun _ => funext fun o => h.core_observe i s o
  cases c with
  | mk frontend core =>
    cases frontend
    cases core
    simp_all only [Components.typed,Behavior.ofCircuit,Streaming.Package.Behavior.ofCircuit]

abbrev State.coreInputs (s : State a) (c : Components a) (p : Pins) : Values Core.Input :=
  Streaming.Package.State.coreInputs s c p
abbrev State.status (s : State a) (c : Components a) (p : Pins) : Values Core.Output :=
  Streaming.Package.State.status s c p
abbrev State.frontendInputs (s : State a) (c : Components a) (p : Pins) : Values Streaming.Frontend.Input :=
  Streaming.Package.State.frontendInputs s c p
abbrev State.step (s : State a) (c : Components a) (p : Pins) : State a :=
  Streaming.Package.State.step s c p
abbrev State.observe (s : State a) (c : Components a) (p : Pins) : Values Output :=
  Streaming.Package.State.observe s c p
abbrev State.run (s : State a) (c : Components a) (pins : List Pins) : State a :=
  Streaming.Package.State.run s c pins

theorem State.step_correct {c : Components a} (h : Correct c) (s : State a) (p : Pins) :
    s.step c p = s.step (Components.typed a) p := by rw [h.eq_typed]
theorem State.observe_correct {c : Components a} (h : Correct c) (s : State a) (p : Pins)
    (o : Output w) : s.observe c p o = s.observe (Components.typed a) p o := by rw [h.eq_typed]
theorem State.run_correct {c : Components a} (h : Correct c) (s : State a) (pins : List Pins) :
    s.run c pins = s.run (Components.typed a) pins := by rw [h.eq_typed]

end Pinwheel.Hardware.StreamingReady.Package
