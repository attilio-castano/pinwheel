import Pinwheel.Hardware.Streaming.Package

/-! Typed interpretation of a parsed stateless streaming wrapper. The parser
is an explicit interpretation boundary; a certificate checks every actual
connection, clock, public port and instance before composition. -/
namespace Pinwheel.Hardware.Streaming.Wiring
open Pinwheel.Hardware

inductive Physical : Nat → Type where
  | initialize : Physical 1 | csn : Physical 1 | sck : Physical 1
  | mosi : Physical 4 | rawInputs : Physical 2

def Physical.eval (p : Package.Pins) : Physical w → BitVec w
  | .initialize => p.initialize | .csn => p.csn | .sck => p.sck
  | .mosi => p.mosi | .rawInputs => p.rawInputs

inductive FrontSource : Nat → Type where
  | physical : Physical w → FrontSource w
  | status : Core.Output w → FrontSource w

def FrontSource.eval (p : Package.Pins) (s : Values Core.Output) : FrontSource w → BitVec w
  | .physical port => port.eval p
  | .status port => s port

inductive PublicSource : Nat → Type where
  | frontend : Frontend.Output w → PublicSource w
  | status : Core.Output w → PublicSource w

def PublicSource.eval (f : Values Frontend.Output) (s : Values Core.Output) : PublicSource w → BitVec w
  | .frontend port => f port
  | .status port => s port

structure Port where
  name : String
  width : Nat
  input : Bool
  deriving DecidableEq

structure Description where
  name : String
  interface : List Port
  instances : List (String × String)
  frontendClock : String
  coreClock : String
  frontend : {w : Nat} → Frontend.Input w → FrontSource w
  core : {w : Nat} → Core.Input w → Frontend.Output w
  outputs : {w : Nat} → Package.Output w → PublicSource w

def interface : List Port :=
  [⟨"clk",1,true⟩,⟨"initialize",1,true⟩,⟨"csn",1,true⟩,⟨"sck",1,true⟩,
   ⟨"mosi",4,true⟩,⟨"raw_inputs",2,true⟩,⟨"miso",4,false⟩,⟨"ready",1,false⟩,
   ⟨"busy",1,false⟩,⟨"levels",3,false⟩,⟨"enabled",3,false⟩]

def canonicalFrontend : Frontend.Input w → FrontSource w
  | .initialize => .physical .initialize | .csn => .physical .csn
  | .sck => .physical .sck | .mosi => .physical .mosi
  | .rawInputs => .physical .rawInputs | .status port => .status port

def canonicalOutput : Package.Output w → PublicSource w
  | .miso => .frontend .miso | .ready => .frontend .ready
  | .busy => .status .busy | .levels => .status .levels | .enabled => .status .enabled

def canonical (a : Nat) : Description :=
  ⟨s!"pinwheel_streaming_quad_d{2^a}",interface,
   [("frontend","pinwheel_streaming_quad_frontend"),("core",s!"pinwheel_streaming_core_d{2^a}")],
   "clk","clk",canonicalFrontend,(fun p => .core p),canonicalOutput⟩

structure Certificate (a : Nat) (d : Description) : Prop where
  name : d.name = (canonical a).name
  interface : d.interface = interface
  instances : d.instances = (canonical a).instances
  frontendClock : d.frontendClock = "clk"
  coreClock : d.coreClock = "clk"
  frontend : ∀ {w} (p : Frontend.Input w), d.frontend p = canonicalFrontend p
  core : ∀ {w} (p : Core.Input w), d.core p = .core p
  outputs : ∀ {w} (p : Package.Output w), d.outputs p = canonicalOutput p

def Description.frontendInputs (d : Description) (p : Package.Pins) (status : Values Core.Output) :
    Values Frontend.Input := fun port => (d.frontend port).eval p status

def Description.coreInputs (d : Description) (c : Package.Components a) (s : Package.State a)
    (p : Package.Pins) : Values Core.Input :=
  fun port => c.frontend.observe (d.frontendInputs p (fun _ => 0)) s.frontend (d.core port)

def Description.status (d : Description) (c : Package.Components a) (s : Package.State a)
    (p : Package.Pins) : Values Core.Output := c.core.observe (d.coreInputs c s p) s.core

def Description.step (d : Description) (c : Package.Components a) (s : Package.State a)
    (p : Package.Pins) : Package.State a :=
  ⟨c.frontend.step (d.frontendInputs p (d.status c s p)) s.frontend,
   c.core.step (d.coreInputs c s p) s.core⟩

def Description.observe (d : Description) (c : Package.Components a) (s : Package.State a)
    (p : Package.Pins) : Values Package.Output :=
  fun port => (d.outputs port).eval
    (c.frontend.observe (d.frontendInputs p (d.status c s p)) s.frontend) (d.status c s p)

def Description.run (d : Description) (c : Package.Components a) (s : Package.State a)
    (pins : List Package.Pins) : Package.State a := pins.foldl (fun s p => d.step c s p) s

theorem Certificate.frontendInputs_eq {d : Description} (h : Certificate a d)
    (p : Package.Pins) (status : Values Core.Output) :
    (d.frontendInputs p status : Values Frontend.Input) = (p.inputs status : Values Frontend.Input) := by
  funext w port
  simp only [Description.frontendInputs,h.frontend]
  cases port <;> rfl
  done

theorem Certificate.coreInputs_eq {d : Description} (h : Certificate a d)
    (c : Package.Components a) (s : Package.State a) (p : Package.Pins) :
    (d.coreInputs c s p : Values Core.Input) = (s.coreInputs c p : Values Core.Input) := by
  funext w port
  simp only [Description.coreInputs,h.frontendInputs_eq,h.core,Package.State.coreInputs]
  done

theorem Certificate.status_eq {d : Description} (h : Certificate a d)
    (c : Package.Components a) (s : Package.State a) (p : Package.Pins) :
    (d.status c s p : Values Core.Output) = (s.status c p : Values Core.Output) := by
  simp only [Description.status,h.coreInputs_eq,Package.State.status]
  done

theorem Certificate.step_eq {d : Description} (h : Certificate a d)
    (c : Package.Components a) (s : Package.State a) (p : Package.Pins) :
    d.step c s p = s.step c p := by
  simp only [Description.step,h.frontendInputs_eq,h.coreInputs_eq,h.status_eq,
    Package.State.step,Package.State.frontendInputs]
  done

theorem Certificate.observe_eq {d : Description} (h : Certificate a d)
    (c : Package.Components a) (s : Package.State a) (p : Package.Pins) (port : Package.Output w) :
    d.observe c s p port = s.observe c p port := by
  simp only [Description.observe,h.frontendInputs_eq,h.status_eq,h.outputs]
  cases port <;> rfl
  done

theorem Certificate.run_eq {d : Description} (h : Certificate a d)
    (c : Package.Components a) (s : Package.State a) (pins : List Package.Pins) :
    d.run c s pins = s.run c pins := by
  induction pins generalizing s with
  | nil => rfl
  | cons pin pins ih =>
    change d.run c (d.step c s pin) pins = (s.step c pin).run c pins
    rw [h.step_eq]
    exact ih (s.step c pin)
  done

end Pinwheel.Hardware.Streaming.Wiring
