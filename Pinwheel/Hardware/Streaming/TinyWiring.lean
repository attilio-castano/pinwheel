import Pinwheel.Hardware.Streaming.Wiring

namespace Pinwheel.Hardware.Streaming.TinyWiring
open Pinwheel.Hardware
set_option maxHeartbeats 200000

inductive Input : Nat → Type where
  | ui : Input 8 | uio : Input 8 | ena : Input 1 | rstN : Input 1
  | engine : Package.Output w → Input w
abbrev Register (_ : Nat) := Empty
abbrev E := Expr Input Register

structure Pins where
  ui : BitVec 8 := 0
  uio : BitVec 8 := 0
  ena : BitVec 1 := 1
  rstN : BitVec 1 := 1

def inputs (p : Pins) (engine : Values Package.Output) : Values Input
  | _, .ui => p.ui | _, .uio => p.uio | _, .ena => p.ena | _, .rstN => p.rstN
  | _, .engine port => engine port
def registers : Values Register := fun r => nomatch r

inductive Pad where | uo | uio | oe

structure Description where
  name : String
  interface : List Wiring.Port
  engineName : String
  engineKind : String
  engineClock : String
  engine : {w : Nat} → Wiring.Physical w → E w
  outputs : Pad → E 8
  unused : E 1

def interface : List Wiring.Port :=
  [⟨"ui_in",8,true⟩,⟨"uo_out",8,false⟩,⟨"uio_in",8,true⟩,
   ⟨"uio_out",8,false⟩,⟨"uio_oe",8,false⟩,⟨"ena",1,true⟩,⟨"clk",1,true⟩,⟨"rst_n",1,true⟩]
def active : E 1 := .band (.input .ena) (.input .rstN)
def canonicalEngine : Wiring.Physical w → E w
  | .initialize => .inv active
  | .csn => .slice 0 1 (by decide) (.input .ui)
  | .sck => .slice 1 1 (by decide) (.input .ui)
  | .mosi => .concat (.slice 5 3 (by decide) (.input .ui)) (.slice 2 1 (by decide) (.input .ui))
  | .rawInputs => .slice 3 2 (by decide) (.input .ui)
def canonicalOutput : Pad → E 8
  | .uo => .mux active (.concat (.lit (0 : BitVec 2))
      (.concat (.input (Input.engine Package.Output.busy))
        (.concat (.input (Input.engine Package.Output.ready)) (.input (Input.engine Package.Output.miso))))) (.lit 0)
  | .uio => .mux active (.concat (.lit (0 : BitVec 5)) (.input (Input.engine Package.Output.levels))) (.lit 0)
  | .oe => .mux active (.concat (.lit (0 : BitVec 5)) (.input (Input.engine Package.Output.enabled))) (.lit 0)
def canonicalUnused : E 1 :=
  .equal (.concat (.input .uio) (.lit (0 : BitVec 1))) (.lit (BitVec.ofNat 9 511))
def canonical (a : Nat) : Description :=
  ⟨s!"tt_um_pinwheel_streaming_d{2^a}",interface,"engine",s!"pinwheel_streaming_quad_d{2^a}",
   "clk",canonicalEngine,canonicalOutput,canonicalUnused⟩

structure Certificate (a : Nat) (d : Description) : Prop where
  name : d.name = (canonical a).name
  interface : d.interface = interface
  engineName : d.engineName = "engine"
  engineKind : d.engineKind = (canonical a).engineKind
  engineClock : d.engineClock = "clk"
  engine : ∀ {w} (p : Wiring.Physical w), d.engine p = canonicalEngine p
  outputs : ∀ p, d.outputs p = canonicalOutput p
  unused : d.unused = canonicalUnused

def Description.enginePins (d : Description) (p : Pins) : Package.Pins :=
  let i : Values Input := inputs p (fun _ => 0)
  ⟨(d.engine .initialize).eval i registers,(d.engine .csn).eval i registers,
   (d.engine .sck).eval i registers,(d.engine .mosi).eval i registers,
   (d.engine .rawInputs).eval i registers⟩

def Description.pads (d : Description) (p : Pins) (engine : Values Package.Output) : Pad → BitVec 8 :=
  fun pad => (d.outputs pad).eval (inputs p engine) registers

def Description.step (d : Description) (w : Wiring.Description) (c : Package.Components a)
    (s : Package.State a) (p : Pins) : Package.State a := w.step c s (d.enginePins p)

def Description.observe (d : Description) (w : Wiring.Description) (c : Package.Components a)
    (s : Package.State a) (p : Pins) : Pad → BitVec 8 :=
  d.pads p (w.observe c s (d.enginePins p))

theorem Certificate.enginePins_eq {d : Description} (h : Certificate a d) (p : Pins) :
    d.enginePins p = Description.enginePins (canonical a) p := by
  have he : (@Description.engine d) = @canonicalEngine :=
    funext fun _ => funext fun port => h.engine port
  simp only [Description.enginePins,he]
  rfl
  done

theorem Certificate.pads_eq {d : Description} (h : Certificate a d) (p : Pins)
    (engine : Values Package.Output) (pad : Pad) :
    d.pads p engine pad = Description.pads (canonical a) p engine pad := by
  have ho : d.outputs = canonicalOutput := funext fun port => h.outputs port
  simp only [Description.pads,ho]
  rfl
  done

theorem Certificate.step_eq {d : Description} (h : Certificate a d)
    {w : Wiring.Description} (hw : Wiring.Certificate a w) (c : Package.Components a)
    (s : Package.State a) (p : Pins) :
    d.step w c s p = s.step c (Description.enginePins (canonical a) p) := by
  simp only [Description.step,h.enginePins_eq,hw.step_eq]
  done

theorem Certificate.observe_eq {d : Description} (h : Certificate a d)
    {w : Wiring.Description} (hw : Wiring.Certificate a w) (c : Package.Components a)
    (s : Package.State a) (p : Pins) (pad : Pad) :
    d.observe w c s p pad =
      Description.pads (canonical a) p (s.observe c (Description.enginePins (canonical a) p)) pad := by
  simp only [Description.observe,h.enginePins_eq,h.pads_eq]
  have outputs : (w.observe c s (Description.enginePins (canonical a) p) : Values Package.Output) =
      (s.observe c (Description.enginePins (canonical a) p) : Values Package.Output) :=
    funext fun _ => funext fun port => hw.observe_eq c s _ port
  rw [outputs]
  done

end Pinwheel.Hardware.Streaming.TinyWiring
