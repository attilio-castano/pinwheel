import Pinwheel.Hardware.Buffered.ArtifactPackageWiring
import Pinwheel.Hardware.Buffered.ArtifactTinyTapeout
import Pinwheel.Hardware.Decode

/-! Stateless expression interpretation for the actual TinyTapeout wrapper.
Generated certificates check the complete interface, instance, clock and every
actual pin/output expression. The expression evaluator is the existing typed
hardware evaluator; the restricted Verilog decoder remains explicit trust. -/
namespace Pinwheel.Hardware.Buffered.ArtifactTinyTapeoutWiring
open Pinwheel.Hardware
open ArtifactTinyTapeout (Pins Pads)

inductive Input : Nat → Type where
  | ui : Input 8 | uio : Input 8 | ena : Input 1 | rstN : Input 1
  | engine : SerialPackage.Output w → Input w

abbrev Register (_ : Nat) := Empty
abbrev E := Expr Input Register

def inputs (p : Pins) (engine : Values SerialPackage.Output) : Values Input
  | _, .ui => p.ui | _, .uio => p.uio
  | _, .ena => BitVec.ofBool p.ena | _, .rstN => BitVec.ofBool p.rstN
  | _, .engine output => engine output

def registers : Values Register := fun r => nomatch r

inductive Pad where | uo | uio | oe

structure Wiring where
  name : String
  interface : List ArtifactPackageWiring.Port
  engineName : String
  engineKind : String
  engineClock : String
  engine : {w : Nat} → ArtifactPackageWiring.Physical w → E w
  outputs : Pad → E 8
  unused : E 1

def interface : List ArtifactPackageWiring.Port :=
  [⟨"ui_in",8,true⟩,⟨"uo_out",8,false⟩,⟨"uio_in",8,true⟩,
    ⟨"uio_out",8,false⟩,⟨"uio_oe",8,false⟩,⟨"ena",1,true⟩,⟨"clk",1,true⟩,⟨"rst_n",1,true⟩]

def active : E 1 := .band (.input .ena) (.input .rstN)

def canonicalEngine : ArtifactPackageWiring.Physical w → E w
  | .initialize => .inv active
  | .csn => .slice 0 1 (by decide) (.input .ui)
  | .sck => .slice 1 1 (by decide) (.input .ui)
  | .mosi => .slice 2 1 (by decide) (.input .ui)
  | .rawInputs => .slice 3 2 (by decide) (.input .ui)

def canonicalOutput : Pad → E 8
  | .uo => .mux active
      (.concat (.lit 0#5) (.concat (.input (Input.engine SerialPackage.Output.busy))
        (.concat (.input (Input.engine SerialPackage.Output.ready))
          (.input (Input.engine SerialPackage.Output.miso))))) (.lit 0)
  | .uio => .mux active (.concat (.lit 0#5) (.input (Input.engine SerialPackage.Output.levels))) (.lit 0)
  | .oe => .mux active (.concat (.lit 0#5) (.input (Input.engine SerialPackage.Output.enabled))) (.lit 0)

def canonicalUnused : E 1 :=
  .equal (.concat (.input .uio) (.concat (.slice 5 3 (by decide) (.input .ui)) (.lit 0#1)))
    (.lit (BitVec.ofNat 12 (2^12-1)))

def canonical : Wiring :=
  ⟨"tt_um_pinwheel_buffered", interface, "engine", "pinwheel_buffered_shared_branches_sram_serial",
    "clk", canonicalEngine, canonicalOutput, canonicalUnused⟩

structure Certificate (wiring : Wiring) : Prop where
  name : wiring.name = canonical.name
  interface : wiring.interface = canonical.interface
  engineName : wiring.engineName = canonical.engineName
  engineKind : wiring.engineKind = canonical.engineKind
  engineClock : wiring.engineClock = "clk"
  engine : ∀ {w} (port : ArtifactPackageWiring.Physical w), wiring.engine port = canonical.engine port
  outputs : ∀ pad, wiring.outputs pad = canonical.outputs pad
  unused : wiring.unused = canonical.unused

def Wiring.enginePins (wiring : Wiring) (p : Pins) : SerialPackage.Pins :=
  let i : Values Input := inputs p (fun _ => 0)
  ⟨(wiring.engine .initialize).eval i registers == 1,
    (wiring.engine .sck).eval i registers == 1,
    (wiring.engine .mosi).eval i registers == 1,
    (wiring.engine .csn).eval i registers == 1,
    (wiring.engine .rawInputs).eval i registers⟩

def Wiring.pads (wiring : Wiring) (p : Pins) (engine : Values SerialPackage.Output) : Pads :=
  ⟨(wiring.outputs .uo).eval (inputs p engine) registers,
    (wiring.outputs .uio).eval (inputs p engine) registers,
    (wiring.outputs .oe).eval (inputs p engine) registers⟩

def Wiring.step {M : Type} (wiring : Wiring) (engine : ArtifactPackageWiring.Wiring)
    (components : ArtifactPackage.Components) (memory : Memory.SinglePort.Contract M 6 64)
    (s : ArtifactPackage.State M) (p : Pins) : ArtifactPackage.State M :=
  engine.step components memory s (wiring.enginePins p)

def Wiring.observe {M : Type} (wiring : Wiring) (engine : ArtifactPackageWiring.Wiring)
    (components : ArtifactPackage.Components) (memory : Memory.SinglePort.Contract M 6 64)
    (s : ArtifactPackage.State M) (p : Pins) : Pads :=
  wiring.pads p (engine.observe components memory s (wiring.enginePins p))

private theorem bool_bit : ∀ b : Bool, (BitVec.ofBool b == 1#1) = b := by decide +kernel

theorem Certificate.enginePins_eq {wiring : Wiring} (certificate : Certificate wiring) (p : Pins) :
    wiring.enginePins p = p.enginePins := by
  simp only [Wiring.enginePins, certificate.engine, canonical, canonicalEngine, active,
    Expr.eval, inputs, ArtifactTinyTapeout.Pins.enginePins, ArtifactTinyTapeout.Pins.active]
  simp [BitVec.ofBool_and_ofBool, BitVec.not_ofBool, Decode.extract_bit,
    BitVec.getLsbD_eq_getElem, bool_bit]
  done

private theorem zero_append : ∀ v : BitVec 3, (0#5) ++ v = v.setWidth 8 := by decide +kernel

theorem Certificate.pads_eq {wiring : Wiring} (certificate : Certificate wiring)
    (p : Pins) (engine : Values SerialPackage.Output) :
    wiring.pads p engine = ArtifactTinyTapeout.pads p engine := by
  simp [Wiring.pads, certificate.outputs, canonical, canonicalOutput, Expr.eval, inputs,
    active, ArtifactTinyTapeout.pads, ArtifactTinyTapeout.Pins.active,
    BitVec.ofBool_and_ofBool, zero_append]
  cases ena : p.ena <;> cases rst : p.rstN
  all_goals simp_all
  done

theorem Certificate.step_eq {M : Type} {wiring : Wiring} (certificate : Certificate wiring)
    {engine : ArtifactPackageWiring.Wiring} (engineCertificate : ArtifactPackageWiring.Certificate engine)
    (components : ArtifactPackage.Components) (memory : Memory.SinglePort.Contract M 6 64)
    (s : ArtifactPackage.State M) (p : Pins) :
    wiring.step engine components memory s p = ArtifactTinyTapeout.step components memory s p := by
  simp only [Wiring.step, certificate.enginePins_eq, engineCertificate.step_eq, ArtifactTinyTapeout.step]
  done

theorem Certificate.observe_eq {M : Type} {wiring : Wiring} (certificate : Certificate wiring)
    {engine : ArtifactPackageWiring.Wiring} (engineCertificate : ArtifactPackageWiring.Certificate engine)
    (components : ArtifactPackage.Components) (memory : Memory.SinglePort.Contract M 6 64)
    (s : ArtifactPackage.State M) (p : Pins) :
    wiring.observe engine components memory s p = ArtifactTinyTapeout.observe components memory s p := by
  simp only [Wiring.observe, certificate.enginePins_eq, certificate.pads_eq, ArtifactTinyTapeout.observe]
  exact congrArg (ArtifactTinyTapeout.pads p)
    (funext fun _ => funext fun output => engineCertificate.observe_eq components memory s p.enginePins output)
  done

def Wiring.run {M : Type} (wiring : Wiring) (engine : ArtifactPackageWiring.Wiring)
    (components : ArtifactPackage.Components) (memory : Memory.SinglePort.Contract M 6 64)
    (s : ArtifactPackage.State M) (pins : List Pins) : ArtifactPackage.State M :=
  pins.foldl (fun state pin => wiring.step engine components memory state pin) s

theorem Certificate.run_eq {M : Type} {wiring : Wiring} (certificate : Certificate wiring)
    {engine : ArtifactPackageWiring.Wiring} (engineCertificate : ArtifactPackageWiring.Certificate engine)
    (components : ArtifactPackage.Components) (memory : Memory.SinglePort.Contract M 6 64)
    (s : ArtifactPackage.State M) (pins : List Pins) :
    wiring.run engine components memory s pins = ArtifactTinyTapeout.run components memory s pins := by
  simp only [Wiring.run, certificate.step_eq engineCertificate, ArtifactTinyTapeout.run,
    ArtifactTinyTapeout.step, ArtifactPackage.State.run, List.foldl_map]
  done

theorem Certificate.view_step {M : Type} {wiring : Wiring} (certificate : Certificate wiring)
    {engine : ArtifactPackageWiring.Wiring} (engineCertificate : ArtifactPackageWiring.Certificate engine)
    {components : ArtifactPackage.Components} (correct : ArtifactPackage.Correct components)
    (memory : Memory.SinglePort.Contract M 6 64) (s : ArtifactPackage.State M) (p : Pins) :
    (wiring.step engine components memory s p).view memory = (s.view memory).step p.enginePins :=
  (congrArg (ArtifactPackage.State.view memory) (certificate.step_eq engineCertificate components memory s p)).trans
    (ArtifactTinyTapeout.view_step correct memory s p)

theorem Certificate.view_observe {M : Type} {wiring : Wiring} (certificate : Certificate wiring)
    {engine : ArtifactPackageWiring.Wiring} (engineCertificate : ArtifactPackageWiring.Certificate engine)
    {components : ArtifactPackage.Components} (correct : ArtifactPackage.Correct components)
    (memory : Memory.SinglePort.Contract M 6 64) (s : ArtifactPackage.State M) (p : Pins) :
    wiring.observe engine components memory s p = ArtifactTinyTapeout.referenceObserve (s.view memory) p :=
  (certificate.observe_eq engineCertificate components memory s p).trans
    (ArtifactTinyTapeout.view_observe correct memory s p)

theorem Certificate.view_run {M : Type} {wiring : Wiring} (certificate : Certificate wiring)
    {engine : ArtifactPackageWiring.Wiring} (engineCertificate : ArtifactPackageWiring.Certificate engine)
    {components : ArtifactPackage.Components} (correct : ArtifactPackage.Correct components)
    (memory : Memory.SinglePort.Contract M 6 64) (s : ArtifactPackage.State M) (pins : List Pins) :
    (wiring.run engine components memory s pins).view memory = (s.view memory).run (pins.map Pins.enginePins) :=
  (congrArg (ArtifactPackage.State.view memory) (certificate.run_eq engineCertificate components memory s pins)).trans
    (ArtifactTinyTapeout.view_run correct memory s pins)

end Pinwheel.Hardware.Buffered.ArtifactTinyTapeoutWiring
