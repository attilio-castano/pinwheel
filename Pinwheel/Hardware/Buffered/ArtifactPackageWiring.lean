import Pinwheel.Hardware.Buffered.ArtifactPackage

/-! A finite typed wiring description for the restricted stateless serial/SRAM
wrapper. The decoder of Verilog into this description is an explicit trusted
interpretation boundary. Actual generated descriptions must supply Certificate;
the evaluator below follows their port selections rather than substituting a
preselected matching package. Fixed clock/macro conditions delimit this model. -/
namespace Pinwheel.Hardware.Buffered.ArtifactPackageWiring
open Pinwheel.Hardware

inductive Physical : Nat → Type where
  | initialize : Physical 1 | csn : Physical 1 | sck : Physical 1
  | mosi : Physical 1 | rawInputs : Physical 2
  deriving DecidableEq

def Physical.eval (p : SerialPackage.Pins) : Physical w → BitVec w
  | .initialize => BitVec.ofBool p.cold
  | .csn => BitVec.ofBool p.csn
  | .sck => BitVec.ofBool p.sck
  | .mosi => BitVec.ofBool p.mosi
  | .rawInputs => p.rawInputs

inductive FrontSource : Nat → Type where
  | physical : Physical w → FrontSource w
  | status : Reactive.Output w → FrontSource w

def FrontSource.eval (p : SerialPackage.Pins) (status : Values Reactive.Output) :
    FrontSource w → BitVec w
  | .physical port => port.eval p
  | .status output => status output

inductive CoreSource : Nat → Type where
  | frontend : Serial.Output w → CoreSource w
  | memory : Bool → CoreSource 64

def CoreSource.eval (frontend : Values Serial.Output) (q : Bool → BitVec 64) :
    CoreSource w → BitVec w
  | .frontend output => frontend output
  | .memory port => q port

inductive PublicSource : Nat → Type where
  | frontend : Serial.Output w → PublicSource w
  | status : Reactive.Output w → PublicSource w

def PublicSource.eval (frontend : Values Serial.Output) (status : Values Reactive.Output) :
    PublicSource w → BitVec w
  | .frontend output => frontend output
  | .status output => status output

structure Port where
  name : String
  width : Nat
  input : Bool
  deriving DecidableEq

structure Constant where
  name : String
  width : Nat
  value : Nat
  deriving DecidableEq

structure Macro where
  name : String
  kind : String
  clock : String
  constants : List Constant
  address : Sram.Port 6
  data : Sram.Port 64
  write : Sram.Port 1
  read : Sram.Port 1

structure Wiring where
  name : String
  interface : List Port
  instances : List (String × String)
  frontendClock : String
  controllerClock : String
  frontend : {w : Nat} → Serial.Input w → FrontSource w
  controller : {w : Nat} → Sram.Input w → CoreSource w
  macros : Bool → Macro
  outputs : {w : Nat} → SerialPackage.Output w → PublicSource w

def interface : List Port :=
  [⟨"clk",1,true⟩,⟨"initialize",1,true⟩,⟨"csn",1,true⟩,⟨"sck",1,true⟩,
    ⟨"mosi",1,true⟩,⟨"raw_inputs",2,true⟩,⟨"miso",1,false⟩,⟨"ready",1,false⟩,
    ⟨"busy",1,false⟩,⟨"levels",3,false⟩,⟨"enabled",3,false⟩]

def macroConstants : List Constant :=
  [⟨"A_MEN",1,1⟩,⟨"A_DLY",1,1⟩,⟨"A_BM",64,2^64-1⟩,
    ⟨"A_BIST_CLK",1,0⟩,⟨"A_BIST_EN",1,0⟩,⟨"A_BIST_MEN",1,0⟩,
    ⟨"A_BIST_WEN",1,0⟩,⟨"A_BIST_REN",1,0⟩,⟨"A_BIST_ADDR",6,0⟩,
    ⟨"A_BIST_DIN",64,0⟩,⟨"A_BIST_BM",64,0⟩]

def canonicalFrontend : Serial.Input w → FrontSource w
  | .initialize => .physical .initialize | .csn => .physical .csn
  | .sck => .physical .sck | .mosi => .physical .mosi
  | .rawInputs => .physical .rawInputs | .status output => .status output

def canonicalController : Sram.Input w → CoreSource w
  | .base port => .frontend (.core port)
  | .q port => .memory port

def canonicalMacro (port : Bool) : Macro :=
  ⟨if port then "storage1" else "storage0", "RM_IHPSG13_1P_64x64_c2_bm_bist", "clk",
    macroConstants, .address port, .data, .write, .read⟩

def canonicalOutput : SerialPackage.Output w → PublicSource w
  | .miso => .frontend .miso | .ready => .frontend .ready
  | .busy => .status .busy | .levels => .status .levels | .enabled => .status .enabled

def canonical : Wiring :=
  ⟨"pinwheel_buffered_shared_branches_sram_serial", interface,
    [("frontend","pinwheel_buffered_sram_serial_frontend"),
      ("controller","pinwheel_buffered_shared_branches_sram_controller"),
      ("memory","pinwheel_buffered_sram_memory")],
    "clk", "clk", canonicalFrontend, canonicalController, canonicalMacro, canonicalOutput⟩

structure Certificate (wiring : Wiring) : Prop where
  name : wiring.name = canonical.name
  interface : wiring.interface = canonical.interface
  instances : wiring.instances = canonical.instances
  frontendClock : wiring.frontendClock = "clk"
  controllerClock : wiring.controllerClock = "clk"
  frontend : ∀ {w} (port : Serial.Input w), wiring.frontend port = canonical.frontend port
  controller : ∀ {w} (port : Sram.Input w), wiring.controller port = canonical.controller port
  macroName : ∀ port, (wiring.macros port).name = (canonicalMacro port).name
  macroKind : ∀ port, (wiring.macros port).kind = (canonicalMacro port).kind
  macroClock : ∀ port, (wiring.macros port).clock = "clk"
  macroConstants : ∀ port, (wiring.macros port).constants = macroConstants
  macroAddress : ∀ port, (wiring.macros port).address = .address port
  macroData : ∀ port, (wiring.macros port).data = .data
  macroWrite : ∀ port, (wiring.macros port).write = .write
  macroRead : ∀ port, (wiring.macros port).read = .read
  outputs : ∀ {w} (port : SerialPackage.Output w), wiring.outputs port = canonical.outputs port

def Wiring.frontendInputs (wiring : Wiring) (p : SerialPackage.Pins)
    (status : Values Reactive.Output) : Values Serial.Input :=
  fun port => (wiring.frontend port).eval p status

def Wiring.controllerInputs {M : Type} (wiring : Wiring) (components : ArtifactPackage.Components)
    (memory : Memory.SinglePort.Contract M 6 64) (s : ArtifactPackage.State M)
    (p : SerialPackage.Pins) : Values Sram.Input :=
  fun port => (wiring.controller port).eval
    (components.frontend.observe (wiring.frontendInputs p (fun _ => 0)) s.frontend)
    (fun port => (memory.view (s.arrays (SramState.port port))).q)

def Wiring.status {M : Type} (wiring : Wiring) (components : ArtifactPackage.Components)
    (memory : Memory.SinglePort.Contract M 6 64) (s : ArtifactPackage.State M)
    (p : SerialPackage.Pins) : Values Reactive.Output :=
  fun output => components.controller.observe (wiring.controllerInputs components memory s p)
    s.controller (.base output)

def Wiring.command (wiring : Wiring) (controller : ArtifactPackage.Behavior Sram.Input Sram.Register Sram.Output)
    (i : Values Sram.Input) (r : Values Sram.Register) (port : Bool) : Memory.SinglePort.Command 6 64 :=
  let selected := wiring.macros port
  if controller.observe i r (.port selected.write) = 1 then
    .write (controller.observe i r (.port selected.address)) (controller.observe i r (.port selected.data))
  else if controller.observe i r (.port selected.read) = 1 then
    .read (controller.observe i r (.port selected.address))
  else .idle

def Wiring.step {M : Type} (wiring : Wiring) (components : ArtifactPackage.Components)
    (memory : Memory.SinglePort.Contract M 6 64) (s : ArtifactPackage.State M)
    (p : SerialPackage.Pins) : ArtifactPackage.State M :=
  ⟨components.frontend.step (wiring.frontendInputs p (wiring.status components memory s p)) s.frontend,
    components.controller.step (wiring.controllerInputs components memory s p) s.controller,
    fun port => memory.advance (wiring.command components.controller
      (wiring.controllerInputs components memory s p) s.controller (decide (port = 1))) (s.arrays port)⟩

def Wiring.observe {M : Type} (wiring : Wiring) (components : ArtifactPackage.Components)
    (memory : Memory.SinglePort.Contract M 6 64) (s : ArtifactPackage.State M)
    (p : SerialPackage.Pins) : Values SerialPackage.Output :=
  fun output => (wiring.outputs output).eval
    (components.frontend.observe (wiring.frontendInputs p (wiring.status components memory s p)) s.frontend)
    (wiring.status components memory s p)

theorem Certificate.frontendInputs_eq {wiring : Wiring} (certificate : Certificate wiring)
    (p : SerialPackage.Pins) (status : Values Reactive.Output) :
    (wiring.frontendInputs p status : Values Serial.Input) =
      ((p.inputs status).values : Values Serial.Input) := by
  funext w port
  simp only [Wiring.frontendInputs, certificate.frontend, canonical]
  cases port <;> rfl
  done

theorem Certificate.controllerInputs_eq {M : Type} {wiring : Wiring} (certificate : Certificate wiring)
    (components : ArtifactPackage.Components) (memory : Memory.SinglePort.Contract M 6 64)
    (s : ArtifactPackage.State M) (p : SerialPackage.Pins) :
    (wiring.controllerInputs components memory s p : Values Sram.Input) =
      (s.controllerInputs components memory p : Values Sram.Input) := by
  funext w port
  simp only [Wiring.controllerInputs, certificate.controller, canonical, certificate.frontendInputs_eq]
  cases port <;> rfl
  done

theorem Certificate.status_eq {M : Type} {wiring : Wiring} (certificate : Certificate wiring)
    (components : ArtifactPackage.Components) (memory : Memory.SinglePort.Contract M 6 64)
    (s : ArtifactPackage.State M) (p : SerialPackage.Pins) :
    (wiring.status components memory s p : Values Reactive.Output) =
      (s.status components memory p : Values Reactive.Output) := by
  funext w output
  simp only [Wiring.status, certificate.controllerInputs_eq, ArtifactPackage.State.status]
  done

theorem Certificate.command_eq {wiring : Wiring} (certificate : Certificate wiring)
    (controller : ArtifactPackage.Behavior Sram.Input Sram.Register Sram.Output)
    (i : Values Sram.Input) (r : Values Sram.Register) (port : Bool) :
    wiring.command controller i r port = ArtifactPackage.command controller i r port := by
  simp only [Wiring.command, certificate.macroWrite, certificate.macroRead,
    certificate.macroAddress, certificate.macroData, ArtifactPackage.command]
  done

theorem Certificate.step_eq {M : Type} {wiring : Wiring} (certificate : Certificate wiring)
    (components : ArtifactPackage.Components) (memory : Memory.SinglePort.Contract M 6 64)
    (s : ArtifactPackage.State M) (p : SerialPackage.Pins) :
    wiring.step components memory s p = s.step components memory p := by
  simp only [Wiring.step, certificate.frontendInputs_eq, certificate.status_eq,
    certificate.controllerInputs_eq, certificate.command_eq, ArtifactPackage.State.step,
    ArtifactPackage.State.frontendInputs]
  done

theorem Certificate.observe_eq {M : Type} {wiring : Wiring} (certificate : Certificate wiring)
    (components : ArtifactPackage.Components) (memory : Memory.SinglePort.Contract M 6 64)
    (s : ArtifactPackage.State M) (p : SerialPackage.Pins) (output : SerialPackage.Output w) :
    wiring.observe components memory s p output = s.observe components memory p output := by
  simp only [Wiring.observe, certificate.outputs, canonical, certificate.frontendInputs_eq,
    certificate.status_eq]
  cases output <;> rfl
  done

def Wiring.run {M : Type} (wiring : Wiring) (components : ArtifactPackage.Components)
    (memory : Memory.SinglePort.Contract M 6 64) (s : ArtifactPackage.State M)
    (pins : List SerialPackage.Pins) : ArtifactPackage.State M :=
  pins.foldl (fun state pin => wiring.step components memory state pin) s

theorem Certificate.run_eq {M : Type} {wiring : Wiring} (certificate : Certificate wiring)
    (components : ArtifactPackage.Components) (memory : Memory.SinglePort.Contract M 6 64)
    (s : ArtifactPackage.State M) (pins : List SerialPackage.Pins) :
    wiring.run components memory s pins = s.run components memory pins := by
  simp only [Wiring.run, certificate.step_eq, ArtifactPackage.State.run]
  done

theorem Certificate.view_step {M : Type} {wiring : Wiring} (certificate : Certificate wiring)
    {components : ArtifactPackage.Components} (correct : ArtifactPackage.Correct components)
    (memory : Memory.SinglePort.Contract M 6 64) (s : ArtifactPackage.State M) (p : SerialPackage.Pins) :
    (wiring.step components memory s p).view memory = (s.view memory).step p :=
  (congrArg (ArtifactPackage.State.view memory) (certificate.step_eq components memory s p)).trans
    (s.view_step correct memory p)

theorem Certificate.view_observe {M : Type} {wiring : Wiring} (certificate : Certificate wiring)
    {components : ArtifactPackage.Components} (correct : ArtifactPackage.Correct components)
    (memory : Memory.SinglePort.Contract M 6 64) (s : ArtifactPackage.State M) (p : SerialPackage.Pins)
    (output : SerialPackage.Output w) :
    wiring.observe components memory s p output = (s.view memory).observe p output :=
  (certificate.observe_eq components memory s p output).trans (s.view_observe correct memory p output)

theorem Certificate.view_run {M : Type} {wiring : Wiring} (certificate : Certificate wiring)
    {components : ArtifactPackage.Components} (correct : ArtifactPackage.Correct components)
    (memory : Memory.SinglePort.Contract M 6 64) (s : ArtifactPackage.State M)
    (pins : List SerialPackage.Pins) :
    (wiring.run components memory s pins).view memory = (s.view memory).run pins :=
  (congrArg (ArtifactPackage.State.view memory) (certificate.run_eq components memory s pins)).trans
    (s.view_run correct memory pins)

end Pinwheel.Hardware.Buffered.ArtifactPackageWiring
