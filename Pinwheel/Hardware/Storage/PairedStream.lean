import Pinwheel.Hardware.Storage.PairedPackage

/-! Opt-in command supervisor for the unchanged paired-validation core.
Command 6 with the exact word 1 arms and starts a stopped committed program;
the exact word 0 stops and resets execution. An enabled session owns the engine
between completions, including its stopped edge. Only completed mode 5 rearms.
The UART interpretation additionally requires the loaded image to be the certified
RX compiler image. The existing mailbox keeps its pre-edge, one-edge-late arrival.
This is a new digital candidate, without physical or analog qualification. -/
namespace Pinwheel.Hardware.Storage.PairedStream
open Pinwheel.Hardware Loader
open SramController (Reads Out bypass)
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

inductive SupervisorRegister : Nat → Type where
  | enabled : SupervisorRegister 1

abbrev Register := Extended PairedController.Register SupervisorRegister
abbrev Input := PairedController.Input
abbrev Output := Out Machine.Output
abbrev FullRegister := Extended (Chip.Register Register) HostResult.Register

structure State where
  enabled : Bool := false
  deriving DecidableEq, Repr

structure Status where
  mode : BitVec 3 := 0
  valid : Bool := false
  pending : Bool := false
  deriving DecidableEq, Repr

structure Transition where
  effective : Machine.Inputs
  state : State

def busy (status : Status) : Bool := status.mode != 0 && status.mode.toNat < 5
def stopping (input : Machine.Inputs) : Bool := input.command == 6 && input.data == 0
def resetting (input : Machine.Inputs) : Bool := input.init || input.reset || input.command == 7
def arming (state : State) (status : Status) (input : Machine.Inputs) : Bool :=
  !resetting input && input.command == 6 && input.data == 1 && !state.enabled &&
    status.valid && !status.pending && !busy status
def rearming (state : State) (status : Status) (input : Machine.Inputs) : Bool :=
  !resetting input && input.command == 0 && state.enabled && status.valid &&
    !status.pending && status.mode == 5
def failed (status : Status) : Bool := status.mode == 6 || status.mode == 7

def step (state : State) (status : Status) (input : Machine.Inputs) : Transition :=
  let start := arming state status input || rearming state status input
  let command := if stopping input then 7 else if resetting input then input.command
    else if start then 5 else if state.enabled && input.command != 0 then 6 else input.command
  let enabled := if resetting input || stopping input then false
    else if arming state status input then true else if failed status then false else state.enabled
  ⟨{input with command := command, data := if start then 0 else input.data}, ⟨enabled⟩⟩

def rawInput (input : Values Input) : Machine.Inputs :=
  ⟨input (.base .init) == 1, input (.base .reset) == 1, input (.base .command),
    input (.base .data), input (.base .incoming)⟩
def state (s : Values Register) : State := ⟨s (.extra .enabled) == 1⟩
def status (s : Values Register) : Status :=
  ⟨s (.inner .mode), s (.inner .valid) == 1, s (.inner .pending) == 1⟩
def policy (input : Values Input) (s : Values Register) : Transition :=
  step (state s) (status s) (rawInput input)
def effectiveInputs (input : Values Input) (s : Values Register) : Values Input
  | _, .base p => (policy input s).effective.values p
  | _, .q b => input (.q b)
def nextEnabled (input : Values Input) (s : Values Register) : BitVec 1 :=
  BitVec.ofBool (policy input s).state.enabled
def nextValues (input : Values Input) (s : Values Register) : Values SupervisorRegister
  | _, .enabled => nextEnabled input s

abbrev E := Expr Input Register
def both (a b : E 1) : E 1 := .band a b
def either (a b : E w) : E w := .inv (.band (.inv a) (.inv b))
def commandIs (value : BitVec 3) : E 1 := .equal (.input (.base .command)) (.lit value)
def stoppingExpr : E 1 := both (commandIs 6) (.equal (.input (.base .data)) (.lit 0))
def resettingExpr : E 1 := either (.input (.base .init))
  (either (.input (.base .reset)) (commandIs 7))
def busyExpr : E 1 := both (.inv (.zero (.reg (.inner .mode))))
  (.ult (.reg (.inner .mode)) (.lit 5))
def armingExpr : E 1 := both (.inv resettingExpr) (both (commandIs 6)
  (both (.equal (.input (.base .data)) (.lit 1)) (both (.inv (.reg (.extra .enabled)))
    (both (.reg (.inner .valid)) (both (.inv (.reg (.inner .pending))) (.inv busyExpr))))))
def rearmingExpr : E 1 := both (.inv resettingExpr) (both (commandIs 0)
  (both (.reg (.extra .enabled)) (both (.reg (.inner .valid))
    (both (.inv (.reg (.inner .pending))) (.equal (.reg (.inner .mode)) (.lit 5))))))
def startExpr : E 1 := either armingExpr rearmingExpr
def failedExpr : E 1 := either (.equal (.reg (.inner .mode)) (.lit 6))
  (.equal (.reg (.inner .mode)) (.lit 7))
def commandExpr : E 3 := .mux stoppingExpr (.lit 7)
  (.mux resettingExpr (.input (.base .command)) (.mux startExpr (.lit 5)
    (.mux (both (.reg (.extra .enabled)) (.inv (commandIs 0))) (.lit 6) (.input (.base .command)))))
def nextEnabledExpr : E 1 := .mux (either resettingExpr stoppingExpr) (.lit 0)
  (.mux armingExpr (.lit 1) (.mux failedExpr (.lit 0) (.reg (.extra .enabled))))
def inputExpr : {w : Nat} → Input w → E w
  | _, .base .command => commandExpr
  | _, .base .data => .mux startExpr (.lit 0) (.input (.base .data))
  | _, p => .input p
def nextExpr : {w : Nat} → SupervisorRegister w → E w
  | _, .enabled => nextEnabledExpr

private theorem bit_value (v : BitVec 1) : BitVec.ofBool (v == 1) = v := by
  rcases PairedUpload.bit_cases v with h | h <;> simp [h]

theorem inputExpr_correct (input : Values Input) (s : Values Register) (p : Input w) :
    (inputExpr p).eval input s = effectiveInputs input s p := by
  cases p
  case base p =>
    cases p
    all_goals rcases PairedUpload.bit_cases (input (.base .init)) with hi | hi
    all_goals rcases PairedUpload.bit_cases (input (.base .reset)) with hr | hr
    all_goals rcases PairedUpload.bit_cases (s (.extra .enabled)) with he | he
    all_goals rcases PairedUpload.bit_cases (s (.inner .valid)) with hv | hv
    all_goals rcases PairedUpload.bit_cases (s (.inner .pending)) with hp | hp
    all_goals simp only [inputExpr, commandExpr, stoppingExpr, resettingExpr, startExpr, armingExpr,
      rearmingExpr, busyExpr, commandIs, both, either, Expr.eval, effectiveInputs,
      policy, step, stopping, resetting, arming, rearming, busy, rawInput, state, status,
      Machine.Inputs.values, bit_value]
    all_goals simp [hi, hr, he, hv, hp, BitVec.ofBool_and_ofBool,
      BitVec.not_ofBool, Bool.beq_eq_decide_eq, Bool.and_assoc]
    all_goals bv_normalize
    all_goals grind
    done
  case q => rfl

theorem nextExpr_correct (input : Values Input) (s : Values Register) (p : SupervisorRegister w) :
    (nextExpr p).eval input s = nextValues input s p := by
  cases p
  rcases PairedUpload.bit_cases (input (.base .init)) with hi | hi
  all_goals rcases PairedUpload.bit_cases (input (.base .reset)) with hr | hr
  all_goals rcases PairedUpload.bit_cases (s (.extra .enabled)) with he | he
  all_goals rcases PairedUpload.bit_cases (s (.inner .valid)) with hv | hv
  all_goals rcases PairedUpload.bit_cases (s (.inner .pending)) with hp | hp
  all_goals simp only [nextExpr, nextEnabledExpr, nextValues, nextEnabled, failedExpr,
    resettingExpr, stoppingExpr, armingExpr, busyExpr, commandIs, both, either, Expr.eval,
    policy, step, stopping, resetting, arming, failed, busy, rawInput, state, status]
  all_goals simp [hi, hr, he, hv, hp, BitVec.ofBool_and_ofBool,
    BitVec.not_ofBool, Bool.beq_eq_decide_eq, Bool.and_assoc]
  all_goals bv_normalize
  all_goals grind
  done

def wrap (n : Netlist PairedController.Register Output Input) : Netlist Register Output Input :=
  n.extend inputExpr nextExpr

def wrapped (c : PairedComposition.Component Input PairedController.Register Output) :
    PairedComposition.Component Input Register Output where
  step := fun input s => Extended.values
    (c.step (effectiveInputs input s) (Extended.innerValues s)) (nextValues input s)
  observe := fun input s => c.observe (effectiveInputs input s) (Extended.innerValues s)

theorem wrap_correct (n : Netlist PairedController.Register Output Input) :
    (wrap n).component = wrapped n.component := by
  apply congr (congrArg Timed.Component.mk ?_) ?_
  all_goals funext input s w p
  all_goals cases p
  all_goals simp only [wrap, Netlist.extend_inner, Netlist.extend_extra, Netlist.extend_observe,
    Extended.values, Netlist.component, inputExpr_correct, nextExpr_correct]
  done

def core : Except String (Netlist Register Output Input) := PairedValidation.core.map wrap
def reference := wrapped PairedComposition.graph

theorem emitted_core_correct (n : Netlist Register Output Input) (hn : core = .ok n) :
    n.component = reference := by
  cases h : PairedValidation.core
  case error =>
    simp only [core, h, Except.map] at hn
    cases hn
  case ok old =>
    simp only [core, h, Except.map, Except.ok.injEq] at hn
    subst n
    rw [wrap_correct, PairedComposition.retained_correct old h]
    rfl
  done

def enabledRegister : FullRegister 1 := .inner (.inner (.inner (.inner (.extra .enabled))))
def enabledBits (bits : BitVec 1) : BitVec 8 := 0#4 ++ (bits ++ 0#3)
def overlayExpr (value : Expr I FullRegister 8) : Expr I FullRegister 8 :=
  .mux (.equal (.reg (.extra .pageSecond)) (.lit 3))
    (.inv (.band (.inv value) (.inv (.concat (.lit (0#4))
      (.concat (.reg enabledRegister) (.lit (0#3))))))) value

/-- The unchanged result observer is followed by one status-bit overlay.
The map adds neither registers nor combinational wires. -/
def mapped : {I : Nat → Type} → Netlist FullRegister (Out Chip.Output) I →
    Netlist FullRegister (Out Chip.Output) I
  | _, .finish c => .finish {next := c.next, output := fun {w} p => match w, p with
      | _, .base .uoOut => overlayExpr (c.output (.base .uoOut))
      | _, p => c.output p}
  | _, .letWire e body => .letWire e (mapped body)

def overlay (s : Values FullRegister) (output : Values (Out Chip.Output)) : Values (Out Chip.Output)
  | _, .base .uoOut => if s (.extra .pageSecond) == 3 then
      ~~~(~~~output (.base .uoOut) &&& ~~~enabledBits (s enabledRegister)) else output (.base .uoOut)
  | _, p => output p

theorem mapped_step (n : Netlist FullRegister (Out Chip.Output) I) (input : Values I)
    (s : Values FullRegister) (r : FullRegister w) :
    (mapped n).step input s r = n.step input s r := by
  induction n <;> simp_all only [mapped, Netlist.step, Circuit.step]

theorem mapped_observe (n : Netlist FullRegister (Out Chip.Output) I) (input : Values I)
    (s : Values FullRegister) (p : Out Chip.Output w) :
    (mapped n).observe input s p = overlay s (n.observe input s) p := by
  induction n
  case finish c =>
    cases p
    case base p =>
      cases p
      all_goals simp only [mapped, Netlist.observe, Circuit.observe, overlayExpr, overlay,
        enabledBits, Expr.eval, Bool.beq_eq_decide_eq, Reactive.bool_one]
      done
    case port => rfl
    done
  case letWire e body ih =>
    simpa only [mapped, Netlist.observe] using ih (WithWire.values input (e.eval input s))
  done

def basePackage (n : Netlist Register Output Input) :=
  SramAssembly.observer.wrap ((bypass Chip.pinMap).wrap
    ((bypass Feeder.sampler).wrap ((bypass Serial.receiver).wrap n)))
def package (n : Netlist Register Output Input) := mapped (basePackage n)
def basePackaged (c : PairedComposition.Component Input Register Output) :=
  PairedComposition.observed SramAssembly.observer (PairedComposition.fed (bypass Chip.pinMap)
    (PairedComposition.fed (bypass Feeder.sampler) (PairedComposition.fed (bypass Serial.receiver) c)))
def packaged (c : PairedComposition.Component Input Register Output) :
    PairedComposition.Component (Reads Chip.Pin) FullRegister (Out Chip.Output) where
  step := (basePackaged c).step
  observe := fun input s => overlay s ((basePackaged c).observe input s)

theorem basePackage_correct (n : Netlist Register Output Input) :
    (basePackage n).component = basePackaged n.component := by
  simp only [basePackage, basePackaged, PairedComposition.observer_correct, PairedComposition.feeder_correct]

theorem package_correct (n : Netlist Register Output Input) :
    (package n).component = packaged n.component := by
  unfold package packaged
  rw [← basePackage_correct n]
  apply congr (congrArg Timed.Component.mk ?_) ?_
  all_goals funext input s w p
  all_goals simp only [Netlist.component, mapped_step, mapped_observe]
  done

theorem emitted_package_correct (n : Netlist Register Output Input) (hn : core = .ok n) :
    (package n).component = packaged reference := by
  rw [package_correct, emitted_core_correct n hn]

theorem overlay_disabled (s : Values FullRegister) (output : Values (Out Chip.Output))
    (h : s enabledRegister = 0) (p : Out Chip.Output w) : overlay s output p = output p := by
  cases p
  case base p =>
    cases p
    all_goals simp [overlay, enabledBits, h]
    all_goals bv_normalize
    done
  case port => rfl
  done

def registers : Array (Sigma Register) :=
  PairedController.registers.map (fun ⟨w,r⟩ => ⟨w,.inner r⟩) ++ #[⟨1,.extra .enabled⟩]
def label : {w : Nat} → Register w → String
  | _, .inner r => PairedController.label r
  | _, .extra .enabled => "stream_enabled"
def fullRegisters : Array (Sigma FullRegister) :=
  registers.map (fun ⟨w,r⟩ => ⟨w,.inner (.inner (.inner (.inner r)))⟩) ++
  Backend.Policy.serialRegisters.map (fun ⟨w,r⟩ => ⟨w,.inner (.inner (.inner (.extra r)))⟩) ++
  Backend.Policy.sampledRegisterList.map (fun ⟨w,r⟩ => ⟨w,.inner (.inner (.extra r))⟩) ++
  HostResult.registers.map (fun ⟨w,r⟩ => ⟨w,.extra r⟩)
def fullLabel : {w : Nat} → FullRegister w → String
  | _, .inner (.inner (.inner (.inner r))) => label r
  | _, .inner (.inner (.inner (.extra r))) => Backend.Policy.serialLabel r
  | _, .inner (.inner (.extra r)) => Backend.Policy.sampledRegisterLabel r
  | _, .inner (.extra r) => nomatch r
  | _, .extra r => HostResult.label r
def coreText : Except String String := match core with
  | .error e => .error e
  | .ok n => Netlist.moduleText "pinwheel_paired_core_controller" n
    (PairedController.inputs Machine.inputs) registers (PairedController.outputs Machine.outputs)
    (SramAssembly.inputLabel Machine.inputLabel) label (SramAssembly.outputLabel Machine.outputLabel)
def chipText : Except String String := match core with
  | .error e => .error e
  | .ok n => Netlist.moduleText "pinwheel_paired_controller" (package n)
    (PairedController.inputs Backend.Policy.chipInputs) fullRegisters
    (PairedController.outputs Backend.Policy.chipOutputs)
    (SramAssembly.inputLabel Backend.Policy.chipInputLabel) fullLabel
    (SramAssembly.outputLabel Backend.Policy.chipOutputLabel)

end Pinwheel.Hardware.Storage.PairedStream
