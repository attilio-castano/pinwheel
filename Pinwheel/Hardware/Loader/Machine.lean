import Pinwheel.Hardware.Loader.Store
import Pinwheel.Hardware.Reactive.Fetch

namespace Pinwheel.Hardware.Loader.Machine

inductive Input : Nat → Type where
  | init : Input 1 | reset : Input 1 | command : Input 3 | data : Input 64 | incoming : Input 2
inductive Register : Nat → Type where
  | control : Loader.Register w → Register w
  | core : Reactive.Register w → Register w
  | memory : Bool → Store.Register w → Register w
inductive Output : Nat → Type where
  | control : Loader.Output w → Output w
  | core : Reactive.Output w → Output w

structure Inputs where
  init : Bool := false
  reset : Bool := false
  command : BitVec 3 := 0
  data : BitVec 64 := 0
  incoming : BitVec 2 := 0
  deriving Repr

structure State where
  control : Loader.State
  core : Reactive.State
  memory : Bool → Store.Image

def Inputs.values (i : Inputs) : Values Input
  | _, .init => BitVec.ofBool i.init | _, .reset => BitVec.ofBool i.reset
  | _, .command => i.command | _, .data => i.data | _, .incoming => i.incoming
def State.values (s : State) : Values Register
  | _, .control r => s.control.values r | _, .core r => s.core.values r
  | _, .memory b r => s.memory b r

def controlInput (i : Inputs) (s : State) : Loader.Inputs :=
  ⟨i.init, i.reset, Reactive.runningValue s.core, i.command, i.data⟩
def committing (i : Inputs) (s : State) : Bool := Loader.commit (controlInput i s) s.control
def selected (i : Inputs) (s : State) : Bool := if committing i s then !s.control.active else s.control.active
def usable (i : Inputs) (s : State) : Bool := !i.init && (s.control.valid || committing i s)
def memoryInput (i : Inputs) (s : State) (b : Bool) : Store.Inputs :=
  ⟨Loader.push (controlInput i s) s.control && (b != s.control.active), s.control.cursor, i.data, 0⟩
def baseInput (i : Inputs) (s : State) : Reactive.Inputs :=
  let m : Store.Image := s.memory (selected i s)
  { reset := i.init || i.reset || !s.control.valid || committing i s
    start := Loader.start (controlInput i s) s.control
    incoming := i.incoming
    idle := if usable i s then ⟨(m .idle).extractLsb' 0 3, (m .idle).extractLsb' 3 3⟩ else {}
    last := m .last
    current := Store.read m s.core.pc
    successor := 4 }
def schedulerInput (i : Inputs) (s : State) : Reactive.Inputs :=
  Reactive.Fetch.resolve (baseInput i s) s.core (Store.read (s.memory (selected i s)))

/-- Functional atomic loader plus the existing scheduler equations. -/
def next (i : Inputs) (s : State) : State :=
  ⟨Loader.next (controlInput i s) s.control,
    Reactive.stepValue (schedulerInput i s) s.core,
    fun b => Store.tick (memoryInput i s b) (s.memory b)⟩

abbrev E := Expr Input Register
def controlReg : {w : Nat} → Loader.Register w → E w := fun r => .reg (.control r)
def coreReg : {w : Nat} → Reactive.Register w → E w := fun r => .reg (.core r)
def memoryReg (b : Bool) : {w : Nat} → Store.Register w → E w := fun r => .reg (.memory b r)
def controlInputs : {w : Nat} → Loader.Input w → E w
  | _, .init => .input .init | _, .reset => .input .reset | _, .command => .input .command
  | _, .data => .input .data
  | _, .busy => Reactive.running.bind (fun _ => .lit 0) coreReg
def commitGate : E 1 := Loader.commitGate.bind controlInputs controlReg
def pushGate : E 1 := Loader.pushGate.bind controlInputs controlReg
def selectedGate : E 1 := .mux commitGate (.inv (controlReg .active)) (controlReg .active)
def usableGate : E 1 := .band (.inv (.input .init)) (Execution.bor (controlReg .valid) commitGate)
def chosen : {w : Nat} → Store.Register w → E w :=
  fun r => .mux selectedGate (memoryReg true r) (memoryReg false r)
def readExpr (address : E 8) : E 64 :=
  Execution.readTree 6 (fun k => chosen (.word k)) (Execution.readTree 8 (fun k => chosen (.index k)) address)
def memoryInputs (b : Bool) : {w : Nat} → Store.Input w → E w
  | _, .write => .band pushGate (.inv (.equal (controlReg .active) (.lit (BitVec.ofBool b))))
  | _, .cursor => controlReg .cursor | _, .data => .input .data | _, .address => .lit 0
def baseInputs : {w : Nat} → Reactive.Input w → E w
  | _, .reset => Execution.bor (.input .init) (Execution.bor (.input .reset) (Execution.bor (.inv (controlReg .valid)) commitGate))
  | _, .start => Loader.startGate.bind controlInputs controlReg
  | _, .incoming => .input .incoming
  | _, .idleLevels => .mux usableGate (.slice 0 3 (by decide) (chosen .idle)) (.lit 0)
  | _, .idleEnabled => .mux usableGate (.slice 3 3 (by decide) (chosen .idle)) (.lit 0)
  | _, .last => chosen .last
  | _, .current => readExpr (coreReg .pc)
  | _, .successor => .lit 4
def addressB : E 8 := Reactive.target.bind baseInputs coreReg
def schedulerInputs : {w : Nat} → Reactive.Input w → E w
  | _, .successor => readExpr addressB
  | _, r => baseInputs r

def circuit : Circuit Input Register Output where
  next := fun r => match r with
    | .control r => (Loader.circuit.next r).bind controlInputs controlReg
    | .core r => (Reactive.circuit.next r).bind schedulerInputs coreReg
    | .memory b r => (Store.next r).bind (memoryInputs b) (memoryReg b)
  output := fun o => match o with
    | .control o => (Loader.circuit.output o).bind controlInputs controlReg
    | .core o => (Reactive.circuit.output o).bind schedulerInputs coreReg

end Pinwheel.Hardware.Loader.Machine
