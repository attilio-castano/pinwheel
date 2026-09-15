import Pinwheel.Hardware.Reactive.Refinement

namespace Pinwheel.Hardware.Reactive.Core

inductive Input : Nat → Type where
  | reset : Input 1 | start : Input 1 | incoming : Input 2
  | write : Input 1 | bank : Input 2 | address : Input 8 | data : Input 64

inductive Register (M : Nat → Type) : Nat → Type where
  | core : Reactive.Register w → Register M w
  | memory : M w → Register M w
  | idleLevels : Register M 3 | idleEnabled : Register M 3 | last : Register M 8

abbrev E M := Expr Input (Register M)

/-- Both alternatives expose a raw word read, sharing the E64 decoder in the scheduler. -/
structure Frontend (M : Nat → Type) where
  read : ({w : Nat} → M w → E M w) → E M 8 → E M 64
  next : {w : Nat} → M w → Expr Execution.Input M w

def direct : Frontend Execution.DirectReg :=
  ⟨fun regs address => Execution.readTree 8 (fun k => regs (.word k)) address,
   Execution.directCircuit.next⟩
def indexed : Frontend Execution.IndexedReg :=
  ⟨fun regs address => Execution.readTree 6 (fun k => regs (.word k))
    (Execution.readTree 8 (fun k => regs (.index k)) address), Execution.indexedCircuit.next⟩

def coreReg (r : Reactive.Register w) : E M w := .reg (.core r)
def memoryReg (r : M w) : E M w := .reg (.memory r)

/-- Read A feeds the current instruction. Read B depends on its decoded finish and capture. -/
def baseInputs (f : Frontend M) : {w : Nat} → Reactive.Input w → E M w
  | _, .reset => .input .reset | _, .start => .input .start | _, .incoming => .input .incoming
  | _, .idleLevels => .reg .idleLevels | _, .idleEnabled => .reg .idleEnabled | _, .last => .reg .last
  | _, .current => f.read memoryReg (coreReg .pc) | _, .successor => .lit 4

def addressB (f : Frontend M) : E M 8 := Reactive.target.bind (baseInputs f) coreReg

def schedulerInputs (f : Frontend M) : {w : Nat} → Reactive.Input w → E M w
  | _, .successor => f.read memoryReg (addressB f)
  | _, i => baseInputs f i

def busy : E M 1 := Reactive.running.bind (fun _ => .lit 0) coreReg

/-- Raw setup writes are disabled during execution, reset, or a start request. -/
def blocked : E M 1 := .inv (.band (.inv busy) (.band (.inv (.input .reset)) (.inv (.input .start))))

def memoryInputs : {w : Nat} → Execution.Input w → E M w
  | _, .write => .band (.input .write) (.zero (.slice 1 1 (by decide) (.input .bank)))
  | _, .busy => blocked | _, .indexBank => .slice 0 1 (by decide) (.input .bank)
  | _, .address => .input .address | _, .data => .input .data
  | _, .readA => .lit 0 | _, .readB => .lit 0

def metadataWrite (address : BitVec 8) : E M 1 :=
  .band (.band (.input .write) (.inv blocked))
    (.band (.equal (.input .bank) (.lit 2)) (.equal (.input .address) (.lit address)))

def circuit (f : Frontend M) : Circuit Input (Register M) Reactive.Output where
  next := fun r => match r with
    | .core r => (Reactive.circuit.next r).bind (schedulerInputs f) coreReg
    | .memory r => (f.next r).bind memoryInputs memoryReg
    | .idleLevels => .mux (metadataWrite 0) (.slice 0 3 (by decide) (.input .data)) (.reg .idleLevels)
    | .idleEnabled => .mux (metadataWrite 0) (.slice 3 3 (by decide) (.input .data)) (.reg .idleEnabled)
    | .last => .mux (metadataWrite 1) (.slice 0 8 (by decide) (.input .data)) (.reg .last)
  output := fun o => (Reactive.circuit.output o).bind (schedulerInputs f) coreReg

structure Inputs where
  request : Reactive.Request := {}
  write : Bool := false
  bank : BitVec 2 := 0
  address : BitVec 8 := 0
  data : BitVec 64 := 0
  deriving Repr

def Inputs.values (i : Inputs) : Values Input
  | _, .reset => BitVec.ofBool i.request.reset | _, .start => BitVec.ofBool i.request.start
  | _, .incoming => i.request.incoming | _, .write => BitVec.ofBool i.write
  | _, .bank => i.bank | _, .address => i.address | _, .data => i.data

def values (s : Reactive.State) (memory : Values M) (idle : Engine.Reactive.Pins) (last : BitVec 8) : Values (Register M)
  | _, .core r => s.values r | _, .memory r => memory r
  | _, .idleLevels => idle.levels | _, .idleEnabled => idle.enabled | _, .last => last

/-- Initial memory contents are a proof premise, not assumed power-up initialization. -/
def represents (p : Program) (memory : Values M) (f : Frontend M) : Prop :=
  ∀ (i : Inputs) (s : Reactive.State) (address : E M 8),
    (f.read memoryReg address).eval i.values (values s memory p.idle (BitVec.ofFin p.last)) =
      Execution.encode (p.fetch ((address.eval i.values (values s memory p.idle (BitVec.ofFin p.last))).toFin))

end Pinwheel.Hardware.Reactive.Core
