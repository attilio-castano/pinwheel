import Pinwheel.Engine.Counted
import Pinwheel.Program.Transfer

/-! Reference execution composing the existing reactive instruction semantics,
the counted virtual-address decoder, and the finite transfer owner. There is no
encoded chip image here. A virtual span is not a stored-word or wire-edge count.
Inputs pass through two sampler registers; each entry sees the pre-edge second
register. Control scratch captures and appended RX data are distinct stores. -/
namespace Pinwheel.Program.Buffered
open Pinwheel.Engine.Reactive

abbrev PC := Fin 1024
abbrev ScratchCapture := Capture 15

inductive Target where
  | absolute (pc : PC)
  | next
  deriving DecidableEq, Repr

def Target.eval (target : Target) (pc : PC) : Option PC :=
  match target with
  | .absolute target => some target
  | .next => if h : pc.val + 1 < 1024 then some ⟨pc.val + 1, h⟩ else none

inductive Finish where
  | sequential
  | jump (target : PC)
  | branch (sample : Fin 16) (whenTrue whenFalse : Target)
  deriving DecidableEq, Repr

def Finish.eval (finish : Finish) (pc : PC) : Option (Engine.Reactive.Finish 1023 15) := do
  match finish with
  | .sequential => return .sequential
  | .jump target => return .jump target
  | .branch sample yes no => return .branch sample (← yes.eval pc) (← no.eval pc)

inductive Failure where
  | fault | timeout
  deriving DecidableEq, Repr

def Failure.outcome : Failure → Transfer.Outcome
  | .fault => .fault
  | .timeout => .timeout

inductive Operation where
  | drive (action : Action 15)
  | shift (output : Fin 3) (enable invert : Bool) (action : Action 15)
  | keep (preserveLevels preserveEnabled : BitVec 3) (action : Action 15)
  | wait (wait : Wait)
  | checked (action : Action 15) (guard : Check) (terminalCapture : Option ScratchCapture)
      (finish : Finish := .sequential)
  | qualify (qualify : Qualify)
  | halt
  | fault (reason : Failure := .fault)
  deriving DecidableEq, Repr

structure Instruction where
  operation : Operation
  append : Option (Fin 2) := none
  preserveLevels : BitVec 3 := 0
  preserveEnabled : BitVec 3 := 0
  deriving DecidableEq, Repr

structure Program where
  code : Engine.Reactive.Counted.Schedule Instruction
  idle : Pins
  fits : code.span ≤ 1024
  nodesFit : code.nodes ≤ 256
  nestingFit : code.nesting ≤ 2
  deriving Repr

def Program.fetch (p : Program) (pc : PC) : Option Instruction :=
  (p.code.locate (Vector.replicate 2 0) pc.val).map Prod.fst

def Program.last (p : Program) : PC := ⟨p.code.span - 1, by have := p.fits; omega⟩

structure State where
  core : Engine.Reactive.State 1023 15
  buffers : Transfer.State
  owner : Transfer.Identity
  samplerFirst : Inputs := 3
  samplerSecond : Inputs := 3
  deriving DecidableEq, Repr

def owned (s : State) : Bool :=
  match s.buffers.slot with
  | .running e => e.request.identity == s.owner
  | _ => false

def txBit (s : State) : Bool :=
  match s.buffers.slot with
  | .running e => e.request.tx[e.txConsumed]?.getD false
  | _ => false

def setBit (old : BitVec 3) (pin : Fin 3) (value : Bool) : BitVec 3 :=
  let mask := BitVec.ofNat 3 (2 ^ pin.val)
  (old &&& ~~~mask) ||| (if value then mask else 0)

def shiftPins (pins : Pins) (pin : Fin 3) (enable invert bit : Bool) : Pins :=
  if enable then {pins with enabled := setBit pins.enabled pin (bit != invert)}
  else {pins with levels := setBit pins.levels pin (bit != invert)}

def keepPins (pins old : Pins) (levels enabled : BitVec 3) : Pins :=
  ⟨(pins.levels &&& ~~~levels) ||| (old.levels &&& levels),
   (pins.enabled &&& ~~~enabled) ||| (old.enabled &&& enabled)⟩

def normalize (s : State) (pc : PC) (instruction : Instruction) :
    Option (Engine.Reactive.Instruction 1023 15) := do
  match instruction.operation with
  | .drive action => return .action action
  | .shift output enable invert action =>
    return .action {action with pins := shiftPins action.pins output enable invert (txBit s)}
  | .keep levels enabled action =>
    return .action {action with pins := keepPins action.pins s.core.pins levels enabled}
  | .wait wait => return .wait {wait with
      pins := keepPins wait.pins s.core.pins instruction.preserveLevels instruction.preserveEnabled}
  | .checked action guard terminal finish =>
    return .checked ⟨{action with
      pins := keepPins action.pins s.core.pins instruction.preserveLevels instruction.preserveEnabled},
      guard, terminal, ← finish.eval pc⟩
  | .qualify qualify => return .qualify {qualify with
      pins := keepPins qualify.pins s.core.pins instruction.preserveLevels instruction.preserveEnabled}
  | .halt | .fault _ => return .halt

def lower (p : Program) (s : State) : Engine.Reactive.Fetch.Store 1023 15 :=
  ⟨fun pc => p.fetch pc >>= normalize s pc, p.idle, p.last⟩

def terminal (p : Program) (capacity : Transfer.Capacity) (s : State) (outcome : Transfer.Outcome) : State :=
  let reason := match outcome with
    | .complete => Stop.completed | .fault => Stop.fault | .timeout => Stop.timeout
  {s with
    core := Engine.Reactive.Fetch.stop (lower p s) reason s.core.samples
    buffers := (Transfer.step capacity s.buffers (.finish s.owner outcome)).state}

/-- Completion preserves the owned TX/RX prefix. Engine testimony is distinct
from a protocol-success or full-result predicate. -/
def settle (p : Program) (capacity : Transfer.Capacity) (s : State) : State :=
  match s.core.control with
  | .stopped .completed => terminal p capacity s .complete
  | .stopped .fault => terminal p capacity s .fault
  | .stopped .timeout => terminal p capacity s .timeout
  | _ => s

def consumed (capacity : Transfer.Capacity) (s : State) : State × Bool :=
  let edge := Transfer.step capacity s.buffers (.consumeTx s.owner)
  ({s with buffers := edge.state}, match edge.reply with | .txBit _ => true | _ => false)

def appended (capacity : Transfer.Capacity) (s : State) (input : Fin 2) (sampled : Inputs) : State × Bool :=
  let edge := Transfer.step capacity s.buffers (.appendRx s.owner sampled[input.val])
  ({s with buffers := edge.state}, edge.reply == .rxStored)

/-- Scratch entry captures have already been applied by Reactive.enter.
TX is consumed before RX append. If append overflows, a consumed TX bit remains
in diagnostics; either datapath failure restores idle and retains a fault. -/
def entryEffects (p : Program) (capacity : Transfer.Capacity) (s : State) (pc : PC)
    (sampled : Inputs) : State :=
  if s.core.control == .stopped .fault then s
  else
    match p.fetch pc with
    | none => terminal p capacity s .fault
    | some instruction =>
      match instruction.operation with
      | .fault reason => terminal p capacity s reason.outcome
      | .halt => s
      | operation =>
        let (s, consumedOk) := match operation with
          | .shift .. => consumed capacity s
          | _ => (s, true)
        if !consumedOk then terminal p capacity s .fault
        else match instruction.append with
          | none => s
          | some input =>
            let (s, appendedOk) := appended capacity s input sampled
            if appendedOk then s else terminal p capacity s .fault

def sequentialTarget (p : Program) (pc : PC) : Option PC :=
  if h : pc.val < p.last.val then some ⟨pc.val + 1, by have := pc.isLt; omega⟩ else none

def finishTarget (p : Program) (pc : PC) (finish : Finish)
    (samples : Vector Bool 16) : Option PC :=
  let target := match finish with
    | .sequential => sequentialTarget p pc
    | .jump target => some target
    | .branch sample yes no => (if samples[sample.val] then yes else no).eval pc
  target.filter fun pc => pc.val ≤ p.last.val

/-- An entry event is about dispatch, not a change in PEngine.Reactive.Counted. A terminal self jump
therefore consumes/appends again even though its numerical address is equal. -/
def entryTarget (p : Program) (s : State) (sampled : Inputs) : Option PC :=
  match s.core.control with
  | .stopped _ => none
  | .active pc remaining => if remaining.val == 0 then sequentialTarget p pc else none
  | .waiting pc _ => match p.fetch pc with
    | some {operation := .wait wait, ..} => if wait.condition.ready sampled then sequentialTarget p pc else none
    | _ => none
  | .checked pc remaining => match p.fetch pc with
    | some {operation := .checked _ guard terminal finish, ..} =>
      if guard.ready sampled && remaining.val == 0 then
        finishTarget p pc finish (capture s.core.samples terminal sampled)
      else none
    | _ => none
  | .qualifying pc remaining _ => match p.fetch pc with
    | some {operation := .qualify qualify, ..} =>
      if qualify.condition.ready sampled && remaining.val == 0 then sequentialTarget p pc else none
    | _ => none

def initial (p : Program) (buffers : Transfer.State) (owner : Transfer.Identity) : State :=
  ⟨⟨.stopped .ready, p.idle, Vector.replicate 16 false⟩, buffers, owner, 3, 3⟩

/-- The caller supplies a running slot admitted by Transfer.start. Stale owners
cannot enter or mutate the data path. -/
def start (p : Program) (capacity : Transfer.Capacity) (s : State) : State :=
  if owned s then
    let core := Engine.Reactive.Fetch.start (lower p s) s.samplerSecond
    settle p capacity (entryEffects p capacity {s with core} 0 s.samplerSecond)
  else s

def advance (p : Program) (capacity : Transfer.Capacity) (s : State) (incoming : Inputs) : State :=
  if owned s && busy s.core then
    let sampled := s.samplerSecond
    let next := {s with
      core := Engine.Reactive.Fetch.advance (lower p s) s.core sampled
      samplerFirst := incoming
      samplerSecond := s.samplerFirst}
    let next := match entryTarget p s sampled with
      | none => next
      | some pc => entryEffects p capacity next pc sampled
    settle p capacity next
  else s

def run (p : Program) (capacity : Transfer.Capacity) (s : State) (incoming : Nat → Inputs) : Nat → State
  | 0 => s
  | n + 1 => advance p capacity (run p capacity s incoming n) (incoming n)

end Pinwheel.Program.Buffered
