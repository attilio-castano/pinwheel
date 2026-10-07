import Pinwheel.Hardware.Storage.PairedResidentImage

/-! Typed resident programs for the existing paired source grammar.

Ordinary operations retain the reactive engine's timing, waits, guards, captures
and branch semantics. SHIFT and KEEP lower to an ordinary action on entry using
the pre-edge operand and output levels. The operand is updated only when SHIFT
is entered. This executable model does not assert an initialized package or
protocol lifecycle refinement. -/
namespace Pinwheel.Program.Resident
open Pinwheel.Engine.Reactive
open Pinwheel.Hardware

inductive Order where
  | lsbFirst | msbFirst
  deriving DecidableEq, Repr

def Order.isMsbFirst : Order → Bool
  | .lsbFirst => false
  | .msbFirst => true

inductive Instruction where
  | ordinary (operation : Engine.Reactive.Instruction 255 15)
  | shift (output : Fin 3) (order : Order) (durationMinusOne : Fin 256) (pins : Pins)
  | keep (preserve : BitVec 3) (pins : Pins) (capture : Option (Capture 15))
      (durationMinusOne : Fin 256)
  deriving DecidableEq, Repr

structure Program where
  memory : Vector Instruction 256
  idle : Pins
  last : Fin 256
  deriving DecidableEq, Repr

def Program.fetch (p : Program) (pc : Fin 256) : Instruction := p.memory[pc.val]

def ordinaryProgram (p : Engine.Reactive.Program 255 15) : Program :=
  ⟨p.memory.map Instruction.ordinary, p.idle, p.last⟩

structure State where
  core : Engine.Reactive.State 255 15
  operand : BitVec 8 := 0
  deriving DecidableEq, Repr

def outputBit (order : Order) (operand : BitVec 8) : Bool :=
  operand.getLsbD (if order.isMsbFirst then 7 else 0)

def shifted (order : Order) (operand : BitVec 8) : BitVec 8 :=
  if order.isMsbFirst then operand <<< 1 else operand >>> 1

def shiftPins (output : Fin 3) (order : Order) (pins : Pins) (operand : BitVec 8) : Pins :=
  {pins with levels := (pins.levels &&& ~~~(BitVec.ofNat 3 (2 ^ output.val))) |||
    (if outputBit order operand then BitVec.ofNat 3 (2 ^ output.val) else 0)}

def keepPins (preserve : BitVec 3) (pins old : Pins) : Pins :=
  {pins with levels := (pins.levels &&& ~~~preserve) ||| (old.levels &&& preserve)}

def normalize (operand : BitVec 8) (old : Pins) : Instruction → Engine.Reactive.Instruction 255 15
  | .ordinary operation => operation
  | .shift output order duration pins => .action ⟨shiftPins output order pins operand, duration, none⟩
  | .keep preserve pins capture duration => .action ⟨keepPins preserve pins old, duration, capture⟩

def lower (p : Program) (operand : BitVec 8) (old : Pins) : Engine.Reactive.Program 255 15 :=
  ⟨p.memory.map (normalize operand old), p.idle, p.last⟩

/-- An entry event is independent of whether its target differs from the old PC.
A terminal self branch re-enters its ordinary checked instruction; dispatch to
SHIFT consumes the next owned bit. The timer, guard,
capture and successor computation themselves are delegated to Reactive.advance. -/
def dispatching (p : Program) (s : State) (inputs : Inputs) : Bool :=
  match s.core.control with
  | .stopped _ => false
  | .active _ remaining => remaining.val == 0
  | .waiting pc _ => match p.fetch pc with
    | .ordinary (.wait wait) => wait.condition.ready inputs
    | _ => false
  | .checked pc remaining => match p.fetch pc with
    | .ordinary (.checked checked) => checked.guard.ready inputs && remaining.val == 0
    | _ => false
  | .qualifying pc remaining _ => match p.fetch pc with
    | .ordinary (.qualify qualify) => qualify.condition.ready inputs && remaining.val == 0
    | _ => false

def enteredOperand (p : Program) (core : Engine.Reactive.State 255 15) (operand : BitVec 8) : BitVec 8 :=
  match core.control with
  | .active pc _ => match p.fetch pc with
    | .shift _ order _ _ => shifted order operand
    | _ => operand
  | _ => operand

def enter (p : Program) (pc : Fin 256) (s : State) (inputs : Inputs) : State :=
  let core := Engine.Reactive.enter (lower p s.operand s.core.pins) pc s.core.samples inputs
  ⟨core, enteredOperand p core s.operand⟩

def reset (p : Program) : State :=
  ⟨Engine.Reactive.reset (lower p 0 p.idle), 0⟩

/-- The caller supplies an accepted START event. It snapshots the entire owned
byte before the first instruction, clears ordinary captures and preserves the
pre-edge output levels for a first KEEP operation. -/
def start (p : Program) (s : State) (payload : BitVec 8) (inputs : Inputs) : State :=
  let core := Engine.Reactive.start (lower p payload s.core.pins) inputs
  ⟨core, enteredOperand p core payload⟩

def advance (p : Program) (s : State) (inputs : Inputs) : State :=
  let core := Engine.Reactive.advance (lower p s.operand s.core.pins) s.core inputs
  ⟨core, if dispatching p s inputs then enteredOperand p core s.operand else s.operand⟩

/-- Reset wins; a busy engine ignores START and its unowned payload. Loading,
valid-image admission, mailbox ownership and serial delivery are outside this model. -/
def step (p : Program) (s : State) (resetRequested startRequested : Bool)
    (payload : BitVec 8) (inputs : Inputs) : State :=
  if resetRequested then reset p
  else if Engine.Reactive.busy s.core then advance p s inputs
  else if startRequested then start p s payload inputs
  else s

def run (p : Program) (s : State) (incoming : Nat → Inputs) : Nat → State
  | 0 => s
  | n + 1 => advance p (run p s incoming n) (incoming (n + 1))

def shiftBits (output : Fin 3) (order : Order) : BitVec 6 :=
  (0#3) ++ BitVec.ofBool order.isMsbFirst ++ (BitVec.ofNat 2 output.val)

def encode : Instruction → BitVec 64
  | .ordinary operation => Execution.encode operation
  | .shift output order duration pins => Execution.pack
      {kind := 5, levels := pins.levels, enabled := pins.enabled,
       duration := BitVec.ofFin duration, entry := shiftBits output order}
  | .keep preserve pins capture duration => Execution.pack
      {kind := 6, levels := pins.levels, enabled := pins.enabled,
       duration := BitVec.ofFin duration, entry := Execution.captureBits capture,
       terminal := preserve.zeroExtend 6}

def imageWords (p : Program) : Execution.Words := p.memory.map encode

def source (p : Program) : Hardware.Storage.PairedResidentImage.Source :=
  ⟨imageWords p, p.idle, p.last⟩

end Pinwheel.Program.Resident
