import Pinwheel.Program.StreamingExecution

/-! Separate sampled-ready instruction set. Legacy streaming words and semantics
remain unchanged. All operational data has a fixed width or fixed queue depth. -/
namespace Pinwheel.Program.StreamingReady

abbrev Cell := Streaming.Cell
abbrev Chunk := Streaming.Chunk
abbrev Queue (a : Nat) := Streaming.Queue a
abbrev Input := Streaming.Input
abbrev Pins := Engine.Reactive.Pins

inductive WaitLimit where
  | unbounded
  | misses (minusOne : Fin 255)
  deriving DecidableEq, Repr

def WaitLimit.budget : WaitLimit → BitVec 8
  | .unbounded => 0
  | .misses n => BitVec.ofNat 8 (n.val + 1)

def WaitLimit.initialCountdown : WaitLimit → BitVec 8
  | .unbounded => 0
  | .misses n => BitVec.ofNat 8 n.val

def WaitLimit.expires (limit : WaitLimit) (countdown : BitVec 8) : Bool :=
  match limit with
  | .unbounded => false
  | .misses _ => countdown == 0

def WaitLimit.poll (limit : WaitLimit) (countdown : BitVec 8) : BitVec 8 :=
  match limit with
  | .unbounded => countdown
  | .misses _ => countdown - 1

structure Guard where
  mask : BitVec 2 := 0
  expected : BitVec 2 := 0
  limit : WaitLimit := .unbounded
  deriving DecidableEq, Repr

def Guard.matches (guard : Guard) (sample : BitVec 2) : Bool :=
  (sample &&& guard.mask) == guard.expected

inductive Instruction where
  | pulse (cell : Cell)
  | stream (cell : Cell) (highGuard : Option Guard)
  | driveWait (pins : Pins) (guard : Guard)
  | halt
  | fault
  deriving DecidableEq, Repr

def Instruction.cell : Instruction → Cell
  | .pulse c | .stream c _ => c
  | .driveWait pins _ => {lowPins := pins}
  | _ => {}

def Instruction.isStream : Instruction → Bool
  | .stream _ _ => true
  | _ => false

def Instruction.hasHighGuard : Instruction → Bool
  | .stream _ (some _) => true
  | _ => false

/-- Unguarded cached instructions have a total immediate-ready guard. -/
def Instruction.guard : Instruction → Guard
  | .stream _ (some guard) | .driveWait _ guard => guard
  | _ => {}

inductive Phase where
  | free | fetch | boundary | low | high | completed | fault | waiting
  deriving DecidableEq, Repr

def Phase.code : Phase → BitVec 3
  | .free => 0 | .fetch => 1 | .boundary => 2 | .low => 3
  | .high => 4 | .completed => 5 | .fault => 6 | .waiting => 7

def Phase.busy : Phase → Bool
  | .fetch | .boundary | .low | .high | .waiting => true
  | _ => false

def Phase.retained : Phase → Bool
  | .completed | .fault => true
  | _ => false

structure Program where
  memory : Vector Instruction 64
  lengthMinusOne : Fin 64
  idle : Pins := {}
  deriving DecidableEq, Repr

def Program.length (p : Program) : Nat := p.lengthMinusOne.val + 1

def Program.fetch (p : Program) (pc : Nat) : Option Instruction :=
  if h : pc < p.length then
    some (p.memory[pc]'(by have := p.lengthMinusOne.isLt; unfold Program.length at h; omega))
  else none

structure State (a : Nat) where
  phase : Phase := .free
  pc : BitVec 7 := 0
  current : Instruction := .halt
  total : BitVec 16 := 0
  remaining : BitVec 16 := 0
  countdown : BitVec 8 := 0
  cellBit : Bool := false
  tx : Queue a := Streaming.Queue.empty a
  rx : Queue a := Streaming.Queue.empty a
  txShift : BitVec 32 := 0
  txValid : BitVec 6 := 0
  rxPartial : BitVec 32 := 0
  rxUsed : BitVec 6 := 0
  samplerFirst : BitVec 2 := 0
  samplerSecond : BitVec 2 := 0
  pins : Pins := {}
  generation : BitVec 16 := 0
  transfer : BitVec 16 := 0
  txAccepted : BitVec 16 := 0
  txConsumed : BitVec 16 := 0
  rxProduced : BitVec 16 := 0
  rxPopped : BitVec 16 := 0
  deriving DecidableEq, Repr

end Pinwheel.Program.StreamingReady
