import Pinwheel.Program.StreamingQueue

/-! The versioned streaming ISA. The original buffered ISA is unchanged. -/
namespace Pinwheel.Program.Streaming

/-- A programmable low/high serial cell; durations encode cycles minus one. -/
structure Cell where
  lowDuration : Fin 256 := 0
  highDuration : Fin 256 := 0
  lowPins : Engine.Reactive.Pins := {}
  highPins : Engine.Reactive.Pins := {}
  txOutput : Fin 3 := 0
  rxInput : Fin 2 := 0
  transmit : Bool := false
  receive : Bool := false
  lastLowLevels : BitVec 3 := 0
  lastHighLevels : BitVec 3 := 0
  txInvert : Bool := false
  txEnableMode : Bool := false
  lastLowEnabled : BitVec 3 := 0
  lastHighEnabled : BitVec 3 := 0
  deriving DecidableEq, Repr

inductive Instruction where
  | pulse (cell : Cell)
  | stream (cell : Cell)
  | halt
  | fault
  deriving DecidableEq, Repr

/-- Exactly64 physical slots; the installed prefix has between1 and64 words. -/
structure Program where
  memory : Vector Instruction 64
  lengthMinusOne : Fin 64
  idle : Engine.Reactive.Pins := {}
  deriving DecidableEq, Repr

def Program.length (p : Program) : Nat := p.lengthMinusOne.val + 1

def Program.fetch (p : Program) (pc : Nat) : Option Instruction :=
  if h : pc < p.length then
    some (p.memory[pc]'(by have := p.lengthMinusOne.isLt; unfold length at h; omega))
  else none

def Instruction.isStream : Instruction → Bool
  | .stream _ => true
  | _ => false

/-- The initial compiler accepts one dynamic stream cell, with arbitrary pulse prefix/suffix. -/
def Program.WellFormed (p : Program) : Prop :=
  (p.memory.toList.take p.length).countP Instruction.isStream ≤ 1

end Pinwheel.Program.Streaming
