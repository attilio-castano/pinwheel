import Std

/-! Typed instructions for the first bounded timed-action engine. -/
namespace Pinwheel.Engine

abbrev Levels := BitVec 3
abbrev Samples := Vector Bool 8

/-- Slot zero is the most-significant bit when interpreting the eight receive slots as a byte. -/
def samplesByte (slots : Samples) : BitVec 8 :=
  BitVec.ofBoolListBE [slots[0], slots[1], slots[2], slots[3], slots[4], slots[5], slots[6], slots[7]]

/-- Capture reads the single logical input into a named receive slot. -/
structure Action where
  levels : Levels
  durationMinusOne : Fin 256
  capture : Option (Fin 8) := none
  deriving DecidableEq, Repr

def Action.duration (a : Action) : Nat := a.durationMinusOne.val + 1

inductive Instruction where
  | action (a : Action)
  | halt
  deriving DecidableEq, Repr

/-- Program/configuration is distinct from execution state. No binary encoding yet. -/
structure Program where
  memory : Vector Instruction 32
  idle : Levels
  deriving DecidableEq, Repr

def Program.fetch (p : Program) (pc : Fin 32) : Instruction := p.memory[pc.val]

def capture (slots : Samples) (destination : Option (Fin 8)) (input : Bool) : Samples :=
  Vector.ofFn fun slot => if destination = some slot then input else slots[slot.val]

end Pinwheel.Engine
