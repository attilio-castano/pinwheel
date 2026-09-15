import Pinwheel.Hardware.Encoding

namespace Pinwheel.Hardware.Raw
open Pinwheel.Engine

structure Program where
  memory : Vector (BitVec 16) 32
  idle : Levels
  deriving DecidableEq, Repr

def encodeProgram (p : Engine.Program) : Program := ⟨p.memory.map Encoding.encode, p.idle⟩

def reset (p : Program) : State := ⟨.stopped .ready, p.idle, Vector.replicate 8 false⟩

/-- Decode at entry; a malformed word faults without capturing input. -/
def enter (p : Program) (pc : Fin 32) (slots : Samples) (input : Bool) : State :=
  match Encoding.decode p.memory[pc.val] with
  | none => ⟨.stopped .fault, p.idle, slots⟩
  | some .halt => ⟨.stopped .completed, p.idle, slots⟩
  | some (.action a) => ⟨.active pc a.durationMinusOne, a.levels, capture slots a.capture input⟩

def next (p : Program) (pc : Fin 32) (slots : Samples) (input : Bool) : State :=
  if h : pc.val + 1 < 32 then enter p ⟨pc.val + 1, h⟩ slots input
  else ⟨.stopped .fault, p.idle, slots⟩

def advance (p : Program) (s : State) (input : Bool) : State :=
  match s.control with
  | .stopped _ => s
  | .active pc remaining =>
    if h : 0 < remaining.val then
      { s with control := .active pc ⟨remaining.val - 1, by omega⟩ }
    else next p pc s.samples input

def step (p : Program) (s : State) (rst start input : Bool) : State :=
  if rst then reset p
  else if busy s then advance p s input
  else if start then enter p 0 (Vector.replicate 8 false) input else s

def run (p : Program) (s : State) (incoming : Nat → Bool) : Nat → State
  | 0 => s
  | n + 1 => advance p (run p s incoming n) (incoming (n + 1))

theorem enter_encoded (p : Engine.Program) (pc : Fin 32) (slots : Samples) (input : Bool) :
    enter (encodeProgram p) pc slots input = Engine.enter p pc slots input := by
  simp [enter, encodeProgram, Encoding.decode_encode, Engine.enter, Engine.Program.fetch]
  cases p.memory[pc.val] <;> rfl

theorem next_encoded (p : Engine.Program) (pc : Fin 32) (slots : Samples) (input : Bool) :
    next (encodeProgram p) pc slots input = Engine.next p pc slots input := by
  simp only [next, Engine.next, enter_encoded]
  rfl

theorem advance_encoded (p : Engine.Program) (s : State) (input : Bool) :
    advance (encodeProgram p) s input = Engine.advance p s input := by
  cases h : s.control <;> simp [advance, Engine.advance, h, next_encoded]

theorem step_encoded (p : Engine.Program) (s : State) (rst start input : Bool) :
    step (encodeProgram p) s rst start input = Engine.step p s rst start input := by
  simp only [step, Engine.step, Engine.start, advance_encoded, enter_encoded]
  rfl

theorem run_encoded (p : Engine.Program) (s : State) (incoming : Nat → Bool) (n : Nat) :
    run (encodeProgram p) s incoming n = Engine.run p s incoming n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [run, Engine.run, ih, advance_encoded]

theorem malformed_fault (p : Program) (pc : Fin 32) (slots : Samples) (input : Bool)
    (h : Encoding.decode p.memory[pc.val] = none) :
    enter p pc slots input = ⟨.stopped .fault, p.idle, slots⟩ := by
  simp [enter, h]

end Pinwheel.Hardware.Raw
