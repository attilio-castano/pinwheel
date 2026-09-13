import Pinwheel.Engine.ISA

/-! One transition per system-clock edge; action entry samples then drives atomically. -/
namespace Pinwheel.Engine

inductive Stop where
  | ready
  | completed
  | fault
  deriving DecidableEq, Repr

inductive Control where
  | stopped (reason : Stop)
  | active (pc : Fin 32) (remaining : Fin 256)
  deriving DecidableEq, Repr

structure State where
  control : Control
  levels : Levels
  samples : Samples
  deriving DecidableEq, Repr

def busy (s : State) : Bool := match s.control with
  | .active .. => true
  | .stopped _ => false

def result (s : State) : Option Samples := match s.control with
  | .stopped .completed => some s.samples
  | _ => none

def reset (p : Program) : State := ⟨.stopped .ready, p.idle, Vector.replicate 8 false⟩

def enter (p : Program) (pc : Fin 32) (slots : Samples) (input : Bool) : State :=
  match p.fetch pc with
  | .halt => ⟨.stopped .completed, p.idle, slots⟩
  | .action a => ⟨.active pc a.durationMinusOne, a.levels, capture slots a.capture input⟩

/-- Entry to the first action is cycle zero. Only this edge's input may be captured. -/
def start (p : Program) (input : Bool) : State := enter p 0 (Vector.replicate 8 false) input

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

/-- Reset has priority. Start requests on busy edges, including completion, are ignored. -/
def step (p : Program) (s : State) (resetRequested startRequested input : Bool) : State :=
  if resetRequested then reset p
  else if busy s then advance p s input
  else if startRequested then start p input
  else s

def run (p : Program) (s : State) (incoming : Nat → Bool) : Nat → State
  | 0 => s
  | n + 1 => advance p (run p s incoming n) (incoming (n + 1))

structure Machine where
  program : Program
  state : State
  deriving DecidableEq, Repr

/-- Atomic host operation. Busy loading is rejected with the entire machine unchanged.
Successful loading clears status/data and immediately applies the new idle profile. -/
def load (m : Machine) (p : Program) : Machine × Bool :=
  if busy m.state then (m, false) else (⟨p, reset p⟩, true)

end Pinwheel.Engine
