import Pinwheel.UART.RxSpec

/-! Independent receive controller: protocol phases and a whole-symbol countdown.
It has no instruction addresses, instruction fetch, or 256-cycle chunk counter. -/
namespace Pinwheel.UART.Rx

inductive Phase where
  | ready | idle | falling | timed (symbol : Fin 10) | finished
  deriving DecidableEq, Repr

structure State where
  phase : Phase := .ready
  remaining : Fin 6656 := 0
  samples : Vector Bool 16 := Vector.replicate 16 false
  deriving DecidableEq, Repr

def reset : State := {}
def initial : State := {phase := .idle}

def busy (s : State) : Bool := match s.phase with
  | .ready | .finished => false
  | _ => true

def result (s : State) : Option Outcome :=
  if s.phase = .finished then some (outcome s.samples) else none

def observe (s : State) (slot : Fin 16) (input : Bool) : State :=
  {s with samples := s.samples.set slot input}

def enterSymbol (cfg : Config) (s : State) (symbol : Fin 10) : State :=
  {s with
    phase := .timed symbol
    remaining := ⟨duration cfg symbol - 1, by
      have := cfg.maximum
      simp only [duration, Config.half]
      split <;> omega⟩}

def finishSymbol (cfg : Config) (s : State) (symbol : Fin 10) (input : Bool) : State :=
  let captured := observe s (sampleSlot symbol) input
  if symbol.val = 0 ∧ input then {captured with phase := .idle, remaining := 0}
  else if h : symbol.val + 1 < 10 then enterSymbol cfg captured ⟨symbol.val + 1, h⟩
  else {captured with phase := .finished, remaining := 0}

/-- Consume the observation at the destination edge. Arming itself consumes no input. -/
def advance (cfg : Config) (s : State) (input : Bool) : State :=
  match s.phase with
  | .ready | .finished => s
  | .idle => {observe s 8 input with phase := if input then .falling else .idle}
  | .falling => if input then observe s 8 input else enterSymbol cfg (observe s 8 input) 0
  | .timed symbol =>
    if h : 0 < s.remaining.val then
      {s with remaining := ⟨s.remaining.val - 1, by omega⟩}
    else finishSymbol cfg s symbol input

def step (cfg : Config) (s : State) (resetRequested startRequested input : Bool) : State :=
  if resetRequested then reset
  else if busy s then advance cfg s input
  else if startRequested then initial else s

def run (cfg : Config) (s : State) (incoming : Nat → Bool) : Nat → State
  | 0 => s
  | n + 1 => advance cfg (run cfg s incoming n) (incoming (n + 1))

def WellFormed (cfg : Config) (s : State) : Prop :=
  match s.phase with
  | .timed symbol => s.remaining.val < duration cfg symbol
  | _ => s.remaining.val = 0

end Pinwheel.UART.Rx
