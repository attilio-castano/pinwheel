import Pinwheel.Engine.Reactive

/-! Functional instruction-store adapter. The reactive bank remains the comparison baseline.
The adapter fetches only the current instruction; it never builds an expanded bank. -/
namespace Pinwheel.Engine.Reactive.Fetch

structure Store where
  fetch : Fin 128 → Option Instruction
  idle : Pins
  last : Fin 128

def Store.ofProgram (p : Program) : Store := ⟨fun pc => some (p.fetch pc), p.idle, p.last⟩

def stop (p : Store) (reason : Stop) (slots : Samples) : State :=
  ⟨.stopped reason, p.idle, slots⟩

def reset (p : Store) : State := stop p .ready (Vector.replicate 8 false)

/-- Wait entry only applies commands. Its first observation is on the following edge. -/
def enter (p : Store) (pc : Fin 128) (slots : Samples) (inputs : Inputs) : State :=
  match p.fetch pc with
  | none => stop p .fault slots
  | some .halt => stop p .completed slots
  | some (.action a) => ⟨.active pc a.durationMinusOne, a.pins, capture slots a.capture inputs⟩
  | some (.wait w) => ⟨.waiting pc w.budgetMinusOne, w.pins, slots⟩
  | some (.checked a) => ⟨.checked pc a.action.durationMinusOne, a.action.pins,
      capture slots a.action.capture inputs⟩
  | some (.qualify q) => ⟨.qualifying pc q.durationMinusOne q.budgetMinusOne, q.pins, slots⟩

def start (p : Store) (inputs : Inputs) : State := enter p 0 (Vector.replicate 8 false) inputs

def next (p : Store) (pc : Fin 128) (slots : Samples) (inputs : Inputs) : State :=
  if h : pc.val < p.last.val then enter p ⟨pc.val + 1, by omega⟩ slots inputs
  else stop p .fault slots

def jump (p : Store) (target : Fin 128) (slots : Samples) (inputs : Inputs) : State :=
  if target.val ≤ p.last.val then enter p target slots inputs else stop p .fault slots

def dispatch (p : Store) (pc : Fin 128) (finish : Finish) (slots : Samples) (inputs : Inputs) : State :=
  match finish with
  | .sequential => next p pc slots inputs
  | .jump target => jump p target slots inputs
  | .branch sample yes no => jump p (if slots[sample.val] then yes else no) slots inputs

def advance (p : Store) (s : State) (inputs : Inputs) : State :=
  match s.control with
  | .stopped _ => s
  | .active pc remaining =>
    if h : 0 < remaining.val then
      {s with control := .active pc ⟨remaining.val - 1, by omega⟩}
    else next p pc s.samples inputs
  | .waiting pc remaining =>
    match p.fetch pc with
    | some (.wait w) =>
      if w.condition.ready inputs then next p pc s.samples inputs
      else if h : 0 < remaining.val then
        {s with control := .waiting pc ⟨remaining.val - 1, by omega⟩}
      else stop p .timeout s.samples
    | _ => stop p .fault s.samples
  | .checked pc remaining =>
    match p.fetch pc with
    | some (.checked a) =>
      if !a.guard.ready inputs then stop p .fault s.samples
      else if h : 0 < remaining.val then
        {s with control := .checked pc ⟨remaining.val - 1, by omega⟩}
      else dispatch p pc a.finish (capture s.samples a.terminalCapture inputs) inputs
    | _ => stop p .fault s.samples
  | .qualifying pc remaining waitLeft =>
    match p.fetch pc with
    | some (.qualify q) =>
      if q.condition.ready inputs then
        if h : 0 < remaining.val then
          {s with control := .qualifying pc ⟨remaining.val - 1, by omega⟩ q.budgetMinusOne}
        else next p pc s.samples inputs
      else if h : 0 < waitLeft.val then
        {s with control := .qualifying pc q.durationMinusOne ⟨waitLeft.val - 1, by omega⟩}
      else stop p .timeout s.samples
    | _ => stop p .fault s.samples

def step (p : Store) (s : State) (resetRequested startRequested : Bool) (inputs : Inputs) : State :=
  if resetRequested then reset p
  else if busy s then advance p s inputs
  else if startRequested then start p inputs
  else s

def run (p : Store) (s : State) (incoming : Nat → Inputs) : Nat → State
  | 0 => s
  | n + 1 => advance p (run p s incoming n) (incoming (n + 1))

structure Machine where
  program : Store
  state : State

def load (m : Machine) (p : Store) : Machine × Bool :=
  if busy m.state then (m, false) else (⟨p, reset p⟩, true)

end Pinwheel.Engine.Reactive.Fetch
