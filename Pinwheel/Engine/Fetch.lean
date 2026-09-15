import Pinwheel.Engine.Reactive

/-! Functional instruction-store adapter. The reactive bank remains the comparison baseline.
The adapter fetches only the current instruction; it never builds an expanded bank. -/
namespace Pinwheel.Engine.Reactive.Fetch

structure Store (lastAddress : Nat := 127) (lastSample : Nat := 7) where
  fetch : Fin (lastAddress + 1) → Option (Instruction lastAddress lastSample)
  idle : Pins
  last : Fin (lastAddress + 1)

def Store.ofProgram (p : Program lastAddress lastSample) : Store lastAddress lastSample := ⟨fun pc => some (p.fetch pc), p.idle, p.last⟩

def stop (p : Store lastAddress lastSample) (reason : Stop) (slots : Vector Bool (lastSample + 1)) : State lastAddress lastSample :=
  ⟨.stopped reason, p.idle, slots⟩

def reset (p : Store lastAddress lastSample) : State lastAddress lastSample := stop p .ready (Vector.replicate (lastSample + 1) false)

/-- Wait entry only applies commands. Its first observation is on the following edge. -/
def enter (p : Store lastAddress lastSample) (pc : Fin (lastAddress + 1)) (slots : Vector Bool (lastSample + 1)) (inputs : Inputs) : State lastAddress lastSample :=
  match p.fetch pc with
  | none => stop p .fault slots
  | some .halt => stop p .completed slots
  | some (.action a) => ⟨.active pc a.durationMinusOne, a.pins, capture slots a.capture inputs⟩
  | some (.wait w) => ⟨.waiting pc w.budgetMinusOne, w.pins, slots⟩
  | some (.checked a) => ⟨.checked pc a.action.durationMinusOne, a.action.pins,
      capture slots a.action.capture inputs⟩
  | some (.qualify q) => ⟨.qualifying pc q.durationMinusOne q.budgetMinusOne, q.pins, slots⟩

def start (p : Store lastAddress lastSample) (inputs : Inputs) : State lastAddress lastSample := enter p 0 (Vector.replicate (lastSample + 1) false) inputs

def next (p : Store lastAddress lastSample) (pc : Fin (lastAddress + 1)) (slots : Vector Bool (lastSample + 1)) (inputs : Inputs) : State lastAddress lastSample :=
  if h : pc.val < p.last.val then enter p ⟨pc.val + 1, by omega⟩ slots inputs
  else stop p .fault slots

def jump (p : Store lastAddress lastSample) (target : Fin (lastAddress + 1)) (slots : Vector Bool (lastSample + 1)) (inputs : Inputs) : State lastAddress lastSample :=
  if target.val ≤ p.last.val then enter p target slots inputs else stop p .fault slots

def dispatch (p : Store lastAddress lastSample) (pc : Fin (lastAddress + 1)) (finish : Finish lastAddress lastSample) (slots : Vector Bool (lastSample + 1)) (inputs : Inputs) : State lastAddress lastSample :=
  match finish with
  | .sequential => next p pc slots inputs
  | .jump target => jump p target slots inputs
  | .branch sample yes no => jump p (if slots[sample.val] then yes else no) slots inputs

def advance (p : Store lastAddress lastSample) (s : State lastAddress lastSample) (inputs : Inputs) : State lastAddress lastSample :=
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

def step (p : Store lastAddress lastSample) (s : State lastAddress lastSample) (resetRequested startRequested : Bool) (inputs : Inputs) : State lastAddress lastSample :=
  if resetRequested then reset p
  else if busy s then advance p s inputs
  else if startRequested then start p inputs
  else s

def run (p : Store lastAddress lastSample) (s : State lastAddress lastSample) (incoming : Nat → Inputs) : Nat → State lastAddress lastSample
  | 0 => s
  | n + 1 => advance p (run p s incoming n) (incoming (n + 1))

structure Machine (lastAddress : Nat := 127) (lastSample : Nat := 7) where
  program : Store lastAddress lastSample
  state : State lastAddress lastSample

def load (m : Machine lastAddress lastSample) (p : Store lastAddress lastSample) : Machine lastAddress lastSample × Bool :=
  if busy m.state then (m, false) else (⟨p, reset p⟩, true)

end Pinwheel.Engine.Reactive.Fetch
