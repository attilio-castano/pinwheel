import Pinwheel.UART.Rx
import Pinwheel.UART.RxBuffer

namespace Pinwheel.UART.Rx.Stream

structure Input where
  line : Bool := true
  take : Bool := false
  clearOverrun : Bool := false
  reset : Bool := false
  deriving DecidableEq, Repr

structure State where
  receiver : Rx.State := Rx.initial
  buffer : Buffer.State := {}
  deriving DecidableEq, Repr

structure Transition where
  state : State
  receipt : Buffer.Receipt
  deriving DecidableEq, Repr

def command (receiver : Rx.State) (input : Input) : Buffer.Command :=
  if input.reset then .reset else .cycle (Rx.result receiver) input.take input.clearOverrun

/-- Start is continuously requested. The existing endpoint spends one edge rearming. -/
def step (cfg : Config) (s : State) (input : Input) : Transition :=
  let receiver := Rx.step cfg s.receiver input.reset true input.line
  let edge := Buffer.step s.buffer (command receiver input)
  ⟨⟨receiver, edge.state⟩, edge.receipt⟩

def run (cfg : Config) (s : State) (incoming : Nat → Input) : Nat → State
  | 0 => s
  | n + 1 => (step cfg (run cfg s incoming n) (incoming (n + 1))).state

/-- Completion is a one-edge event; the next non-reset edge rearms the receiver. -/
def arrival (s : State) : Option Outcome := Rx.result s.receiver

def completion (cfg : Config) (detected : Nat) : Nat :=
  detected + (cfg.half + 9 * cfg.bitCycles)

/-- One valid frame measured from an armed receiver edge. Consumer controls are free. -/
structure Frame (cfg : Config) (incoming : Nat → Input) (detected : Nat) (byte : BitVec 8) : Prop where
  later : 2 ≤ detected
  high : ∀ k, 1 ≤ k → k < detected → (incoming k).line = true
  low : (incoming detected).line = false
  startLow : (incoming (detected + cfg.half)).line = false
  samples : SamplesFrame cfg detected (fun k => (incoming k).line) byte
  quiet : ∀ k, 1 ≤ k → k ≤ completion cfg detected + 1 → (incoming k).reset = false

/-- A logical command history for applying the buffer's trace theorems. -/
def commands (cfg : Config) (s : State) (incoming : Nat → Input) : Nat → List Buffer.Command
  | 0 => []
  | n + 1 => commands cfg s incoming n ++
    [command (run cfg s incoming (n + 1)).receiver (incoming (n + 1))]

end Pinwheel.UART.Rx.Stream
