import Pinwheel.Compile.UARTLink
import Pinwheel.UART.RxWire

/-! A Lean supervisor for one existing reactive RX program. Buffer implementation in RTL
and scheduling concurrent TX/RX on shared resources remain outside this correspondence. -/
namespace Pinwheel.Compile.UARTRxStream
open Pinwheel.UART.Rx

structure State where
  core : UARTRx.RxState
  buffer : Buffer.State := {}
  deriving DecidableEq, Repr

structure Transition where
  state : State
  receipt : Buffer.Receipt
  deriving DecidableEq, Repr

/-- The program is supplied once by the caller; the proof specializes it to `UARTRx.program`. -/
def step (program : Engine.Reactive.Program 255 15) (pin : Fin 2) (s : State)
    (input : Stream.Input) (spare : Bool) : Transition :=
  let core := Engine.Reactive.step program s.core input.reset true (UARTLink.pins pin input.line spare)
  let command := if input.reset then Buffer.Command.reset
    else .cycle (UARTRx.result core) input.take input.clearOverrun
  let edge := Buffer.step s.buffer command
  ⟨⟨core, edge.state⟩, edge.receipt⟩

def lift (cfg : Config) (s : Stream.State) : State := ⟨UARTRx.lift cfg s.receiver, s.buffer⟩

def run (cfg : Config) (s : State) (incoming : Nat → Stream.Input) (spare : Nat → Bool) : Nat → State
  | 0 => s
  | n + 1 => (step (UARTRx.program cfg) cfg.input (run cfg s incoming spare n) (incoming (n + 1)) (spare (n + 1))).state

theorem start_simulation (cfg : Config) (buffer : Buffer.State) (pins : Engine.Reactive.Inputs) :
    (⟨Engine.Reactive.start (UARTRx.program cfg) pins, buffer⟩ : State) =
      lift cfg ⟨initial, buffer⟩ := by
  rw [UARTRx.start_simulation]
  rfl

/-- Both machine state and ownership observations agree on each edge. -/
theorem step_simulation (cfg : Config) (s : Stream.State) (input : Stream.Input) (spare : Bool)
    (valid : WellFormed cfg s.receiver) :
    step (UARTRx.program cfg) cfg.input (lift cfg s) input spare =
      ⟨lift cfg (Stream.step cfg s input).state, (Stream.step cfg s input).receipt⟩ := by
  simp only [step, lift, Stream.step, Stream.command,
    UARTRx.step_simulation cfg s.receiver input.reset true _ valid,
    UARTLink.pins_selected, UARTRx.result_lift]

theorem run_simulation (cfg : Config) (s : Stream.State) (incoming : Nat → Stream.Input)
    (spare : Nat → Bool) (valid : WellFormed cfg s.receiver) (n : Nat) :
    run cfg (lift cfg s) incoming spare n = lift cfg (Stream.run cfg s incoming n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simpa only [run, Stream.run, ih] using congrArg Transition.state
      (step_simulation cfg (Stream.run cfg s incoming n) (incoming (n + 1)) (spare (n + 1))
        (Stream.wellFormed_run cfg s incoming valid n))

theorem ideal_series (cfg : Config) (fits : cfg.bitCycles ≤ 256) (bytes : List (BitVec 8))
    (start : Nat) (later : 2 ≤ start) (buffer : Buffer.State) (incoming : Nat → Stream.Input)
    (spare : Nat → Bool)
    (line : ∀ n, (incoming n).line = Stream.wire (Stream.idealTx cfg fits) start bytes n)
    (quiet : ∀ n, (incoming n).reset = false) (n : Nat)
    (within : n ≤ Stream.horizon cfg (Stream.idealFrames cfg start bytes)) :
    UARTRx.result (run cfg (lift cfg ⟨initial, buffer⟩) incoming spare n).core =
      Stream.expected cfg (Stream.idealFrames cfg start bytes) n := by
  rw [run_simulation cfg ⟨initial, buffer⟩ incoming spare rfl]
  simpa only [lift, UARTRx.result_lift, Stream.arrival] using
    Stream.ideal_series cfg fits bytes start later buffer incoming line quiet n within

theorem buffer_correct (cfg : Config) (s : Stream.State) (incoming : Nat → Stream.Input)
    (spare : Nat → Bool) (valid : WellFormed cfg s.receiver) (n : Nat) :
    (run cfg (lift cfg s) incoming spare n).buffer = (Stream.run cfg s incoming n).buffer :=
  congrArg State.buffer (run_simulation cfg s incoming spare valid n)

theorem outputs_released (cfg : Config) (s : Stream.State) (incoming : Nat → Stream.Input)
    (spare : Nat → Bool) (valid : WellFormed cfg s.receiver) (n : Nat) :
    (run cfg (lift cfg s) incoming spare n).core.pins = {} := by
  rw [run_simulation cfg s incoming spare valid]
  rfl

end Pinwheel.Compile.UARTRxStream
