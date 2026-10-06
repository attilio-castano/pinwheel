import Pinwheel.Hardware.HostResultBuffer
import Pinwheel.Hardware.UARTRx
import Pinwheel.Compile.UARTRxStream

/-! UART supervision on the existing observer's pre-step clock phase.
Receiver abort/reset and mailbox flush are distinct inputs: a core reset or
replacement may retain an unread outcome, while external mailbox reset flushes it.
The caller owns activation and command policy; this module infers no protocol. -/
namespace Pinwheel.UART.Rx.BufferedSupervisor
open Pinwheel.Hardware

structure Input where
  line : Bool := true
  start : Bool := false
  receiverReset : Bool := false
  flush : Bool := false
  take : Bool := false
  clearOverrun : Bool := false
  deriving DecidableEq, Repr

structure State where
  receiver : Rx.State := Rx.reset
  buffer : Buffer.State := {}
  wasActive : Bool := false
  deriving DecidableEq, Repr

structure Transition where
  state : State
  receipt : Buffer.Receipt
  deriving DecidableEq, Repr

/-- A stopped completion arrives once, on the edge that observes the old receiver. -/
def arrival (s : State) : Option Outcome := if s.wasActive then Rx.result s.receiver else none

def command (s : State) (input : Input) : Buffer.Command :=
  if input.flush then .reset else .cycle (arrival s) input.take input.clearOverrun

def step (cfg : Config) (s : State) (input : Input) : Transition :=
  let buffer := Buffer.step s.buffer (command s input)
  ⟨⟨Rx.step cfg s.receiver input.receiverReset input.start input.line, buffer.state,
    if input.flush then false else Rx.busy s.receiver || input.start⟩, buffer.receipt⟩

def run (cfg : Config) (s : State) (incoming : Nat → Input) : Nat → State
  | 0 => s
  | n + 1 => (step cfg (run cfg s incoming n) (incoming (n + 1))).state

/-- These are ordinary existing E64 compiler-state observations, not assumed UART values. -/
structure CoreCorresponds (cfg : Config) (receiver : Rx.State)
    (o : Values Loader.Machine.Output) : Prop where
  busy : o (.core .busy) = BitVec.ofBool (Rx.busy receiver)
  mode : o (.core (.state .mode)) = (Reactive.embed (Compile.UARTRx.lift cfg receiver)).mode
  samples : HostResultBuffer.sampleVector (HostResult.sampleValues o) = receiver.samples

/-- The pre-step completed packet decodes exactly to the receiver's byte/framing outcome.
Core correspondence excludes generic timeout/fault packets from this UART specialization. -/
theorem arrival_refines (cfg : Config) (receiver : Rx.State) (o : Values Loader.Machine.Output)
    (host : HostResult.State) (active : Bool) (hactive : host.wasActive = active)
    (core : CoreCorresponds cfg receiver o) :
    (HostResultBuffer.arrival o host).map HostResultBuffer.uartOutcome =
      if active then Rx.result receiver else none := by
  rcases receiver with ⟨phase, remaining, samples⟩
  cases phase
  all_goals simp [HostResultBuffer.arrival, HostResult.arriving, core.busy, core.mode, hactive,
    Compile.UARTRx.lift, Compile.UARTRx.liftControl, Reactive.embed, Reactive.stopMode,
    Rx.busy, Rx.result, HostResultBuffer.uartOutcome, core.samples]
  done

theorem command_refines (cfg : Config) (s : State) (input : Input)
    (pins : Chip.Pins) (o : Values Loader.Machine.Output) (host : HostResult.State)
    (active : host.wasActive = s.wasActive) (core : CoreCorresponds cfg s.receiver o)
    (flush : HostResult.resetting pins host = input.flush)
    (take : HostResult.consuming host = input.take)
    (clear : HostResult.clearing host = input.clearOverrun) :
    HostResultBuffer.uartCommand (HostResultBuffer.command pins o host) = command s input := by
  simp only [HostResultBuffer.command, flush, take, clear]
  split <;> simp [HostResultBuffer.uartCommand, command, arrival, *,
    arrival_refines cfg s.receiver o host s.wasActive active core]
  done

/-- The real observer, including its receipt, implements the pre-step UART supervisor buffer.
Controls refer to the observer's consumed synchronizer/edge-detector state. -/
theorem observer_step (cfg : Config) (s : State) (input : Input)
    (pins : Chip.Pins) (o : Values Loader.Machine.Output) (host : HostResult.State)
    (buffer : HostResultBuffer.uartProject host = s.buffer)
    (active : host.wasActive = s.wasActive) (core : CoreCorresponds cfg s.receiver o)
    (flush : HostResult.resetting pins host = input.flush)
    (take : HostResult.consuming host = input.take)
    (clear : HostResult.clearing host = input.clearOverrun) :
    (⟨HostResultBuffer.uartProject (HostResult.next pins o host),
      HostResultBuffer.uartReceipt (HostResultBuffer.receipt pins o host)⟩ : Buffer.Transition) =
      ⟨(step cfg s input).state.buffer, (step cfg s input).receipt⟩ := by
  rw [HostResultBuffer.uart_next_refines, buffer,
    command_refines cfg s input pins o host active core flush take clear]
  rfl
  done

theorem observer_active (cfg : Config) (s : State) (input : Input)
    (pins : Chip.Pins) (o : Values Loader.Machine.Output) (host : HostResult.State)
    (core : CoreCorresponds cfg s.receiver o)
    (flush : HostResult.resetting pins host = input.flush)
    (start : o (.control .start) = BitVec.ofBool input.start) :
    (HostResult.next pins o host).wasActive = (step cfg s input).state.wasActive := by
  simp [HostResult.next, step, flush, core.busy, start]
  cases Rx.busy s.receiver <;> cases input.start <;> rfl
  done

structure CompiledState where
  core : Compile.UARTRx.RxState
  buffer : Buffer.State := {}
  wasActive : Bool := false
  deriving DecidableEq, Repr

structure CompiledTransition where
  state : CompiledState
  receipt : Buffer.Receipt
  deriving DecidableEq, Repr

def lift (cfg : Config) (s : State) : CompiledState :=
  ⟨Compile.UARTRx.lift cfg s.receiver, s.buffer, s.wasActive⟩

/-- Existing canonical E64 fetch execution; buffer observation uses the OLD core. -/
def decodedStep (cfg : Config) (s : CompiledState) (input : Input) (spare : Bool) : CompiledTransition :=
  let store := Execution.directStore (UARTRx.words cfg) (Compile.UARTRx.program cfg).idle
    (Compile.UARTRx.program cfg).last
  let core := Engine.Reactive.Fetch.step store s.core input.receiverReset input.start
    (Compile.UARTLink.pins cfg.input input.line spare)
  let arrival := if s.wasActive then Compile.UARTRx.result s.core else none
  let buffer := Buffer.step s.buffer
    (if input.flush then .reset else .cycle arrival input.take input.clearOverrun)
  ⟨⟨core, buffer.state,
    if input.flush then false else Engine.Reactive.busy s.core || input.start⟩, buffer.receipt⟩

theorem decoded_step (cfg : Config) (s : State) (input : Input) (spare : Bool)
    (valid : WellFormed cfg s.receiver) :
    decodedStep cfg (lift cfg s) input spare =
      ⟨lift cfg (step cfg s input).state, (step cfg s input).receipt⟩ := by
  simp only [decodedStep, lift, UARTRx.direct_step cfg s.receiver _ _ _ valid,
    Compile.UARTLink.pins_selected, Compile.UARTRx.result_lift, Compile.UARTRx.busy_lift,
    step, command, arrival]
  done

theorem wellFormed_step (cfg : Config) (s : State) (input : Input)
    (valid : WellFormed cfg s.receiver) : WellFormed cfg (step cfg s input).state.receiver := by
  grind [step, Rx.step, Rx.wellFormed_advance, Rx.WellFormed, Rx.reset, Rx.initial]
  done

theorem wellFormed_run (cfg : Config) (s : State) (incoming : Nat → Input)
    (valid : WellFormed cfg s.receiver) (n : Nat) : WellFormed cfg (run cfg s incoming n).receiver :=
  Nat.recOn n valid (fun n ih => wellFormed_step cfg _ (incoming (n + 1)) ih)

def decodedRun (cfg : Config) (s : CompiledState) (incoming : Nat → Input)
    (spare : Nat → Bool) : Nat → CompiledState
  | 0 => s
  | n + 1 => (decodedStep cfg (decodedRun cfg s incoming spare n) (incoming (n + 1))
      (spare (n + 1))).state

theorem decoded_run (cfg : Config) (s : State) (incoming : Nat → Input)
    (spare : Nat → Bool) (valid : WellFormed cfg s.receiver) (n : Nat) :
    decodedRun cfg (lift cfg s) incoming spare n = lift cfg (run cfg s incoming n) := by
  induction n
  case zero => rfl
  case succ n ih =>
    simpa only [decodedRun, run, ih] using congrArg CompiledTransition.state
      (decoded_step cfg (run cfg s incoming n) (incoming (n + 1)) (spare (n + 1))
        (wellFormed_run cfg s incoming valid n))
  done

/-- A POST-step Stream receiver is the NEXT observer edge's PRE-step receiver.
The consumer/reset controls must follow that same delayed buffer edge. The next
receiver's own line/start/reset controls do not affect this old-state observation. -/
theorem delayed_stream_edge (cfg : Config) (old : Stream.State) (consumed : Stream.Input)
    (next : Input) (flush : next.flush = consumed.reset) (take : next.take = consumed.take)
    (clear : next.clearOverrun = consumed.clearOverrun) :
    let pre : State := ⟨(Stream.step cfg old consumed).state.receiver, old.buffer, true⟩
    (⟨(step cfg pre next).state.buffer, (step cfg pre next).receipt⟩ : Buffer.Transition) =
      ⟨(Stream.step cfg old consumed).state.buffer, (Stream.step cfg old consumed).receipt⟩ := by
  simp only [step, command, arrival, ↓reduceIte, flush, take, clear,
    Stream.step, Stream.command]
  done

/-- Core abort/disarm leaves unread mailbox ownership intact when no old completion
is arriving and no take/flush is consumed. This includes serial core-reset commands. -/
theorem receiver_reset_retains (cfg : Config) (s : State) (input : Input)
    (reset : input.receiverReset = true) (flush : input.flush = false)
    (take : input.take = false) (quiet : arrival s = none) :
    (step cfg s input).state.receiver = Rx.reset ∧
      (step cfg s input).state.buffer = ⟨s.buffer.pending, s.buffer.overrun && !input.clearOverrun⟩ ∧
      (step cfg s input).receipt = {} := by
  simp [step, command, reset, flush, take, quiet, Rx.step, Buffer.step]
  cases s.buffer.pending <;> exact ⟨rfl, rfl⟩
  done

theorem external_flush (cfg : Config) (s : State) (input : Input) (flush : input.flush = true) :
    (step cfg s input).state.buffer = {} ∧ (step cfg s input).state.wasActive = false ∧
      (step cfg s input).receipt = {flushed := s.buffer.pending} := by
  simp [step, command, flush, Buffer.step]
  done

/-- Phase-correct connection to the older POST-step stream contract. The actual
observer now sees that receiver state, and consumes the correspondingly delayed
buffer controls. No unshifted stream/observer equality is asserted. -/
theorem observer_stream_delayed (cfg : Config) (old : Stream.State) (consumed : Stream.Input)
    (pins : Chip.Pins) (o : Values Loader.Machine.Output) (host : HostResult.State)
    (buffer : HostResultBuffer.uartProject host = old.buffer)
    (active : host.wasActive = true)
    (core : CoreCorresponds cfg (Stream.step cfg old consumed).state.receiver o)
    (flush : HostResult.resetting pins host = consumed.reset)
    (take : HostResult.consuming host = consumed.take)
    (clear : HostResult.clearing host = consumed.clearOverrun) :
    (⟨HostResultBuffer.uartProject (HostResult.next pins o host),
      HostResultBuffer.uartReceipt (HostResultBuffer.receipt pins o host)⟩ : Buffer.Transition) =
      ⟨(Stream.step cfg old consumed).state.buffer, (Stream.step cfg old consumed).receipt⟩ := by
  have exactEdge := observer_step cfg
    ⟨(Stream.step cfg old consumed).state.receiver, old.buffer, true⟩
    {flush := consumed.reset, take := consumed.take, clearOverrun := consumed.clearOverrun}
    pins o host buffer active core flush take clear
  exact exactEdge.trans (delayed_stream_edge cfg old consumed _ rfl rfl rfl)
  done

/-- A quiet continuous receiver uses the current line but the previous edge's
consumer controls. The first edge performs no mailbox consumption. -/
def delayedInput (incoming : Nat → Stream.Input) (n : Nat) : Input :=
  {line := (incoming n).line, start := true,
   take := if n ≤ 1 then false else (incoming (n - 1)).take,
   clearOverrun := if n ≤ 1 then false else (incoming (n - 1)).clearOverrun}

/-- On uninterrupted continuous-start histories, receiver state agrees on the
same edge while mailbox state is one edge behind the POST-step stream model.
This theorem shifts consumer controls as well as arrivals; reset/flush boundaries
instead use the separate transition theorems above. -/
theorem uninterrupted_delay (cfg : Config) (buffer : Buffer.State) (incoming : Nat → Stream.Input)
    (quiet : ∀ n, (incoming n).reset = false) (n : Nat) :
    run cfg ⟨Rx.initial, buffer, false⟩ (delayedInput incoming) (n + 1) =
      ⟨(Stream.run cfg ⟨Rx.initial, buffer⟩ incoming (n + 1)).receiver,
        (Stream.run cfg ⟨Rx.initial, buffer⟩ incoming n).buffer, true⟩ := by
  induction n
  case zero =>
    simp [run, step, command, arrival, delayedInput, Stream.run, Stream.step, quiet,
      Rx.initial, Buffer.step]
    cases buffer with | mk pending overrun => cases pending <;> rfl
    done
  case succ n ih =>
    rw [run, ih]
    simp only [step, command, arrival, delayedInput, show ¬ n + 1 + 1 ≤ 1 by omega,
      ↓reduceIte, show n + 1 + 1 - 1 = n + 1 by omega, Bool.or_true,
      Stream.run, Stream.step, Stream.command, quiet]
    rfl
    done

theorem uninterrupted_receipt (cfg : Config) (buffer : Buffer.State) (incoming : Nat → Stream.Input)
    (quiet : ∀ n, (incoming n).reset = false) (n : Nat) :
    (step cfg (run cfg ⟨Rx.initial, buffer, false⟩ (delayedInput incoming) (n + 1))
      (delayedInput incoming (n + 2))).receipt =
        (Stream.step cfg (Stream.run cfg ⟨Rx.initial, buffer⟩ incoming n) (incoming (n + 1))).receipt := by
  rw [uninterrupted_delay cfg buffer incoming quiet n]
  simp [step, command, arrival, delayedInput, show ¬ n + 2 ≤ 1 by omega,
    show n + 2 - 1 = n + 1 by omega, Stream.run, Stream.step, Stream.command, quiet]
  done

end Pinwheel.UART.Rx.BufferedSupervisor
