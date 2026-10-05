import Pinwheel.UART.BufferedSupervisor
import Pinwheel.UART.StreamLinkProofs
import Pinwheel.Hardware.Storage.PairedHost

/-! The observer's first consumer event is retained when aligning its PRE-step
mailbox with the existing POST-step stream. Activation premises in this module
are local interfaces; a package session must derive them from its control policy. -/
namespace Pinwheel.UART.Rx.BufferedSupervisor
open Pinwheel.Hardware

/-- A reset-free receiver cannot return to READY; an admitted START also leaves
READY. This does not require timing-counter well-formedness. -/
theorem step_not_ready (cfg : Config) (s : Rx.State) (start line : Bool)
    (live : s.phase ≠ .ready ∨ start = true) :
    (Rx.step cfg s false start line).phase ≠ .ready := by
  rcases s with ⟨phase, remaining, samples⟩
  cases phase
  all_goals simp_all [Rx.step, Rx.busy, Rx.advance, Rx.finishSymbol, Rx.enterSymbol, Rx.observe, Rx.initial]
  all_goals repeat (split <;> simp_all)
  done

theorem stopped_finished (s : Rx.State) (stopped : Rx.busy s = false)
    (live : s.phase ≠ .ready) : s.phase = .finished := by
  rcases s with ⟨phase, remaining, samples⟩
  cases phase <;> simp_all [Rx.busy]
  done

theorem mode_not_failure (cfg : Config) (s : Rx.State) :
    (Reactive.embed (Compile.UARTRx.lift cfg s)).mode ≠ 6 ∧
      (Reactive.embed (Compile.UARTRx.lift cfg s)).mode ≠ 7 := by
  rcases s with ⟨phase, remaining, samples⟩
  cases phase
  all_goals simp [Compile.UARTRx.lift, Compile.UARTRx.liftControl, Reactive.embed, Reactive.stopMode]
  all_goals by_cases chunk : remaining.val < 256 <;> simp [chunk]
  done

theorem mode_finished (cfg : Config) (s : Rx.State) :
    (Reactive.embed (Compile.UARTRx.lift cfg s)).mode = 5 ↔ s.phase = .finished := by
  rcases s with ⟨phase, remaining, samples⟩
  cases phase
  all_goals simp [Compile.UARTRx.lift, Compile.UARTRx.liftControl, Reactive.embed, Reactive.stopMode]
  all_goals by_cases chunk : remaining.val < 256 <;> simp [chunk]
  done

private def packedSamples (samples : Vector Bool 16) : BitVec 16 :=
  (((((((((((((((BitVec.ofBool samples[15] ++ BitVec.ofBool samples[14]) ++ BitVec.ofBool samples[13]) ++ BitVec.ofBool samples[12]) ++ BitVec.ofBool samples[11]) ++ BitVec.ofBool samples[10]) ++ BitVec.ofBool samples[9]) ++ BitVec.ofBool samples[8]) ++ BitVec.ofBool samples[7]) ++ BitVec.ofBool samples[6]) ++ BitVec.ofBool samples[5]) ++ BitVec.ofBool samples[4]) ++ BitVec.ofBool samples[3]) ++ BitVec.ofBool samples[2]) ++ BitVec.ofBool samples[1]) ++ BitVec.ofBool samples[0])

private theorem packed_execution_samples (o : Values Loader.Machine.Output) (m : Reactive.Model) :
    HostResult.sampleValues (Storage.PairedHost.withExecution o m) = packedSamples m.samples := by
  rcases m with ⟨control, pins, samples⟩
  cases control <;> rfl
  done

/-- Packing the compiled execution samples and reading them back retains all
sixteen observations, independently of the loader sideband. -/
theorem execution_samples (o : Values Loader.Machine.Output) (m : Reactive.Model) :
    HostResultBuffer.sampleVector (HostResult.sampleValues (Storage.PairedHost.withExecution o m)) =
      m.samples := by
  apply Vector.ext
  intro i hi
  have range : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨
      i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 := by omega
  rcases range with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp only [HostResultBuffer.sampleVector, Vector.getElem_ofFn, packed_execution_samples,
    packedSamples, BitVec.getLsbD_append, BitVec.getLsbD_ofBool]
  all_goals rfl
  done

/-- Exact independent compiled observations supply the observer premise. -/
theorem execution_coreCorresponds (cfg : Config) (receiver : Rx.State)
    (o : Values Loader.Machine.Output) :
    CoreCorresponds cfg receiver
      (Storage.PairedHost.withExecution o (Compile.UARTRx.lift cfg receiver)) := by
  refine ⟨?_, rfl, ?_⟩
  case refine_1 => simp only [Storage.PairedHost.withExecution, Compile.UARTRx.busy_lift]
  case refine_2 => exact execution_samples o (Compile.UARTRx.lift cfg receiver)
  done

/-- Arming consumes no receive sample or completion, but preserves the actual
consumer/clear transition on any unread initial mailbox. -/
theorem arm_step (cfg : Config) (buffer : Buffer.State) (active : Bool) (input : Input)
    (start : input.start = true) (reset : input.receiverReset = false)
    (flush : input.flush = false) :
    step cfg ⟨Rx.reset, buffer, active⟩ input =
      let edge := Buffer.step buffer (.cycle none input.take input.clearOverrun)
      ⟨⟨Rx.initial, edge.state, true⟩, edge.receipt⟩ := by
  simp [step, command, arrival, Rx.step, Rx.busy, Rx.result, Rx.reset, start, reset, flush]
  done

/-- While busy START is ignored; while stopped the supplied START is needed.
This local equality retains the full observer transition and receipt. -/
theorem step_continuous (cfg : Config) (s : State) (input : Input)
    (active : (Rx.busy s.receiver || input.start) = true) :
    step cfg s input = step cfg s {input with start := true} := by
  cases busy : Rx.busy s.receiver <;> simp_all [step, command, Rx.step]
  done

/-- The first observer edge has no receiver completion. Its consumer and clear
event still belongs to the history, including when the initial slot is full. -/
def warmup (buffer : Buffer.State) (incoming : Nat → Input) : Buffer.Transition :=
  Buffer.step buffer (.cycle none (incoming 1).take (incoming 1).clearOverrun)

/-- POST-step buffer controls on edge n are the observer controls on edge n+1.
The receive line remains on its original receiver edge. -/
def phaseInput (incoming : Nat → Input) (n : Nat) : Stream.Input :=
  {line := (incoming n).line, take := (incoming (n + 1)).take,
    clearOverrun := (incoming (n + 1)).clearOverrun}

/-- Every actual pulse-start history with no reset/flush has the same receiver
as continuous START. The initial consumer event is retained in `warmup`; later
mailbox states are exactly one edge behind the POST-step stream. -/
theorem phase_run (cfg : Config) (buffer : Buffer.State) (incoming : Nat → Input)
    (quiet : ∀ n, (incoming n).receiverReset = false ∧ (incoming n).flush = false)
    (active : ∀ n, (Rx.busy (run cfg ⟨Rx.initial, buffer, true⟩ incoming n).receiver ||
      (incoming (n + 1)).start) = true) (n : Nat) :
    run cfg ⟨Rx.initial, buffer, true⟩ incoming (n + 1) =
      ⟨(Stream.run cfg ⟨Rx.initial, (warmup buffer incoming).state⟩ (phaseInput incoming) (n + 1)).receiver,
        (Stream.run cfg ⟨Rx.initial, (warmup buffer incoming).state⟩ (phaseInput incoming) n).buffer,
        true⟩ := by
  induction n
  case zero =>
    simp [run, step, command, arrival, quiet, warmup, phaseInput, Rx.step, Rx.busy,
      Rx.initial, Rx.result, Stream.run, Stream.step]
  case succ n ih =>
    rw [run, step_continuous cfg _ _ (active (n + 1)), ih]
    simp [step, command, arrival, quiet, Stream.run, Stream.step, Stream.command, phaseInput]
  done

/-- The first exact receipt is kept separately from the shifted stream history. -/
theorem phase_first (cfg : Config) (buffer : Buffer.State) (incoming : Nat → Input)
    (quiet : (incoming 1).receiverReset = false ∧ (incoming 1).flush = false) :
    step cfg ⟨Rx.initial, buffer, true⟩ (incoming 1) =
      ⟨⟨Rx.step cfg Rx.initial false true (incoming 1).line,
        (warmup buffer incoming).state, true⟩, (warmup buffer incoming).receipt⟩ := by
  simp [step, command, arrival, Rx.initial, Rx.busy, Rx.result, Rx.step, quiet, warmup]
  done

/-- Reuses the existing delay theorem after applying, rather than suppressing,
the first consumer event. Equality starts after that event; its receipt is
`phase_first`, not an omitted prefix. -/
theorem phase_delayed_run (cfg : Config) (buffer : Buffer.State) (incoming : Nat → Input)
    (quiet : ∀ n, (incoming n).receiverReset = false ∧ (incoming n).flush = false)
    (active : ∀ n, (Rx.busy (run cfg ⟨Rx.initial, buffer, true⟩ incoming n).receiver ||
      (incoming (n + 1)).start) = true) (n : Nat) :
    run cfg ⟨Rx.initial, buffer, true⟩ incoming (n + 1) =
      run cfg ⟨Rx.initial, (warmup buffer incoming).state, false⟩
        (delayedInput (phaseInput incoming)) (n + 1) := by
  exact (phase_run cfg buffer incoming quiet active n).trans
    (uninterrupted_delay cfg (warmup buffer incoming).state (phaseInput incoming) (fun _ => rfl) n).symm

/-- All subsequent receipts agree exactly, including consume-plus-arrival and
clear-plus-drop. Consumer and clear controls move with the completion edge. -/
theorem phase_receipt (cfg : Config) (buffer : Buffer.State) (incoming : Nat → Input)
    (quiet : ∀ n, (incoming n).receiverReset = false ∧ (incoming n).flush = false)
    (active : ∀ n, (Rx.busy (run cfg ⟨Rx.initial, buffer, true⟩ incoming n).receiver ||
      (incoming (n + 1)).start) = true) (n : Nat) :
    (step cfg (run cfg ⟨Rx.initial, buffer, true⟩ incoming (n + 1)) (incoming (n + 2))).receipt =
      (Stream.step cfg
        (Stream.run cfg ⟨Rx.initial, (warmup buffer incoming).state⟩ (phaseInput incoming) n)
        (phaseInput incoming (n + 1))).receipt := by
  rw [phase_run cfg buffer incoming quiet active n]
  simp [step, command, arrival, quiet, Stream.run, Stream.step, Stream.command, phaseInput,
    Nat.add_assoc]
  done

/-- The physical observer ARM edge keeps generic packet ownership. No UART
interpretation of an older unread packet is needed for this transition. -/
theorem raw_arm_transition (pins : Chip.Pins) (o : Values Loader.Machine.Output)
    (host : HostResult.State) (ready : o (.core (.state .mode)) = 0)
    (flush : HostResult.resetting pins host = false) :
    (⟨HostResultBuffer.project (HostResult.next pins o host),
      HostResultBuffer.receipt pins o host⟩ : HostResultBuffer.Retained.Transition HostResultBuffer.Packet) =
      HostResultBuffer.Retained.step (HostResultBuffer.project host)
        (.cycle none (HostResult.consuming host) (HostResult.clearing host)) := by
  rw [HostResultBuffer.transition_refines]
  simp [HostResultBuffer.command, HostResultBuffer.arrival, HostResult.arriving, ready, flush]
  done

/-- A real start assertion sets the observer activity latch on the ARM edge. -/
theorem raw_arm_active (pins : Chip.Pins) (o : Values Loader.Machine.Output)
    (host : HostResult.State) (start : o (.control .start) = 1)
    (flush : HostResult.resetting pins host = false) :
    (HostResult.next pins o host).wasActive = true := by
  simp [HostResult.next, start, flush]
  done

/-- Receiver completion pulses retain their receiver edge; the observer buffer
receives that pulse on the following edge. -/
theorem phase_arrival (cfg : Config) (buffer : Buffer.State) (incoming : Nat → Input)
    (quiet : ∀ n, (incoming n).receiverReset = false ∧ (incoming n).flush = false)
    (active : ∀ n, (Rx.busy (run cfg ⟨Rx.initial, buffer, true⟩ incoming n).receiver ||
      (incoming (n + 1)).start) = true) (n : Nat) :
    arrival (run cfg ⟨Rx.initial, buffer, true⟩ incoming n) =
      Stream.arrival (Stream.run cfg ⟨Rx.initial, (warmup buffer incoming).state⟩ (phaseInput incoming) n) := by
  cases n
  case zero => rfl
  case succ n => simp only [phase_run cfg buffer incoming quiet active n, arrival, Stream.arrival, ↓reduceIte]
  done

/-- Strong stream timing for the PRE-step observer: a pulse in state n is
consumed by the mailbox on edge n+1. Receive timing places no restriction on
consumer stalls or the initial pending packet. -/
theorem phase_receive_series (t : UART.Link.Timing) (latency : UART.Link.Latency)
    (bytes : List (BitVec 8)) (age : Nat → Nat) (buffer : Buffer.State) (incoming : Nat → Input)
    (quiet : ∀ n, (incoming n).receiverReset = false ∧ (incoming n).flush = false)
    (active : ∀ n, (Rx.busy (run t.rx ⟨Rx.initial, buffer, true⟩ incoming n).receiver ||
      (incoming (n + 1)).start) = true)
    (safe : UART.StreamLink.Safe t latency) (within : latency.Contains age)
    (line : ∀ n, (incoming n).line = UART.StreamLink.sampled t bytes age n) :
    ∃ frames, frames.map Stream.FrameSpec.byte = bytes ∧ UART.StreamLink.Windows t latency frames ∧
      ∀ n, n ≤ Stream.horizon t.rx frames →
        arrival (run t.rx ⟨Rx.initial, buffer, true⟩ incoming n) = Stream.expected t.rx frames n := by
  obtain ⟨frames, payloads, windows, pulses⟩ := UART.StreamLink.receive_series t latency bytes age
    (phaseInput incoming) (warmup buffer incoming).state safe within line (fun _ => rfl)
  exact ⟨frames, payloads, windows, fun n hn =>
    (phase_arrival t.rx buffer incoming quiet active n).trans (pulses n hn)⟩
  done

/-- Canonical compiled execution inherits the same PRE-step completion event.
The paired-package session supplies this compiled-state relation through its
resident-image and SRAM proof, rather than assuming a desired fetch response. -/
theorem decoded_arrival (cfg : Config) (s : State) (incoming : Nat → Input)
    (spare : Nat → Bool) (valid : WellFormed cfg s.receiver) (n : Nat) :
    (if (decodedRun cfg (lift cfg s) incoming spare n).wasActive then
      Compile.UARTRx.result (decodedRun cfg (lift cfg s) incoming spare n).core else none) =
        arrival (run cfg s incoming n) := by
  rw [decoded_run cfg s incoming spare valid n]
  simp only [lift, arrival, Compile.UARTRx.result_lift]
  done

/-- The strongest existing Safe/age stream domain also applies to canonical E64
execution, with arbitrary spare-pin values and consumer controls. -/
theorem phase_decoded_receive_series (t : UART.Link.Timing) (latency : UART.Link.Latency)
    (bytes : List (BitVec 8)) (age : Nat → Nat) (buffer : Buffer.State) (incoming : Nat → Input)
    (spare : Nat → Bool)
    (quiet : ∀ n, (incoming n).receiverReset = false ∧ (incoming n).flush = false)
    (active : ∀ n, (Rx.busy (run t.rx ⟨Rx.initial, buffer, true⟩ incoming n).receiver ||
      (incoming (n + 1)).start) = true)
    (safe : UART.StreamLink.Safe t latency) (within : latency.Contains age)
    (line : ∀ n, (incoming n).line = UART.StreamLink.sampled t bytes age n) :
    ∃ frames, frames.map Stream.FrameSpec.byte = bytes ∧ UART.StreamLink.Windows t latency frames ∧
      ∀ n, n ≤ Stream.horizon t.rx frames →
        (if (decodedRun t.rx (lift t.rx ⟨Rx.initial, buffer, true⟩) incoming spare n).wasActive then
          Compile.UARTRx.result (decodedRun t.rx (lift t.rx ⟨Rx.initial, buffer, true⟩) incoming spare n).core
          else none) = Stream.expected t.rx frames n := by
  obtain ⟨frames, payloads, windows, pulses⟩ :=
    phase_receive_series t latency bytes age buffer incoming quiet active safe within line
  exact ⟨frames, payloads, windows, fun n hn =>
    (decoded_arrival t.rx ⟨Rx.initial, buffer, true⟩ incoming spare
      (by simp [WellFormed, Rx.initial]) n).trans (pulses n hn)⟩
  done

end Pinwheel.UART.Rx.BufferedSupervisor
