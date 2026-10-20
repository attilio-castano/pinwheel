import Pinwheel.Program.StreamingReadySession
import Pinwheel.Program.StreamingUARTQuiet

/-! Public idle host pins generate quiet engine actions even though inactive
START operands remain in the frontend registers. No literal-zero command
record, core status or raw-input agreement is assumed. -/
namespace Pinwheel.Program.StreamingUART.HostQuiet
open Pinwheel.Program.StreamingReady

structure Idle (s : Streaming.Host.State) : Prop where
  phase : s.phase = 0
  inactive : s.active = false

structure Pins (i : Session.Pins) : Prop where
  cold : i.initialize = false
  selected : i.csn = true
  clock : i.sck = false

theorem command_quiet (s : Session.State a) (i : Session.Pins)
    (idle : Idle s.host) (pins : Pins i) : QuietTiming.Quiet (s.command i).runtime := by
  constructor
  · exact pins.cold
  · simp [Session.State.command,Streaming.Host.State.command,Streaming.Host.State.delivering,idle.phase]
  · simp [Session.State.command,Streaming.Host.State.command,Streaming.Host.State.stagedTX,idle.phase]
  · simp [Session.State.command,Streaming.Host.State.command,Streaming.Host.State.stagedRX,idle.phase]

theorem host_step (s : Streaming.Host.State) (i : Streaming.Host.Input)
    (idle : Idle s) (cold : i.initialize = false) (selected : i.csn = true) :
    Streaming.Host.step i s = {s with sckPrev := i.sck, csnPrev := i.csn} := by
  simp [Streaming.Host.step,cold,idle.phase,idle.inactive,selected,
    Streaming.Host.State.startingFrame,Streaming.Host.State.closing,
    Streaming.Host.State.closingRequest,Streaming.Host.State.closingReadExact,
    Streaming.Host.State.taking,Streaming.Host.State.receiving,
    Streaming.Host.State.finishingCRC,Streaming.Host.State.admittingBulk,
    Streaming.Host.State.stagedTX,Streaming.Host.State.stagedRX,
    Streaming.Host.State.stageRejected,Streaming.Host.State.clearingExport,
    Streaming.Host.State.delivering]

theorem step_idle (s : Session.State a) (p : Program) (pending : Bool) (i : Session.Pins)
    (idle : Idle s.host) (pins : Pins i) : Idle (s.step p pending i).host := by
  change Idle (Streaming.Host.step (s.hostInput pending i) s.host)
  rw [host_step s.host (s.hostInput pending i) idle pins.cold pins.selected]
  exact ⟨idle.phase,idle.inactive⟩

theorem run_idle (s : Session.State a) (p : Program) (pending : Bool) (inputs : List Session.Pins)
    (idle : Idle s.host) (pins : ∀ i ∈ inputs, Pins i) : Idle (s.run p pending inputs).host := by
  induction inputs generalizing s with
  | nil => exact idle
  | cons i rest ih =>
    exact ih (s.step p pending i) (step_idle s p pending i idle (pins i (by simp)))
      (fun j member => pins j (by simp [member]))

theorem runtime_trace (s : Session.State a) (p : Program) (pending : Bool) (inputs : List Session.Pins)
    (idle : Idle s.host) (pins : ∀ i ∈ inputs, Pins i) :
    Session.RuntimeTrace p pending s inputs := by
  induction inputs generalizing s with
  | nil => trivial
  | cons i rest ih =>
    have pin := pins i (by simp)
    have quiet := command_quiet s i idle pin
    constructor
    · exact ⟨quiet.cold,by rw [quiet.command]; decide,
        by rw [quiet.command]; decide,by rw [quiet.command]; decide⟩
    · exact ih (s.step p pending i) (step_idle s p pending i idle pin)
        (fun j member => pins j (by simp [member]))

theorem runtime_inputs_quiet (s : Session.State a) (p : Program) (pending : Bool)
    (inputs : List Session.Pins) (idle : Idle s.host) (pins : ∀ i ∈ inputs, Pins i) :
    ∀ i ∈ s.runtimeInputs p pending inputs, QuietTiming.Quiet i := by
  induction inputs generalizing s with
  | nil => simp [Session.State.runtimeInputs]
  | cons i rest ih =>
    intro j member
    simp only [Session.State.runtimeInputs,List.mem_cons] at member
    rcases member with same | later
    · subst j
      exact command_quiet s i idle (pins i (by simp))
    · exact ih (s.step p pending i) (step_idle s p pending i idle (pins i (by simp)))
        (fun j member => pins j (by simp [member])) j later

theorem runtime_inputs_raw (s : Session.State a) (p : Program) (pending : Bool)
    (inputs : List Session.Pins) :
    (s.runtimeInputs p pending inputs).map (fun i => i.rawInputs) = inputs.map (fun i => i.rawInputs) := by
  induction inputs generalizing s with
  | nil => rfl
  | cons i rest ih =>
    change i.rawInputs :: ((s.step p pending i).runtimeInputs p pending rest).map (fun i => i.rawInputs) =
      i.rawInputs :: rest.map (fun i => i.rawInputs)
    rw [ih]

theorem runtime_inputs_length (s : Session.State a) (p : Program) (pending : Bool)
    (inputs : List Session.Pins) : (s.runtimeInputs p pending inputs).length = inputs.length := by
  have lengths := congrArg List.length (runtime_inputs_raw s p pending inputs)
  simpa only [List.length_map] using lengths

/-- Inactive operands do not influence the engine, including its queues. -/
theorem step_canonical (p : Program) (s : State a) (i : Input) (quiet : QuietTiming.Quiet i) :
    step p i s = step p {rawInputs := i.rawInputs} s := by
  simp [step,quiet.cold,quiet.command,clock,State.hostPush,State.hostPop,quiet.tx,quiet.rx]

/-- The actual frontend's quiet commands reduce to public raw samples only. -/
theorem run_core_canonical (s : Session.State a) (p : Program) (pending : Bool)
    (inputs : List Session.Pins) (idle : Idle s.host) (pins : ∀ i ∈ inputs, Pins i) :
    (s.run p pending inputs).core =
      run p s.core (inputs.map (fun i => ({rawInputs := i.rawInputs} : Input))) := by
  induction inputs generalizing s with
  | nil => rfl
  | cons i rest ih =>
    have pin := pins i (by simp)
    have next := step_canonical p s.core (s.command i).runtime (command_quiet s i idle pin)
    change ((s.step p pending i).run p pending rest).core =
      run p (step p {rawInputs := i.rawInputs} s.core)
        (rest.map (fun i => ({rawInputs := i.rawInputs} : Input)))
    rw [ih (s.step p pending i) (step_idle s p pending i idle pin)
      (fun j member => pins j (by simp [member]))]
    change run p (step p (s.command i).runtime s.core) _ = _
    rw [next]
    rfl

end Pinwheel.Program.StreamingUART.HostQuiet
