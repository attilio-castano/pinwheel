import Pinwheel.Hardware.Storage.PairedStream

/-! The actual stream package closed over its single-port memory contract.
The supervisor, pin adapters and result observer use their real pre-edge state;
initial memory contents, Q and all represented registers are unrestricted. -/
namespace Pinwheel.Hardware.Storage.PairedStreamPackage
open Pinwheel.Hardware
open SramController (Reads Out bypass)
set_option backward.isDefEq.respectTransparency false

structure State (S : Type) where
  core : Values PairedController.Register × S
  enabled : Bool
  adapters : Chip.State
  result : HostResult.State

def controller (s : State S) : Values PairedStream.Register :=
  Extended.values s.core.1 (fun {_} r => match r with
    | .enabled => BitVec.ofBool s.enabled)

def registers (s : State S) : Values PairedStream.FullRegister :=
  Extended.values (Chip.values (controller s) s.adapters) s.result.values

def State.physical (s : State S) : Values PairedStream.FullRegister × S :=
  (registers s, s.core.2)

def rawInput (s : State S) : Loader.Machine.Inputs := PairedPackage.decoded s.adapters

theorem controller_eq (s : State S) :
    (controller s : Values PairedStream.Register) =
      (Extended.values s.core.1 (fun {w} (r : PairedStream.SupervisorRegister w) => match w, r with
        | _, .enabled => BitVec.ofBool s.enabled) : Values PairedStream.Register) := rfl

theorem rawInput_eq (s : State S) :
    rawInput s = Serial.feed s.adapters.second s.adapters.receiver := rfl

def policy (s : State S) : PairedStream.Transition :=
  PairedStream.step ⟨s.enabled⟩
    ⟨s.core.1 .mode, s.core.1 .valid == 1, s.core.1 .pending == 1⟩ (rawInput s)

def effective (s : State S) : Loader.Machine.Inputs := (policy s).effective

def coreOutput (memory : Memory.SinglePort.Contract S 9 64) (s : State S) :
    Values Loader.Machine.Output :=
  (PairedClosed.implementation PairedComposition.graph memory).observe (effective s).values s.core

def interpreted (memory : Memory.SinglePort.Contract S 9 64) :
    Timed.Component Chip.Pins (State S) (Values Chip.Output) where
  step := fun i s =>
    ⟨(PairedClosed.implementation PairedComposition.graph memory).step (effective s).values s.core,
      (policy s).state.enabled, PairedPackage.adaptersNext i s.adapters,
      HostResult.next i (coreOutput memory s) s.result⟩
  observe := fun _ s => fun {_} p =>
    (PairedStream.overlay (registers s)
      (fun {_} o => match o with
        | .base p => HostResult.shown (coreOutput memory s) s.result p
        | .port p => (PairedComposition.graph.observe
          (PairedClosed.feedback (effective s).values (memory.view s.core.2).q) s.core.1) (.port p))) (.base p)

def executable (c : PairedComposition.Component (Reads Chip.Pin) PairedStream.FullRegister (Out Chip.Output))
    (memory : Memory.SinglePort.Contract S 9 64) :
    Timed.Component Chip.Pins (Values PairedStream.FullRegister × S) (Values Chip.Output) where
  step := fun i => (PairedClosed.implementation c memory).step i.values
  observe := fun i => (PairedClosed.implementation c memory).observe i.values

theorem effective_feedback (memory : Memory.SinglePort.Contract S 9 64) (s : State S) :
    (PairedStream.effectiveInputs
      (PairedClosed.feedback (rawInput s).values (memory.view s.core.2).q) (controller s) : Values PairedController.Input) =
      (PairedClosed.feedback (effective s).values (memory.view s.core.2).q : Values PairedController.Input) := by
  funext w p
  cases p
  all_goals simp [PairedStream.effectiveInputs, PairedClosed.feedback, effective, policy,
    PairedStream.policy, PairedStream.state, PairedStream.status, PairedStream.rawInput,
    controller, Extended.values, Loader.Machine.Inputs.values, Bool.beq_eq_decide_eq]
  done

theorem next_feedback (memory : Memory.SinglePort.Contract S 9 64) (s : State S)
    (r : PairedStream.SupervisorRegister w) :
    PairedStream.nextValues
      (PairedClosed.feedback (rawInput s).values (memory.view s.core.2).q) (controller s) r =
      (match r with | .enabled => BitVec.ofBool (policy s).state.enabled) := by
  cases r
  simp [PairedStream.nextValues, PairedStream.nextEnabled, PairedStream.policy,
    PairedStream.state, PairedStream.status, PairedStream.rawInput, policy,
    controller, Extended.values, PairedClosed.feedback, Loader.Machine.Inputs.values,
    Bool.beq_eq_decide_eq]
  done

private theorem inner_values (r : Values R) (x : Values X) :
    (Extended.innerValues (Extended.values r x) : Values R) = (r : Values R) := rfl

private theorem extra_values (r : Values R) (x : Values X) :
    (Extended.extraValues (Extended.values r x) : Values X) = (x : Values X) := rfl

private theorem pin_feed (i : Chip.Pins) :
    (Chip.pinMap.feed i.values (Chip.pinModel.state ()) : Values Serial.Input) =
      ((Chip.wired i).values : Values Serial.Input) := Chip.pinModel.feed_eq i ()

private theorem pin_step (i : Chip.Pins) :
    (Chip.pinMap.step i.values (Chip.pinModel.state ()) : Values NoRegister) =
      (Chip.pinModel.state () : Values NoRegister) := Chip.pinModel.step_eq i ()

private theorem sampler_feed (i a b : Serial.Inputs) :
    (Feeder.sampler.feed i.values (Chip.sampling.state (a, b)) : Values Serial.Input) =
      (b.values : Values Serial.Input) := Chip.sampling.feed_eq i (a, b)

private theorem sampler_step (i a b : Serial.Inputs) :
    (Feeder.sampler.step i.values (Chip.sampling.state (a, b)) : Values (Feeder.Sampled Serial.Input)) =
      (Chip.sampling.state (i, a) : Values (Feeder.Sampled Serial.Input)) := Chip.sampling.step_eq i (a, b)

private theorem serial_feed (i : Serial.Inputs) (s : Serial.State) :
    (Serial.receiver.feed i.values s.values : Values Loader.Machine.Input) =
      ((Serial.feed i s).values : Values Loader.Machine.Input) := Serial.model.feed_eq i s

private theorem serial_step (i : Serial.Inputs) (s : Serial.State) :
    (Serial.receiver.step i.values s.values : Values Serial.Register) =
      ((Serial.next i s).values : Values Serial.Register) := Serial.model.step_eq i s

theorem step_physical (memory : Memory.SinglePort.Contract S 9 64) (i : Chip.Pins) (s : State S) :
    (executable (PairedStream.packaged PairedStream.reference) memory).step i s.physical =
      ((interpreted memory).step i s).physical := by
  apply Prod.ext
  case fst =>
    funext w r
    cases r
    all_goals simp only [executable, PairedClosed.implementation, PairedClosed.closed, State.physical,
      registers, Chip.values, PairedStream.packaged, PairedStream.basePackaged,
      PairedComposition.observed, PairedComposition.fed, inner_values, extra_values,
      Extended.values, PairedPackage.bypass_feed, PairedPackage.bypass_step, pin_feed, sampler_feed,
      serial_feed, pin_step, sampler_step, serial_step, interpreted, PairedPackage.adaptersNext,
      controller, PairedStream.reference, PairedStream.wrapped]
    all_goals simp only [← controller_eq, ← rawInput_eq, effective_feedback, next_feedback]
    exact (PairedPackage.observer_next _ _ _ _ _).trans
      (HostResult.next_correct i (coreOutput memory s) s.result _)
    done
  case snd =>
    simp only [executable, PairedClosed.implementation, PairedClosed.closed, State.physical,
      registers, Chip.values, PairedStream.packaged, PairedStream.basePackaged,
      PairedComposition.observed, PairedComposition.fed, inner_values, extra_values,
      PairedPackage.bypass_feed, pin_feed, sampler_feed, serial_feed,
      interpreted, controller, PairedStream.reference, PairedStream.wrapped, PairedClosed.command,
      PairedStream.overlay, SramAssembly.observer, Observed.values, Expr.eval]
    simp only [← controller_eq, ← rawInput_eq, effective_feedback]
    done

theorem observe_physical (memory : Memory.SinglePort.Contract S 9 64) (i : Chip.Pins) (s : State S) :
    ((executable (PairedStream.packaged PairedStream.reference) memory).observe i s.physical : Values Chip.Output) =
      ((interpreted memory).observe i s : Values Chip.Output) := by
  funext w p
  simp only [executable, PairedClosed.implementation, PairedClosed.closed, State.physical,
    registers, Chip.values, PairedStream.packaged, PairedStream.basePackaged,
    PairedComposition.observed, PairedComposition.fed, inner_values, extra_values,
    PairedPackage.bypass_feed, pin_feed, sampler_feed, serial_feed,
    interpreted, controller, PairedStream.reference, PairedStream.wrapped]
  simp only [← controller_eq, ← rawInput_eq, effective_feedback]
  cases p
  all_goals simp only [PairedStream.overlay, PairedPackage.observer_output]
  all_goals simp only [HostResult.output_correct]
  all_goals rfl
  done

/-- The emitted package has the modeled pre-edge and post-edge pin values for
every finite history, without assumptions on memory Q or initial registers. -/
theorem retained_trace
    (n : Netlist PairedStream.Register PairedStream.Output PairedStream.Input)
    (hn : PairedStream.core = .ok n)
    (memory : Memory.SinglePort.Contract S 9 64) (s : State S) (history : List Chip.Pins) :
    (executable (PairedStream.package n).component memory).trace s.physical history =
      (interpreted memory).trace s history := by
  rw [PairedStream.emitted_package_correct n hn]
  induction history generalizing s with
  | nil => rfl
  | cons i rest ih =>
    simp only [Timed.Component.trace, Timed.Component.edge, step_physical, observe_physical, ih]
  done

theorem retained_run
    (n : Netlist PairedStream.Register PairedStream.Output PairedStream.Input)
    (hn : PairedStream.core = .ok n)
    (memory : Memory.SinglePort.Contract S 9 64) (s : State S) (history : List Chip.Pins) :
    (executable (PairedStream.package n).component memory).run s.physical history =
      ((interpreted memory).run s history).physical := by
  rw [PairedStream.emitted_package_correct n hn]
  induction history generalizing s with
  | nil => rfl
  | cons i rest ih =>
    simpa only [Timed.Component.run, step_physical] using ih ((interpreted memory).step i s)
  done

end Pinwheel.Hardware.Storage.PairedStreamPackage
