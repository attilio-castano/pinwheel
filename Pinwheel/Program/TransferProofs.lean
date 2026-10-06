import Pinwheel.Program.Transfer
import Init.Data.List.Lemmas

namespace Pinwheel.Program.Transfer

/-- The hardest preservation obligation includes both data bounds and the
nonwrapping identity allocation invariant. -/
theorem admittedStep_valid (capacity : Capacity) (s : State) (command : Command)
    (valid : s.Valid capacity) : (admittedStep capacity s command).state.Valid capacity := by
  cases command
  all_goals cases slot : s.slot
  all_goals simp_all [admittedStep, reject, State.Valid, Slot.Bounded, Slot.identity,
    Execution.Bounded, Request.Bounded]
  all_goals grind [List.getElem?_eq_some_iff]
  done

theorem initial_valid (capacity : Capacity) : ({} : State).Valid capacity := by
  simp [State.Valid, Slot.Bounded, Slot.identity]
  done

theorem step_valid (capacity : Capacity) (s : State) (command : Command)
    (valid : s.Valid capacity) : (step capacity s command).state.Valid capacity := by
  cases identity : command.identity
  all_goals simp only [step, identity]
  all_goals grind [admittedStep_valid, reject]
  done

theorem run_valid (capacity : Capacity) (s : State) (commands : List Command)
    (valid : s.Valid capacity) : (run capacity s commands).state.Valid capacity := by
  induction commands generalizing s
  all_goals grind [run, step_valid]
  done

theorem wrong_identity_rejected (capacity : Capacity) (s : State) (command : Command)
    (id : Identity) (identified : command.identity = some id)
    (wrong : s.slot.identity ≠ some id) : step capacity s command = reject s .wrongIdentity := by
  simp [step, identified, wrong]
  done

theorem wrong_epoch_rejected (capacity : Capacity) (s : State) (command : Command)
    (valid : s.Valid capacity) (id : Identity) (identified : command.identity = some id)
    (wrong : id.epoch ≠ s.epoch) : step capacity s command = reject s .wrongIdentity := by
  grind [wrong_identity_rejected, State.Valid]
  done

theorem read_nondestructive (capacity : Capacity) (s : State) (id : Identity) :
    (step capacity s (.read id)).state = s := by
  grind [step, Command.identity, admittedStep, reject]
  done

theorem running_release_rejected (capacity : Capacity) (s : State) (e : Execution)
    (running : s.slot = .running e) :
    step capacity s (.release e.request.identity) = reject s .wrongPhase := by
  simp [step, Command.identity, running, Slot.identity, admittedStep]
  done

/-- All commands except reset and matching release retain the exact completed
descriptor, TX, RX prefix, counts and outcome, including invalid engine commands. -/
theorem completed_retained (capacity : Capacity) (s : State) (c : Completion)
    (completed : s.slot = .completed c) (command : Command)
    (noReset : command ≠ .reset) (noRelease : ∀ id, command ≠ .release id) :
    (step capacity s command).state = s := by
  cases command
  all_goals grind [step, Command.identity, admittedStep, reject]
  done

theorem finish_retains_execution (capacity : Capacity) (s : State) (e : Execution)
    (running : s.slot = .running e) (outcome : Outcome) :
    step capacity s (.finish e.request.identity outcome) =
      ⟨{s with slot := .completed ⟨e, outcome⟩}, .finished⟩ := by
  simp [step, Command.identity, running, Slot.identity, admittedStep]
  done

theorem start_freezes_request (capacity : Capacity) (s : State) (r : Request)
    (preparing : s.slot = .preparing r) :
    step capacity s (.start r.identity r.programGeneration) =
      ⟨{s with slot := .running ⟨r, 0, []⟩}, .started⟩ := by
  simp [step, Command.identity, preparing, Slot.identity, admittedStep]
  done

theorem wrong_generation_rejected (capacity : Capacity) (s : State) (r : Request)
    (preparing : s.slot = .preparing r) (generation : Nat)
    (wrong : generation ≠ r.programGeneration) :
    step capacity s (.start r.identity generation) = reject s .programGeneration := by
  simp [step, Command.identity, preparing, Slot.identity, admittedStep, wrong]
  done

theorem occupied_prepare_rejected (capacity : Capacity) (s : State)
    (occupied : s.slot ≠ .free) (generation : Nat) (tx : List Bool) (rxLimit : Nat) :
    step capacity s (.prepare generation tx rxLimit) = reject s .wrongPhase := by
  cases slot : s.slot
  all_goals simp_all [step, Command.identity, admittedStep]
  done

theorem capacity_rejected (capacity : Capacity) (s : State) (free : s.slot = .free)
    (generation : Nat) (tx : List Bool) (rxLimit : Nat)
    (tooLarge : ¬ (tx.length ≤ capacity.txBits ∧ rxLimit ≤ capacity.rxBits)) :
    step capacity s (.prepare generation tx rxLimit) = reject s .capacity := by
  simp [step, Command.identity, admittedStep, free, tooLarge]
  done

theorem prepare_allocates (capacity : Capacity) (s : State) (free : s.slot = .free)
    (generation : Nat) (tx : List Bool) (rxLimit : Nat)
    (fits : tx.length ≤ capacity.txBits ∧ rxLimit ≤ capacity.rxBits) :
    step capacity s (.prepare generation tx rxLimit) =
      ⟨{s with nextSequence := s.nextSequence + 1, slot := .preparing ⟨⟨s.epoch, s.nextSequence⟩, generation, tx, rxLimit⟩},
        .prepared ⟨s.epoch, s.nextSequence⟩⟩ := by
  simp [step, Command.identity, admittedStep, free, fits]
  done

theorem completed_release (capacity : Capacity) (s : State) (c : Completion)
    (completed : s.slot = .completed c) :
    step capacity s (.release c.execution.request.identity) =
      ⟨{s with slot := .free}, .released⟩ := by
  simp [step, Command.identity, admittedStep, completed, Slot.identity]
  done

theorem reset_invalidates (capacity : Capacity) (s : State) :
    step capacity s .reset = ⟨⟨s.epoch + 1, 1, .free⟩, .reset⟩ := by
  rfl
  done

theorem reset_then_prepare_rejects_old_identity (capacity : Capacity) (s : State)
    (old : Identity) (oldEpoch : old.epoch = s.epoch) (generation : Nat)
    (tx : List Bool) (rxLimit : Nat) (command : Command)
    (identified : command.identity = some old) :
    let reset := (step capacity s .reset).state
    let prepared := (step capacity reset (.prepare generation tx rxLimit)).state
    step capacity prepared command = reject prepared .wrongIdentity := by
  simp only [reset_invalidates]
  grind [step, Command.identity, admittedStep, Slot.identity, reject]
  done

theorem consume_tx_exact (capacity : Capacity) (s : State) (e : Execution)
    (running : s.slot = .running e) (bit : Bool)
    (available : e.request.tx[e.txConsumed]? = some bit) :
    step capacity s (.consumeTx e.request.identity) =
      ⟨{s with slot := .running {e with txConsumed := e.txConsumed + 1}}, .txBit bit⟩ := by
  simp [step, Command.identity, running, Slot.identity, admittedStep, available]
  done

theorem append_rx_exact (capacity : Capacity) (s : State) (e : Execution)
    (running : s.slot = .running e) (bit : Bool)
    (room : e.rx.length < e.request.rxLimit) :
    step capacity s (.appendRx e.request.identity bit) =
      ⟨{s with slot := .running {e with rx := e.rx ++ [bit]}}, .rxStored⟩ := by
  simp [step, Command.identity, running, Slot.identity, admittedStep, room]
  done

theorem tx_exhausted_rejected (capacity : Capacity) (s : State) (e : Execution)
    (running : s.slot = .running e) (exhausted : e.request.tx[e.txConsumed]? = none) :
    step capacity s (.consumeTx e.request.identity) = reject s .txExhausted := by
  simp [step, Command.identity, running, Slot.identity, admittedStep, exhausted]
  done

theorem rx_full_rejected (capacity : Capacity) (s : State) (e : Execution)
    (running : s.slot = .running e) (bit : Bool)
    (full : ¬ e.rx.length < e.request.rxLimit) :
    step capacity s (.appendRx e.request.identity bit) = reject s .rxFull := by
  simp [step, Command.identity, running, Slot.identity, admittedStep, full]
  done

theorem release_then_prepare_rejects_old_identity (capacity : Capacity) (s : State)
    (c : Completion) (completed : s.slot = .completed c) (valid : s.Valid capacity)
    (generation : Nat) (tx : List Bool) (rxLimit : Nat) (command : Command)
    (identified : command.identity = some c.execution.request.identity) :
    let released := (step capacity s (.release c.execution.request.identity)).state
    let prepared := (step capacity released (.prepare generation tx rxLimit)).state
    step capacity prepared command = reject prepared .wrongIdentity := by
  simp only [completed_release capacity s c completed]
  grind [step, Command.identity, admittedStep, Slot.identity, reject, State.Valid]
  done

end Pinwheel.Program.Transfer
