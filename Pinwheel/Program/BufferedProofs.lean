import Pinwheel.Program.Buffered
import Pinwheel.Program.TransferProofs

namespace Pinwheel.Program.Buffered

theorem terminal_valid (p : Program) (capacity : Transfer.Capacity) (s : State)
    (outcome : Transfer.Outcome) (valid : s.buffers.Valid capacity) :
    (terminal p capacity s outcome).buffers.Valid capacity := by
  exact Transfer.step_valid capacity s.buffers (.finish s.owner outcome) valid
  done

theorem settle_valid (p : Program) (capacity : Transfer.Capacity) (s : State)
    (valid : s.buffers.Valid capacity) : (settle p capacity s).buffers.Valid capacity := by
  cases control : s.core.control <;> simp_all [settle]
  rename_i reason
  cases reason
  all_goals simp_all [terminal_valid]
  done

theorem consumed_valid (capacity : Transfer.Capacity) (s : State)
    (valid : s.buffers.Valid capacity) : (consumed capacity s).1.buffers.Valid capacity := by
  exact Transfer.step_valid capacity s.buffers (.consumeTx s.owner) valid
  done

theorem appended_valid (capacity : Transfer.Capacity) (s : State) (input : Fin 2)
    (sampled : Engine.Reactive.Inputs) (valid : s.buffers.Valid capacity) :
    (appended capacity s input sampled).1.buffers.Valid capacity := by
  exact Transfer.step_valid capacity s.buffers (.appendRx s.owner sampled[input.val]) valid
  done

theorem entryEffects_valid (p : Program) (capacity : Transfer.Capacity) (s : State)
    (pc : PC) (sampled : Engine.Reactive.Inputs) (valid : s.buffers.Valid capacity) :
    (entryEffects p capacity s pc sampled).buffers.Valid capacity := by
  unfold entryEffects
  split
  all_goals grind [terminal_valid, consumed_valid, appended_valid]
  done

/-- Every composed edge preserves finite data bounds and identity provenance,
including entry failures after a successful TX consumption. -/
theorem advance_valid (p : Program) (capacity : Transfer.Capacity) (s : State)
    (incoming : Engine.Reactive.Inputs) (valid : s.buffers.Valid capacity) :
    (advance p capacity s incoming).buffers.Valid capacity := by
  grind [advance, settle_valid, entryEffects_valid]
  done

theorem start_valid (p : Program) (capacity : Transfer.Capacity) (s : State)
    (valid : s.buffers.Valid capacity) : (start p capacity s).buffers.Valid capacity := by
  grind [start, settle_valid, entryEffects_valid]
  done

theorem run_valid (p : Program) (capacity : Transfer.Capacity) (s : State)
    (incoming : Nat → Engine.Reactive.Inputs) (count : Nat) (valid : s.buffers.Valid capacity) :
    (run p capacity s incoming count).buffers.Valid capacity := by
  induction count <;> grind [run, advance_valid]
  done

theorem stale_owner_advance (p : Program) (capacity : Transfer.Capacity) (s : State)
    (incoming : Engine.Reactive.Inputs) (stale : owned s = false) :
    advance p capacity s incoming = s := by
  simp [advance, stale]
  done

theorem terminal_idle (p : Program) (capacity : Transfer.Capacity) (s : State)
    (outcome : Transfer.Outcome) : (terminal p capacity s outcome).core.pins = p.idle := by
  rfl
  done

theorem terminal_scratch_retained (p : Program) (capacity : Transfer.Capacity) (s : State)
    (outcome : Transfer.Outcome) : (terminal p capacity s outcome).core.samples = s.core.samples := by
  rfl
  done

theorem terminal_execution_retained (p : Program) (capacity : Transfer.Capacity) (s : State)
    (execution : Transfer.Execution) (running : s.buffers.slot = .running execution)
    (owner : s.owner = execution.request.identity) (outcome : Transfer.Outcome) :
    (terminal p capacity s outcome).buffers.slot = .completed ⟨execution, outcome⟩ := by
  simp [terminal, owner, Transfer.finish_retains_execution capacity s.buffers execution running outcome]
  done

theorem malformed_entry_has_no_effects (p : Program) (capacity : Transfer.Capacity) (s : State)
    (pc : PC) (sampled : Engine.Reactive.Inputs)
    (faulted : s.core.control = .stopped .fault) :
    entryEffects p capacity s pc sampled = s := by
  simp [entryEffects, faulted]
  done

theorem completed_advance_retained (p : Program) (capacity : Transfer.Capacity) (s : State)
    (completion : Transfer.Completion) (completed : s.buffers.slot = .completed completion)
    (incoming : Engine.Reactive.Inputs) : advance p capacity s incoming = s := by
  simp [advance, owned, completed]
  done

theorem self_jump_is_entry (p : Program) (s : State) (pc : PC)
    (action : Engine.Reactive.Action 15) (guard : Engine.Reactive.Check)
    (terminalCapture : Option (Engine.Reactive.Capture 15)) (sampled : Engine.Reactive.Inputs)
    (checked : s.core.control = .checked pc 0)
    (fetched : p.fetch pc = some {operation := .checked action guard terminalCapture (.jump pc)})
    (ready : guard.ready sampled = true) (inRange : pc.val ≤ p.last.val) :
    entryTarget p s sampled = some pc := by
  simp [entryTarget, checked, fetched, ready, finishTarget, inRange]
  done

end Pinwheel.Program.Buffered
