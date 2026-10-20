import Pinwheel.Hardware.Buffered.LifecycleEpoch
import Pinwheel.Program.Buffered

set_option maxRecDepth 4096

/-! Logical epoch renaming preserves complete buffered source execution.
This lifts the epoch-zero source seed to a later logical reset epoch without
adding an epoch field to the hardware wire identity. -/
namespace Pinwheel.Hardware.Buffered.Lifecycle.EpochView
open Pinwheel.Program

def buffered (offset : Nat) (s : Buffered.State) : Buffered.State :=
  {s with buffers := state offset s.buffers, owner := identity offset s.owner}

theorem identity_beq (offset : Nat) (a b : Transfer.Identity) :
    (identity offset a == identity offset b) = (a == b) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, identity_injective]
  done

theorem owned (offset : Nat) (s : Buffered.State) :
    Buffered.owned (buffered offset s) = Buffered.owned s := by
  cases stored : s.buffers.slot
  all_goals simp [Buffered.owned, buffered, state, slot, request, execution,
    completion, stored, identity_beq]
  done

theorem txBit (offset : Nat) (s : Buffered.State) :
    Buffered.txBit (buffered offset s) = Buffered.txBit s := by
  cases stored : s.buffers.slot
  all_goals simp [Buffered.txBit, buffered, state, slot, request, execution,
    completion, stored]
  done

theorem normalize (offset : Nat) (s : Buffered.State) (pc : Buffered.PC)
    (instruction : Buffered.Instruction) :
    Buffered.normalize (buffered offset s) pc instruction = Buffered.normalize s pc instruction := by
  cases instruction.operation
  all_goals simp only [Buffered.normalize, txBit]
  all_goals rfl
  done

theorem lower (offset : Nat) (p : Buffered.Program) (s : Buffered.State) :
    Buffered.lower p (buffered offset s) = Buffered.lower p s := by
  unfold Buffered.lower
  congr 1
  funext pc
  cases fetch : p.fetch pc
  all_goals simp [normalize]
  done

theorem terminal (offset : Nat) (p : Buffered.Program) (capacity : Transfer.Capacity)
    (s : Buffered.State) (outcome : Transfer.Outcome) :
    Buffered.terminal p capacity (buffered offset s) outcome =
      buffered offset (Buffered.terminal p capacity s outcome) := by
  unfold Buffered.terminal
  rw [lower]
  have step := step_rename capacity s.buffers (.finish s.owner outcome) offset
  change Transfer.step capacity (state offset s.buffers)
    (.finish (identity offset s.owner) outcome) = _ at step
  simp only [buffered]
  rw [step]
  rfl
  done

theorem settle (offset : Nat) (p : Buffered.Program) (capacity : Transfer.Capacity)
    (s : Buffered.State) :
    Buffered.settle p capacity (buffered offset s) = buffered offset (Buffered.settle p capacity s) := by
  simp only [Buffered.settle, buffered]
  cases s.core.control
  case stopped reason => cases reason <;> first | exact terminal offset p capacity s _ | rfl
  all_goals rfl
  done

theorem consumed (offset : Nat) (capacity : Transfer.Capacity) (s : Buffered.State) :
    Buffered.consumed capacity (buffered offset s) =
      ((buffered offset (Buffered.consumed capacity s).1), (Buffered.consumed capacity s).2) := by
  have step := step_rename capacity s.buffers (.consumeTx s.owner) offset
  unfold Buffered.consumed
  change Transfer.step capacity (state offset s.buffers)
    (.consumeTx (identity offset s.owner)) = _ at step
  simp only [buffered]
  rw [step]
  cases hreply : (Transfer.step capacity s.buffers (.consumeTx s.owner)).reply
  all_goals simp only [transition, hreply, reply]
  done

theorem appended (offset : Nat) (capacity : Transfer.Capacity) (s : Buffered.State)
    (input : Fin 2) (sampled : Engine.Reactive.Inputs) :
    Buffered.appended capacity (buffered offset s) input sampled =
      ((buffered offset (Buffered.appended capacity s input sampled).1),
        (Buffered.appended capacity s input sampled).2) := by
  have step := step_rename capacity s.buffers (.appendRx s.owner sampled[input.val]) offset
  unfold Buffered.appended
  change Transfer.step capacity (state offset s.buffers)
    (.appendRx (identity offset s.owner) sampled[input.val]) = _ at step
  simp only [buffered]
  rw [step]
  cases hreply : (Transfer.step capacity s.buffers (.appendRx s.owner sampled[input.val])).reply
  all_goals simp only [transition, hreply, reply]
  all_goals rfl
  done

private theorem buffered_if (offset : Nat) (condition : Prop) [Decidable condition]
    (yes no : Buffered.State) :
    (if condition then buffered offset yes else buffered offset no) =
      buffered offset (if condition then yes else no) := by
  split <;> rfl
  done

theorem entryEffects (offset : Nat) (p : Buffered.Program) (capacity : Transfer.Capacity)
    (s : Buffered.State) (pc : Buffered.PC) (sampled : Engine.Reactive.Inputs) :
    Buffered.entryEffects p capacity (buffered offset s) pc sampled =
      buffered offset (Buffered.entryEffects p capacity s pc sampled) := by
  simp only [Buffered.entryEffects, show (buffered offset s).core = s.core from rfl]
  split
  · rfl
  · cases fetch : p.fetch pc
    · exact terminal offset p capacity s .fault
    · rename_i instruction
      cases operation : instruction.operation
      all_goals simp [operation, consumed, appended, terminal]
      all_goals cases append : instruction.append
      all_goals dsimp only
      all_goals simp only [buffered_if]
  done

theorem entryTarget (offset : Nat) (p : Buffered.Program) (s : Buffered.State)
    (sampled : Engine.Reactive.Inputs) :
    Buffered.entryTarget p (buffered offset s) sampled = Buffered.entryTarget p s sampled := rfl

theorem start (offset : Nat) (p : Buffered.Program) (capacity : Transfer.Capacity)
    (s : Buffered.State) :
    Buffered.start p capacity (buffered offset s) = buffered offset (Buffered.start p capacity s) := by
  simp only [Buffered.start, owned, lower]
  split
  · change Buffered.settle p capacity (Buffered.entryEffects p capacity
      (buffered offset {s with core := Engine.Reactive.Fetch.start (Buffered.lower p s) s.samplerSecond})
      0 s.samplerSecond) = _
    rw [entryEffects, settle]
  · rfl
  done

theorem advance (offset : Nat) (p : Buffered.Program) (capacity : Transfer.Capacity)
    (s : Buffered.State) (incoming : Engine.Reactive.Inputs) :
    Buffered.advance p capacity (buffered offset s) incoming =
      buffered offset (Buffered.advance p capacity s incoming) := by
  simp only [Buffered.advance, owned, lower,
    show (buffered offset s).core = s.core from rfl,
    show (buffered offset s).samplerFirst = s.samplerFirst from rfl,
    show (buffered offset s).samplerSecond = s.samplerSecond from rfl, entryTarget]
  split
  · cases target : Buffered.entryTarget p s s.samplerSecond
    · exact settle offset p capacity {s with
        core := Engine.Reactive.Fetch.advance (Buffered.lower p s) s.core s.samplerSecond
        samplerFirst := incoming
        samplerSecond := s.samplerFirst}
    · rename_i pc
      change Buffered.settle p capacity (Buffered.entryEffects p capacity
        (buffered offset {s with
          core := Engine.Reactive.Fetch.advance (Buffered.lower p s) s.core s.samplerSecond
          samplerFirst := incoming
          samplerSecond := s.samplerFirst}) pc s.samplerSecond) = _
      rw [entryEffects, settle]
  · rfl
  done

theorem run (offset : Nat) (p : Buffered.Program) (capacity : Transfer.Capacity)
    (s : Buffered.State) (incoming : Nat → Engine.Reactive.Inputs) (n : Nat) :
    Buffered.run p capacity (buffered offset s) incoming n =
      buffered offset (Buffered.run p capacity s incoming n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [Buffered.run, ih, advance]
  done

end Pinwheel.Hardware.Buffered.Lifecycle.EpochView
