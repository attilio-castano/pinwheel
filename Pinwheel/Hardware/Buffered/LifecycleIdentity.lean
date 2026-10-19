import Pinwheel.Program.Transfer

/-! A checked identity renaming from logical epoch-local sequence numbers to a
wire-sequence view. Warm reset needs a fresh offset because its hardware
transfer counter persists. Cold reset can reuse wire pairs, so this adapter
does not assert authentication or replay exclusion across cold initialization. -/
namespace Pinwheel.Hardware.Buffered.Lifecycle.IdentityView
open Pinwheel.Program.Transfer

def identity (offset : Nat) (id : Identity) : Identity :=
  {id with sequence := offset + id.sequence}

def request (offset : Nat) (r : Request) : Request :=
  {r with identity := identity offset r.identity}

def execution (offset : Nat) (e : Execution) : Execution :=
  {e with request := request offset e.request}

def completion (offset : Nat) (c : Completion) : Completion :=
  {c with execution := execution offset c.execution}

def slot (offset : Nat) : Slot → Slot
  | .free => .free
  | .preparing r => .preparing (request offset r)
  | .running e => .running (execution offset e)
  | .completed c => .completed (completion offset c)

def state (offset : Nat) (s : State) : State :=
  {s with nextSequence := offset + s.nextSequence, slot := slot offset s.slot}

def command (offset : Nat) : Command → Command
  | .prepare g tx cap => .prepare g tx cap
  | .start id g => .start (identity offset id) g
  | .consumeTx id => .consumeTx (identity offset id)
  | .appendRx id bit => .appendRx (identity offset id) bit
  | .finish id outcome => .finish (identity offset id) outcome
  | .read id => .read (identity offset id)
  | .release id => .release (identity offset id)
  | .reset => .reset

def reply (offset : Nat) : Reply → Reply
  | .prepared id => .prepared (identity offset id)
  | .result c => .result (completion offset c)
  | .started => .started
  | .txBit bit => .txBit bit
  | .rxStored => .rxStored
  | .finished => .finished
  | .released => .released
  | .reset => .reset
  | .rejected reason => .rejected reason

def transition (offset : Nat) (t : Transition) : Transition :=
  ⟨state offset t.state, reply offset t.reply⟩

theorem identity_injective (offset : Nat) (a b : Identity) :
    identity offset a = identity offset b ↔ a = b := by
  cases a
  cases b
  simp [identity, Identity.mk.injEq]
  done

theorem slot_identity (offset : Nat) (s : Slot) :
    (slot offset s).identity = s.identity.map (identity offset) := by
  cases s <;> rfl
  done

theorem slot_identity_match (offset : Nat) (s : Slot) (id : Identity) :
    (slot offset s).identity = some (identity offset id) ↔ s.identity = some id := by
  cases s
  all_goals simp [slot, Slot.identity, request, execution, completion, identity_injective]
  done

theorem admittedStep_rename (capacity : Capacity) (s : State) (c : Command) (offset : Nat)
    (nonreset : c ≠ .reset) :
    admittedStep capacity (state offset s) (command offset c) =
      transition offset (admittedStep capacity s c) := by
  cases c
  case reset => exact (nonreset rfl).elim
  all_goals cases stored : s.slot
  all_goals simp [admittedStep, state, command, slot, transition, reject,
    reply, request, execution, completion, identity, Nat.add_assoc, stored]
  all_goals split <;> simp [stored]
  done

theorem command_identity (offset : Nat) (c : Command) :
    (command offset c).identity = c.identity.map (identity offset) := by
  cases c <;> rfl
  done

theorem step_rename (capacity : Capacity) (s : State) (c : Command) (offset : Nat)
    (nonreset : c ≠ .reset) :
    step capacity (state offset s) (command offset c) = transition offset (step capacity s c) := by
  have admitted := admittedStep_rename capacity s c offset nonreset
  cases hid : c.identity with
  | none => simpa only [step, command_identity, hid, Option.map_none] using admitted
  | some id =>
    simp only [step, command_identity, hid, Option.map_some]
    change (if (slot offset s.slot).identity = some (identity offset id) then _ else _) = _
    simp only [slot_identity_match]
    split
    · exact admitted
    · rfl
  done

def trace (offset : Nat) (t : Trace) : Trace :=
  ⟨state offset t.state, t.replies.map (reply offset)⟩

theorem run_rename (capacity : Capacity) (s : State) (commands : List Command) (offset : Nat)
    (nonreset : ∀ c ∈ commands, c ≠ .reset) :
    run capacity (state offset s) (commands.map (command offset)) =
      trace offset (run capacity s commands) := by
  induction commands generalizing s with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.map_cons, run]
    rw [step_rename capacity s c offset (nonreset c (by simp))]
    change (⟨(run capacity (state offset (step capacity s c).state)
      (cs.map (command offset))).state,
      reply offset (step capacity s c).reply ::
        (run capacity (state offset (step capacity s c).state) (cs.map (command offset))).replies⟩ : Trace) = _
    rw [ih _ (fun d hd => nonreset d (by simp [hd]))]
    rfl
  done

theorem reset_rebase (capacity : Capacity) (s : State) (newOffset : Nat) :
    state newOffset (step capacity s .reset).state =
      {epoch := s.epoch + 1, nextSequence := newOffset + 1, slot := .free} := by
  rfl
  done

theorem request_bounded (offset : Nat) (capacity : Capacity) (r : Request) :
    (request offset r).Bounded capacity ↔ r.Bounded capacity := Iff.rfl

theorem execution_bounded (offset : Nat) (capacity : Capacity) (e : Execution) :
    (execution offset e).Bounded capacity ↔ e.Bounded capacity := Iff.rfl

theorem slot_bounded (offset : Nat) (capacity : Capacity) (s : Slot) :
    (slot offset s).Bounded capacity ↔ s.Bounded capacity := by
  cases s <;> rfl
  done

theorem state_valid (offset : Nat) (capacity : Capacity) (s : State) :
    (state offset s).Valid capacity ↔ s.Valid capacity := by
  constructor
  · intro h
    refine ⟨(slot_bounded offset capacity s.slot).mp h.1, ?_⟩
    intro id hid
    have valid := h.2 (identity offset id) ((slot_identity_match offset s.slot id).mpr hid)
    exact ⟨valid.1, Nat.lt_of_add_lt_add_left valid.2⟩
  · intro h
    refine ⟨(slot_bounded offset capacity s.slot).mpr h.1, ?_⟩
    intro id hid
    change (slot offset s.slot).identity = some id at hid
    rw [slot_identity] at hid
    cases hs : s.slot.identity with
    | none => simp [hs] at hid
    | some original =>
      have equal : identity offset original = id := by simpa [hs] using hid
      subst id
      have valid := h.2 original hs
      exact ⟨valid.1, Nat.add_lt_add_left valid.2 offset⟩
  done

end Pinwheel.Hardware.Buffered.Lifecycle.IdentityView
