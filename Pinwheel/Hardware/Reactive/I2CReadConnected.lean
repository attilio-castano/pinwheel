import Pinwheel.Hardware.Reactive.I2CReadFetch

/-! Baseline and retimed I²C circuits are connected to independent copies
of the same target state machine. Resolved observations determine each target's
next state. A local target law justifies a pending fetch without an assumption
relating the two runs' input histories. -/
namespace Pinwheel.Hardware.Reactive.I2CReadConnected
open Pinwheel.Hardware Pinwheel.I2C RegisterReadFetch

structure Peer (S : Type) where
  drive : S → Pins
  advance : S → Bus → S

structure Reference (S : Type) where
  core : RegisterRead.State
  target : S

structure Connected (S : Type) where
  core : Values RegisteredFetch.Register
  target : S

def Reference.clock (cfg : Config) (request : RegisterRead.Request)
    (peer : Peer S) (state : Reference S) : Reference S :=
  let bus := resolve (RegisterRead.pins request state.core.phase) (peer.drive state.target)
  ⟨RegisterRead.step cfg state.core bus, peer.advance state.target bus⟩

def Reference.schedule (cfg : Config) (request : RegisterRead.Request)
    (peer : Peer S) (state : Reference S) : Nat → List Tick
  | 0 => []
  | n+1 => .step (peer.drive state.target) :: (state.clock cfg request peer).schedule cfg request peer n

def Reference.fetchRound (peer : Peer S) (state : Reference S) : List Tick :=
  let pins := peer.drive state.target
  if state.core.phase = .fall 8 ∧ state.core.remaining = 0 then
    [.pending pins, .step pins]
  else [.step pins]

def Reference.fetchSchedule (cfg : Config) (request : RegisterRead.Request)
    (peer : Peer S) (state : Reference S) : Nat → List Tick
  | 0 => []
  | n+1 => state.fetchRound peer ++ (state.clock cfg request peer).fetchSchedule cfg request peer n

def Reference.run (cfg : Config) (request : RegisterRead.Request)
    (peer : Peer S) (state : Reference S) : Nat → Reference S
  | 0 => state
  | n+1 => (state.clock cfg request peer).run cfg request peer n

theorem Reference.run_add (cfg : Config) (request : RegisterRead.Request)
    (peer : Peer S) (state : Reference S) (a b : Nat) :
    state.run cfg request peer (a+b) = (state.run cfg request peer a).run cfg request peer b := by
  induction a generalizing state with
  | zero => simp only [Nat.zero_add, run]
  | succ a ih => rw [Nat.succ_add]; exact ih (state.clock cfg request peer)

theorem Reference.schedule_add (cfg : Config) (request : RegisterRead.Request)
    (peer : Peer S) (state : Reference S) (a b : Nat) :
    state.schedule cfg request peer (a+b) =
      state.schedule cfg request peer a ++ (state.run cfg request peer a).schedule cfg request peer b := by
  induction a generalizing state with
  | zero => simp only [Nat.zero_add, run, schedule, List.nil_append]
  | succ a ih =>
    rw [Nat.succ_add]
    exact congrArg (.step (peer.drive state.target) :: ·) (ih (state.clock cfg request peer))

theorem Reference.fetchSchedule_add (cfg : Config) (request : RegisterRead.Request)
    (peer : Peer S) (state : Reference S) (a b : Nat) :
    state.fetchSchedule cfg request peer (a+b) =
      state.fetchSchedule cfg request peer a ++ (state.run cfg request peer a).fetchSchedule cfg request peer b := by
  induction a generalizing state with
  | zero => simp only [Nat.zero_add, run, fetchSchedule, List.nil_append]
  | succ a ih =>
    rw [Nat.succ_add, fetchSchedule, fetchSchedule, List.append_assoc]
    exact congrArg (state.fetchRound peer ++ ·) (ih (state.clock cfg request peer))

theorem Reference.fetchSchedule_eq_schedule (cfg : Config) (request : RegisterRead.Request)
    (peer : Peer S) (state : Reference S) (n : Nat)
    (noCut : ∀ i < n, let atEdge := state.run cfg request peer i
      ¬ (atEdge.core.phase = .fall 8 ∧ atEdge.core.remaining = 0)) :
    state.fetchSchedule cfg request peer n = state.schedule cfg request peer n := by
  induction n generalizing state with
  | zero => rfl
  | succ n ih =>
    have head := noCut 0 (Nat.zero_lt_succ n)
    change ¬ (state.core.phase = .fall 8 ∧ state.core.remaining = 0) at head
    have tail := ih (state.clock cfg request peer) (fun i hi => noCut (i+1) (Nat.succ_lt_succ hi))
    simp [fetchSchedule, fetchRound, schedule, head, tail]

/-- If the transaction reaches the cut once, all the extra physical time is
at that dispatch and the remaining schedule comes from the same target. -/
theorem Reference.single_hold (cfg : Config) (request : RegisterRead.Request)
    (peer : Peer S) (state : Reference S) (before after : Nat)
    (cut : let atEdge := state.run cfg request peer before
      atEdge.core.phase = .fall 8 ∧ atEdge.core.remaining = 0)
    (unique : ∀ i < before+1+after, let atEdge := state.run cfg request peer i
      atEdge.core.phase = .fall 8 ∧ atEdge.core.remaining = 0 → i = before) :
    let atEdge := state.run cfg request peer before
    let pins := peer.drive atEdge.target
    let initialSteps := state.schedule cfg request peer before
    let suffix := (atEdge.clock cfg request peer).schedule cfg request peer after
    state.fetchSchedule cfg request peer (before+1+after) = initialSteps ++ .pending pins :: .step pins :: suffix ∧
      state.schedule cfg request peer (before+1+after) = initialSteps ++ .step pins :: suffix := by
  let atEdge := state.run cfg request peer before
  have head := state.fetchSchedule_eq_schedule cfg request peer before
    (fun i hi reached => Nat.ne_of_lt hi (unique i (by omega) reached))
  have tail := (atEdge.clock cfg request peer).fetchSchedule_eq_schedule cfg request peer after (by
    intro i hi
    dsimp only
    intro reached
    have same : state.run cfg request peer (before+1+i) = (atEdge.clock cfg request peer).run cfg request peer i := by
      rw [Nat.add_assoc, state.run_add, Nat.add_comm 1 i]
      rfl
    have equal := unique (before+1+i) (by omega) (by rw [same]; exact reached)
    omega)
  rw [Nat.add_assoc, Nat.add_comm 1 after, fetchSchedule_add, schedule_add, head]
  change atEdge.core.phase = .fall 8 ∧ atEdge.core.remaining = 0 at cut
  change state.schedule cfg request peer before ++ atEdge.fetchSchedule cfg request peer (after+1) = _ ∧ _
  simp [fetchRound, cut, tail, fetchSchedule, schedule]
  exact ⟨rfl, rfl⟩

/-- At the held LOW cut the first observation may update the target. If the
next drive agrees and that observation is idempotent, two physical clocks
have the same target effect as one. -/
def Peer.StableAt (peer : Peer S) (target : S) (controller : Pins) : Prop :=
  let bus := resolve controller (peer.drive target)
  let after := peer.advance target bus
  peer.drive after = peer.drive target ∧ peer.advance after bus = after

/-- The only environmental premise specific to retiming is local to the
reached dispatch cut. A concrete target invariant can discharge it. -/
def Reference.Safe (cfg : Config) (request : RegisterRead.Request)
    (peer : Peer S) (state : Reference S) : Nat → Prop
  | 0 => True
  | n+1 =>
    (state.core.phase = .fall 8 ∧ state.core.remaining = 0 →
      peer.StableAt state.target (RegisterRead.pins request state.core.phase)) ∧
    (state.clock cfg request peer).Safe cfg request peer n

theorem Reference.safe_of_run (cfg : Config) (request : RegisterRead.Request)
    (peer : Peer S) (state : Reference S) (n : Nat)
    (localLaw : ∀ i < n, let reached := state.run cfg request peer i
      reached.core.phase = .fall 8 ∧ reached.core.remaining = 0 →
        peer.StableAt reached.target (RegisterRead.pins request reached.core.phase)) :
    state.Safe cfg request peer n := by
  induction n generalizing state with
  | zero => trivial
  | succ n ih =>
    exact ⟨localLaw 0 (Nat.zero_lt_succ n), ih _ fun i hi => localLaw (i+1) (Nat.succ_lt_succ hi)⟩

def Connected.clock (peer : Peer S) (state : Connected S) : Connected S :=
  let pins := peer.drive state.target
  let bus := resolve (I2CReadFetch.drive state.core) pins
  ⟨I2CReadFetch.clock state.core pins, peer.advance state.target bus⟩

structure Execution (S : Type) where
  final : Connected S
  inputs : List Pins

/-- Retire one reference edge. A real pending fetch adds one physical edge;
both edges independently observe the target's drive at the time of the edge. -/
def Connected.round (peer : Peer S) (state : Connected S) : Execution S :=
  let pins := peer.drive state.target
  let after := state.clock peer
  match I2CReadFetch.tick state.core pins with
  | .step _ => ⟨after, [pins]⟩
  | .pending _ => ⟨after.clock peer, [pins, peer.drive after.target]⟩

def Connected.run (peer : Peer S) (state : Connected S) : Nat → Execution S
  | 0 => ⟨state, []⟩
  | n+1 =>
    let first := state.round peer
    let more := first.final.run peer n
    ⟨more.final, first.inputs ++ more.inputs⟩

structure Related (cfg : Config) (request : RegisterRead.Request)
    (reference : Reference S) (hardware : Connected S) : Prop where
  core : I2CReadFetch.Related cfg request reference.core hardware.core
  target : hardware.target = reference.target

/-- Keep every ordinary step and allow a request edge immediately before it.
The constructor records the equality of the target drives at those edges. -/
inductive Alignment : List Tick → List Tick → Prop where
  | nil : Alignment [] []
  | step (pins : Pins) : Alignment xs ys → Alignment (.step pins :: xs) (.step pins :: ys)
  | hold (pins : Pins) : Alignment xs ys → Alignment (.step pins :: xs) (.pending pins :: .step pins :: ys)

private theorem tick_drive (hardware : Values RegisteredFetch.Register) (pins : Pins) :
    (I2CReadFetch.tick hardware pins).peer = pins := by
  unfold I2CReadFetch.tick
  split <;> rfl

private theorem moving_response_zero (hardware : Values RegisteredFetch.Register) (pins : Pins)
    (moving : I2CReadFetch.tick hardware pins = .step pins) :
    I2CReadFetch.clock hardware pins .response = 0 := by
  apply RegisteredFetch.no_response
  unfold I2CReadFetch.tick at moving
  split at moving
  · contradiction
  · rename_i notWaiting
    bv_omega

private theorem target_clock (cfg : Config) (request : RegisterRead.Request) (peer : Peer S)
    (reference : Reference S) (hardware : Connected S)
    (h : Related cfg request reference hardware) :
    (hardware.clock peer).target = (reference.clock cfg request peer).target := by
  unfold Connected.clock Reference.clock
  dsimp only
  rw [h.target, I2CReadFetch.drive_eq cfg request reference.core hardware.core h.core.registers]

private theorem round_refines (cfg : Config) (request : RegisterRead.Request) (peer : Peer S)
    (reference : Reference S) (hardware : Connected S) (h : Related cfg request reference hardware)
    (safe : reference.core.phase = .fall 8 ∧ reference.core.remaining = 0 →
      peer.StableAt reference.target (RegisterRead.pins request reference.core.phase)) :
    let retired := hardware.round peer
    Related cfg request (reference.clock cfg request peer) retired.final ∧
      Alignment [.step (peer.drive reference.target)] (I2CReadFetch.schedule hardware.core retired.inputs) ∧
      @I2CReadFetch.runHardware hardware.core retired.inputs = @retired.final.core ∧
      retired.final.core .response = 0 ∧
      (hardware.core .response = 0 → I2CReadFetch.schedule hardware.core retired.inputs = reference.fetchRound peer) := by
  let pins := peer.drive hardware.target
  let first := hardware.clock peer
  have one := (I2CReadFetch.step cfg request reference.core hardware.core pins h.core).1
  have peerClock := target_clock cfg request peer reference hardware h
  have peerNow : pins = peer.drive reference.target := congrArg peer.drive h.target
  unfold Connected.round
  change (let retired := (match I2CReadFetch.tick hardware.core pins with
    | .step _ => ⟨first, [pins]⟩
    | .pending _ => ⟨first.clock peer, [pins, peer.drive first.target]⟩ : Execution S)
    Related cfg request (reference.clock cfg request peer) retired.final ∧
      Alignment [.step (peer.drive reference.target)] (I2CReadFetch.schedule hardware.core retired.inputs) ∧
      @I2CReadFetch.runHardware hardware.core retired.inputs = @retired.final.core ∧
      retired.final.core .response = 0 ∧
      (hardware.core .response = 0 → I2CReadFetch.schedule hardware.core retired.inputs = reference.fetchRound peer))
  cases marked : I2CReadFetch.tick hardware.core pins with
  | step got =>
    have own : got = pins := by
      rw [← tick_drive hardware.core pins, marked]
      rfl
    subst got
    rw [marked] at one
    change Related cfg request (reference.clock cfg request peer) first ∧
      Alignment [.step (peer.drive reference.target)] (I2CReadFetch.schedule hardware.core [pins]) ∧
      @I2CReadFetch.runHardware hardware.core [pins] = @first.core ∧
      first.core .response = 0 ∧
      (hardware.core .response = 0 → I2CReadFetch.schedule hardware.core [pins] = reference.fetchRound peer)
    refine ⟨⟨?_, peerClock⟩, ?_, rfl, moving_response_zero hardware.core pins marked, ?_⟩
    · change I2CReadFetch.Related cfg request ((Tick.step (peer.drive reference.target)).advance cfg request reference.core)
        (I2CReadFetch.clock hardware.core pins)
      rw [← peerNow]
      exact one
    · rw [← peerNow]
      simp only [I2CReadFetch.schedule, marked]
      exact .step _ .nil
    · intro empty
      have notCut : ¬ (reference.core.phase = .fall 8 ∧ reference.core.remaining = 0) := by
        intro cut
        have waiting := I2CReadFetch.wait_at_dispatch cfg request reference.core hardware.core
          h.core.registers (resolve (I2CReadFetch.drive hardware.core) pins) empty cut
        simp only [I2CReadFetch.tick, I2CReadFetch.wireInput, waiting, ↓reduceIte] at marked
        contradiction
      simp only [Reference.fetchRound, if_neg notCut, I2CReadFetch.schedule, ← peerNow, marked]
  | pending got =>
    have own : got = pins := by
      rw [← tick_drive hardware.core pins, marked]
      rfl
    subst got
    have cut := (I2CReadFetch.step cfg request reference.core hardware.core pins h.core).2 marked
    have stable := safe cut
    change peer.drive (reference.clock cfg request peer).target = peer.drive reference.target ∧
      peer.advance (reference.clock cfg request peer).target
        (resolve (RegisterRead.pins request reference.core.phase) (peer.drive reference.target)) =
        (reference.clock cfg request peer).target at stable
    have held : I2CReadFetch.Related cfg request reference.core first.core := by
      rw [marked] at one
      exact one
    have repeated : peer.drive first.target = pins := by
      change first.target = (reference.clock cfg request peer).target at peerClock
      rw [peerClock, stable.1, peerNow]
    have waiting : (RegisteredFetch.fetchWait 37).eval
        (I2CReadFetch.wireInput hardware.core pins) hardware.core = 1 := by
      unfold I2CReadFetch.tick at marked
      split at marked
      · assumption
      · contradiction
    have resume : I2CReadFetch.tick first.core (peer.drive first.target) = .step (peer.drive first.target) :=
      I2CReadFetch.resumes_next_edge hardware.core pins (peer.drive first.target) waiting
    have second := (I2CReadFetch.step cfg request reference.core first.core (peer.drive first.target) held).1
    rw [resume, repeated] at second
    change Related cfg request (reference.clock cfg request peer) (first.clock peer) ∧
      Alignment [.step (peer.drive reference.target)]
        (I2CReadFetch.schedule hardware.core [pins, peer.drive first.target]) ∧
      @I2CReadFetch.runHardware hardware.core [pins, peer.drive first.target] = @(first.clock peer).core ∧
      (first.clock peer).core .response = 0 ∧
      (hardware.core .response = 0 →
        I2CReadFetch.schedule hardware.core [pins, peer.drive first.target] = reference.fetchRound peer)
    refine ⟨⟨?_, ?_⟩, ?_, rfl, moving_response_zero first.core (peer.drive first.target) resume, ?_⟩
    · change I2CReadFetch.Related cfg request ((Tick.step (peer.drive reference.target)).advance cfg request reference.core)
        (I2CReadFetch.clock first.core (peer.drive first.target))
      rw [repeated, ← peerNow]
      exact second
    · unfold Connected.clock
      change peer.advance first.target (resolve (I2CReadFetch.drive first.core) (peer.drive first.target)) = _
      rw [repeated, peerClock, I2CReadFetch.drive_eq cfg request reference.core first.core held.registers, peerNow]
      exact stable.2
    · simp only [I2CReadFetch.schedule, marked]
      change Alignment [_] (.pending pins :: I2CReadFetch.tick first.core (peer.drive first.target) :: [])
      rw [resume, repeated, peerNow]
      exact .hold _ .nil
    · intro _
      simp only [Reference.fetchRound, if_pos cut, I2CReadFetch.schedule, marked]
      change .pending pins :: I2CReadFetch.tick first.core (peer.drive first.target) :: [] = _
      rw [resume, repeated, peerNow]

private theorem schedule_append (hardware : Values RegisteredFetch.Register) (first more : List Pins) :
    I2CReadFetch.schedule hardware (first ++ more) =
      I2CReadFetch.schedule hardware first ++ I2CReadFetch.schedule (I2CReadFetch.runHardware hardware first) more := by
  induction first generalizing hardware with
  | nil => rfl
  | cons pins first ih =>
    simp only [List.cons_append, I2CReadFetch.schedule]
    exact congrArg (I2CReadFetch.tick hardware pins :: ·) (ih (I2CReadFetch.clock hardware pins))

private theorem hardware_append (hardware : Values RegisteredFetch.Register) (first more : List Pins) :
    @I2CReadFetch.runHardware hardware (first ++ more) =
      @I2CReadFetch.runHardware (I2CReadFetch.runHardware hardware first) more :=
  List.foldl_append

private theorem Alignment.append (first : Alignment xs ys) (more : Alignment zs ws) :
    Alignment (xs ++ zs) (ys ++ ws) := by
  induction first with
  | nil => exact more
  | step pins _ ih => exact .step pins ih
  | hold pins _ ih => exact .hold pins ih

/-- Each physical edge in `inputs` is taken from the target state reached by
that execution. The result pairs those actual schedules with the independently
computed reference schedule. -/
theorem run_refines (cfg : Config) (request : RegisterRead.Request) (peer : Peer S)
    (reference : Reference S) (hardware : Connected S) (n : Nat)
    (h : Related cfg request reference hardware) (safe : reference.Safe cfg request peer n) :
    let execution := hardware.run peer n
    Related cfg request (reference.run cfg request peer n) execution.final ∧
      Alignment (reference.schedule cfg request peer n) (I2CReadFetch.schedule hardware.core execution.inputs) ∧
      @I2CReadFetch.runHardware hardware.core execution.inputs = @execution.final.core ∧
      (hardware.core .response = 0 →
        I2CReadFetch.schedule hardware.core execution.inputs = reference.fetchSchedule cfg request peer n) := by
  induction n generalizing reference hardware with
  | zero => exact ⟨h, .nil, rfl, fun _ => rfl⟩
  | succ n ih =>
    let one := hardware.round peer
    have first := round_refines cfg request peer reference hardware h safe.1
    obtain ⟨related, alignment, built, exactSchedule⟩ := ih (reference.clock cfg request peer) one.final first.1 safe.2
    refine ⟨related, ?_, ?_, ?_⟩
    · simp only [Reference.schedule, Connected.run, schedule_append, first.2.2.1]
      exact first.2.1.append alignment
    · change @I2CReadFetch.runHardware hardware.core (one.inputs ++ (one.final.run peer n).inputs) =
        @(one.final.run peer n).final.core
      rw [hardware_append, first.2.2.1]
      exact built
    · intro empty
      change I2CReadFetch.schedule hardware.core (one.inputs ++ (one.final.run peer n).inputs) =
        reference.fetchRound peer ++ (reference.clock cfg request peer).fetchSchedule cfg request peer n
      rw [schedule_append, first.2.2.1, first.2.2.2.2 empty]
      exact congrArg (reference.fetchRound peer ++ ·) (exactSchedule first.2.2.2.1)

theorem reference_schedule_run (cfg : Config) (request : RegisterRead.Request) (peer : Peer S)
    (reference : Reference S) (n : Nat) :
    RegisterReadFetch.run cfg request reference.core (reference.schedule cfg request peer n) =
      (reference.run cfg request peer n).core := by
  induction n generalizing reference with
  | zero => rfl
  | succ n ih => exact ih (reference.clock cfg request peer)

private theorem Alignment.trace (cfg : Config) (request : RegisterRead.Request)
    (alignment : Alignment xs ys) (start : RegisterRead.State) :
    let base := RegisterReadFetch.trace cfg request start xs
    let slow := RegisterReadFetch.trace cfg request start ys
    slow.filterMap Observation.capture = base.filterMap Observation.capture ∧
    wireChanges slow = wireChanges base ∧
    (∀ prev, wireChangesFrom prev (slow.map Observation.wire) = wireChangesFrom prev (base.map Observation.wire)) := by
  induction alignment generalizing start with
  | nil => exact ⟨rfl, rfl, fun _ => rfl⟩
  | step pins _ ih =>
    have tail := ih ((Tick.step pins).advance cfg request start)
    dsimp only at tail
    simp only [RegisterReadFetch.trace, List.filterMap_cons, tail.1, wireChanges, List.map_cons, tail.2.2]
    exact ⟨trivial, trivial, fun prev => by simp only [wireChangesFrom, tail.2.2]⟩
  | hold pins _ ih =>
    have tail := ih ((Tick.step pins).advance cfg request start)
    dsimp only at tail
    have holdWire : (observe request start (.pending pins)).wire = (observe request start (.step pins)).wire := rfl
    have holdCapture : (observe request start (.pending pins)).capture = none := rfl
    have holdAfter : (Tick.pending pins).advance cfg request start = start := rfl
    simp only [RegisterReadFetch.trace, holdAfter, List.filterMap_cons, holdCapture, tail.1,
      wireChanges, List.map_cons, holdWire, wireChangesFrom, ↓reduceIte, tail.2.2]
    exact ⟨trivial, trivial, fun _ => trivial⟩

/-- A reference proof of result and ordered bus/capture events carries to the
independently connected hardware. The extra physical clocks remain in its
wire trace, for checking an elapsed-time contract. -/
theorem connected_refinement (cfg : Config) (request : RegisterRead.Request) (peer : Peer S)
    (reference : Reference S) (hardware : Connected S) (n : Nat)
    (h : Related cfg request reference hardware) (safe : reference.Safe cfg request peer n) :
    let execution := hardware.run peer n
    let base := RegisterReadFetch.trace cfg request reference.core (reference.schedule cfg request peer n)
    let slow := RegisterReadFetch.trace cfg request reference.core (I2CReadFetch.schedule hardware.core execution.inputs)
    I2CReadFetch.result execution.final.core = RegisterRead.result (reference.run cfg request peer n).core ∧
      I2CReadFetch.wireTrace hardware.core execution.inputs = slow.map Observation.wire ∧
      slow.filterMap Observation.capture = base.filterMap Observation.capture ∧
      wireChanges slow = wireChanges base := by
  have run := run_refines cfg request peer reference hardware n h safe
  have wire := I2CReadFetch.run_refines cfg request reference.core hardware.core (hardware.run peer n).inputs h.core
  have events := run.2.1.trace cfg request reference.core
  exact ⟨I2CReadFetch.related_result cfg request _ _ run.1.core, wire.2.1, events.1, events.2.1⟩

structure Direct (S : Type) where
  core : Values RegisteredFetch.Base
  target : S

/-- The baseline holds the same installed program and logical state, with
    the same initial target state. The two circuits then run independently. -/
def Direct.installed (cfg : Config) (request : RegisterRead.Request) (reference : Reference S) : Direct S :=
  ⟨I2CReadFetch.baseState cfg request reference.core, reference.target⟩

def Direct.wire (peer : Peer S) (hardware : Direct S) : Wire :=
  let drive := I2CReadFetch.directDrive hardware.core
  ⟨drive, resolve drive (peer.drive hardware.target)⟩

def Direct.clock (peer : Peer S) (hardware : Direct S) : Direct S :=
  let bus := (hardware.wire peer).bus
  ⟨(Core.circuit Core.direct).step (I2CReadFetch.runtimeInput bus).values hardware.core,
    peer.advance hardware.target bus⟩

def Direct.run (peer : Peer S) (hardware : Direct S) : Nat → Direct S × List Wire
  | 0 => (hardware, [])
  | n+1 =>
    let more := (hardware.clock peer).run peer n
    (more.1, hardware.wire peer :: more.2)

private theorem Direct.installed_wire (cfg : Config) (request : RegisterRead.Request) (peer : Peer S)
    (reference : Reference S) :
    (Direct.installed cfg request reference).wire peer =
      (observe request reference.core (.step (peer.drive reference.target))).wire := by
  simp [Direct.wire, Direct.installed, I2CReadFetch.directDrive_eq, observe, Tick.peer]

private theorem Direct.installed_clock (cfg : Config) (request : RegisterRead.Request) (peer : Peer S)
    (reference : Reference S) :
    (Direct.installed cfg request reference).clock peer =
      Direct.installed cfg request (reference.clock cfg request peer) := by
  unfold Direct.clock
  rw [installed_wire]
  unfold Direct.installed Reference.clock
  exact congrArg (fun core : Values RegisteredFetch.Base => Direct.mk core _) (I2CReadFetch.baseline_step cfg request _ _)

theorem Direct.refines (cfg : Config) (request : RegisterRead.Request) (peer : Peer S)
    (reference : Reference S) (n : Nat) :
    let execution := (Direct.installed cfg request reference).run peer n
    execution.1 = Direct.installed cfg request (reference.run cfg request peer n) ∧
      execution.2 = (RegisterReadFetch.trace cfg request reference.core (reference.schedule cfg request peer n)).map
        Observation.wire := by
  induction n generalizing reference with
  | zero => exact ⟨rfl, rfl⟩
  | succ n ih =>
    simp only [Direct.run, installed_clock, Reference.run, Reference.schedule, RegisterReadFetch.trace, List.map_cons,
      installed_wire]
    exact ⟨(ih (reference.clock cfg request peer)).1, congrArg (_ :: ·) (ih (reference.clock cfg request peer)).2⟩

/-- The two independently connected circuits terminate with equal target
    states and results. Their actual physical wire traces have the same
    ordered changes, and their protocol captures agree. -/
theorem circuits_refine (cfg : Config) (request : RegisterRead.Request) (peer : Peer S)
    (reference : Reference S) (hardware : Connected S) (n : Nat)
    (h : Related cfg request reference hardware) (safe : reference.Safe cfg request peer n) :
    let direct := (Direct.installed cfg request reference).run peer n
    let retimed := hardware.run peer n
    let wires := I2CReadFetch.wireTrace hardware.core retimed.inputs
    let baseline := RegisterReadFetch.trace cfg request reference.core (reference.schedule cfg request peer n)
    let scheduled := RegisterReadFetch.trace cfg request reference.core (I2CReadFetch.schedule hardware.core retimed.inputs)
    I2CReadFetch.directResult direct.1.core = I2CReadFetch.result retimed.final.core ∧
      direct.1.target = retimed.final.target ∧
      baseline.map Observation.wire = direct.2 ∧
      scheduled.map Observation.wire = wires ∧
      scheduled.filterMap Observation.capture = baseline.filterMap Observation.capture ∧
      wireChanges scheduled = wireChanges baseline := by
  have direct := Direct.refines cfg request peer reference n
  have connected := connected_refinement cfg request peer reference hardware n h safe
  have retimed := run_refines cfg request peer reference hardware n h safe
  refine ⟨?_, ?_, direct.2.symm, connected.2.1.symm, connected.2.2.1, connected.2.2.2⟩
  · rw [direct.1]
    exact (I2CReadFetch.directResult_eq cfg request _).trans connected.1.symm
  · rw [direct.1]
    exact retimed.1.target.symm

end Pinwheel.Hardware.Reactive.I2CReadConnected
