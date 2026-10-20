import Pinwheel.Hardware.Buffered.LogicalSession

/-! One transfer round consumes the carried ordinary logical owner state.
Rejected commands and indexed observations may be interleaved with execution. -/
namespace Pinwheel.Hardware.Buffered.LogicalSession
open Pinwheel.Hardware Pinwheel.Program Refinement

structure CommandRound where
  start : Values Reactive.Input
  body : List (Values Reactive.Input)
  release : Values Reactive.Input

def CommandRound.finished (round : CommandRound) (actual : SramState.State) : SramState.State :=
  (actual.step round.start).run round.body

def CommandRound.after (round : CommandRound) (actual : SramState.State) : SramState.State :=
  (round.finished actual).step round.release

def CommandRound.source (round : CommandRound) (p : Program.Buffered.Program)
    (actual : SramState.State) (logical : Transfer.State) : Program.Buffered.State :=
  sourceCommands p (started p actual round.start logical) round.body

def CommandRound.logicalAfter (round : CommandRound) (p : Program.Buffered.Program)
    (actual : SramState.State) (logical : Transfer.State) : Transfer.State :=
  (Transfer.step capacity (round.source p actual logical).buffers
    (.release (round.source p actual logical).owner)).state

structure RoundAdmitted (actual : SramState.State) (round : CommandRound) : Prop where
  starting : Reactive.starting.eval round.start actual.core = 1
  body : AdministrativeHistory (actual.step round.start) round.body
  observed : (round.finished actual).observe round.release .retained = 1
  cold : round.release .initialize = 0
  command : round.release .command = 4
  generation : round.release .expectedGeneration = (round.finished actual).core .generation
  transfer : round.release .expectedTransfer = (round.finished actual).core .transfer

theorem RoundAdmitted.retained {actual : SramState.State} {round : CommandRound}
    (h : RoundAdmitted actual round) : (round.finished actual).core .retained = 1 := by
  have observed := h.observed
  rw [Lifecycle.observe_effective] at observed
  exact observed

theorem start_related {p : Program.Buffered.Program} {layout : GenericCertificate.Layout p}
    {actual : SramState.State} {logical : Transfer.State} {offset : Nat}
    (installed : InstalledSram p layout actual) (aligned : Aligned actual logical offset)
    (i : Values Reactive.Input) (starting : Reactive.starting.eval i actual.core = 1) :
    RelatedSram p layout (i .txData) (actual.step i)
      (Lifecycle.IdentityView.buffered offset (started p actual i logical)) := by
  have facts := SpiCircuit.starting_facts i actual.core starting
  rw [wire_started aligned i facts.txLength facts.rxCapacity]
  exact Lifecycle.EpochView.relatedSram logical.epoch (installed.start i starting)

theorem round_related {p : Program.Buffered.Program} {layout : GenericCertificate.Layout p}
    {actual : SramState.State} {logical : Transfer.State} {offset : Nat}
    (installed : InstalledSram p layout actual) (aligned : Aligned actual logical offset)
    {round : CommandRound} (admitted : RoundAdmitted actual round) :
    RelatedSram p layout (round.start .txData) (round.finished actual)
      (Lifecycle.IdentityView.buffered offset (round.source p actual logical)) := by
  have result := (start_related installed aligned round.start admitted.starting).run_administrative
    round.body admitted.body
  rw [sourceCommands_rename] at result
  exact result

theorem local_completed {p : Program.Buffered.Program} {layout : GenericCertificate.Layout p}
    {payload : BitVec 32} {actual : SramState.State} {source : Program.Buffered.State} {offset : Nat}
    (related : RelatedSram p layout payload actual (Lifecycle.IdentityView.buffered offset source))
    (retained : actual.core .retained = 1) :
    ∃ e outcome, source.buffers.slot = .completed ⟨e, outcome⟩ ∧
      source.core.control = .stopped (stopReason outcome) ∧
      Datapath payload actual.core (Lifecycle.IdentityView.execution offset e) ∧
      e.request.identity = source.owner := by
  rcases GenericSession.completed related retained with ⟨wire, outcome, wireSlot, control, data, owner⟩
  cases stored : source.buffers.slot
  all_goals simp only [Lifecycle.IdentityView.buffered, Lifecycle.IdentityView.state,
    stored, Lifecycle.IdentityView.slot] at wireSlot
  all_goals try contradiction
  case completed completion =>
    rcases completion with ⟨e, reason⟩
    have same : Lifecycle.IdentityView.execution offset e = wire ∧ reason = outcome := by
      simpa only [Lifecycle.IdentityView.completion, Transfer.Completion.mk.injEq] using
        Transfer.Slot.completed.inj wireSlot
    rcases same with ⟨rfl, rfl⟩
    exact ⟨e, reason, rfl, control, data, (Lifecycle.IdentityView.identity_injective offset _ _).mp owner⟩

theorem local_read {p : Program.Buffered.Program} {layout : GenericCertificate.Layout p}
    {payload : BitVec 32} {actual : SramState.State} {source : Program.Buffered.State} {offset : Nat}
    (related : RelatedSram p layout payload actual (Lifecycle.IdentityView.buffered offset source))
    (retained : actual.core .retained = 1) (query : Values Reactive.Input) :
    ∃ e outcome, source.buffers.slot = .completed ⟨e, outcome⟩ ∧
      Transfer.step capacity source.buffers (.read source.owner) =
        ⟨source.buffers, .result ⟨e, outcome⟩⟩ ∧
      actual.observe query .readValid = BitVec.ofBool (decide ((query .readIndex).toNat < e.rx.length)) ∧
      actual.observe query .readBit = BitVec.ofBool (e.rx.getD (query .readIndex).toNat false) := by
  obtain ⟨e, outcome, slot, _, data, owner⟩ := local_completed related retained
  refine ⟨e, outcome, slot, ?_, datapath_read_valid data retained query, datapath_read_bit data retained query⟩
  simp [Transfer.step, Transfer.Command.identity, Transfer.Slot.identity, Transfer.admittedStep, slot, owner]

theorem started_allocation {p : Program.Buffered.Program} {actual : SramState.State}
    {logical : Transfer.State} {offset : Nat} (aligned : Aligned actual logical offset)
    (i : Values Reactive.Input) (tx : (i .txLength).toNat ≤ 32) (rx : (i .rxCapacity).toNat ≤ 32) :
    (started p actual i logical).buffers.epoch = logical.epoch ∧
      (started p actual i logical).buffers.nextSequence = logical.nextSequence + 1 := by
  have base := GenericSession.round_source_allocation
    (⟨i, fun _ => 0, 0, i⟩ : GenericSession.Round) p actual
  change (GenericStart.started p actual.core i).buffers.epoch = 0 ∧
    (GenericStart.started p actual.core i).buffers.nextSequence = (actual.core .transfer).toNat + 2 at base
  have wire := wire_started (p := p) aligned i tx rx
  have epoch := congrArg (fun s : Program.Buffered.State => s.buffers.epoch) wire
  have sequence := congrArg (fun s : Program.Buffered.State => s.buffers.nextSequence) wire
  simp only [Lifecycle.IdentityView.buffered, Lifecycle.IdentityView.state,
    Lifecycle.EpochView.buffered, Lifecycle.EpochView.state, base.1, base.2, Nat.add_zero] at epoch sequence
  exact ⟨epoch, by have := aligned.sequence; omega⟩

theorem round_allocation {p : Program.Buffered.Program} {actual : SramState.State}
    {logical : Transfer.State} {offset : Nat} (aligned : Aligned actual logical offset)
    {round : CommandRound} (admitted : RoundAdmitted actual round) :
    (round.source p actual logical).buffers.epoch = logical.epoch ∧
      (round.source p actual logical).buffers.nextSequence = logical.nextSequence + 1 := by
  have facts := SpiCircuit.starting_facts round.start actual.core admitted.starting
  have first := started_allocation (p := p) aligned round.start facts.txLength facts.rxCapacity
  have body := sourceCommands_allocation p (started p actual round.start logical) round.body
  exact ⟨body.1.trans first.1, body.2.trans first.2⟩

private theorem generation_runtime (actual : SramState.State) (i : Values Reactive.Input)
    (executing : SramExecution.ExecutingInput i) :
    (actual.step i).core .generation = actual.core .generation := by
  have committing : Sram.committing.eval (actual.inputs i) actual.registers = 0 := by
    rw [Lifecycle.committing_effective, Lifecycle.effective_runtime actual i executing.1]
    simp [Reactive.committing, Reactive.both, Reactive.cmd, Expr.eval, executing.1.2.1]
  simp [Lifecycle.generation_step, executing.2.1, executing.2.2, committing]

private theorem quiet_counters (actual : SramState.State) (i : Values Reactive.Input)
    (quiet : SpiCircuit.Quiet i) :
    (actual.step i).core .generation = actual.core .generation ∧
      (actual.step i).core .transfer = actual.core .transfer := by
  have starting : Sram.starting.eval (actual.inputs i) actual.registers = 0 := by
    rw [Lifecycle.starting_effective, Lifecycle.starting_direct]
    exact (SpiCircuit.quiet_controls i actual.core quiet).2.2.1
  refine ⟨generation_runtime actual i ?_, ?_⟩
  · simp [SramExecution.ExecutingInput, SharedBranches.Runtime, quiet.1, quiet.2]
  · simp [Lifecycle.transfer_step, quiet.1, starting]

theorem administrative_counters {p : Program.Buffered.Program} {layout : GenericCertificate.Layout p}
    {payload : BitVec 32} {actual : SramState.State} {source : Program.Buffered.State}
    (related : RelatedSram p layout payload actual source) (inputs : List (Values Reactive.Input))
    (admitted : AdministrativeHistory actual inputs) :
    (actual.run inputs).core .generation = actual.core .generation ∧
      (actual.run inputs).core .transfer = actual.core .transfer := by
  induction inputs generalizing actual source
  case nil => exact ⟨rfl, rfl⟩
  case cons i rest ih =>
    have first : (actual.step i).core .generation = actual.core .generation ∧
        (actual.step i).core .transfer = actual.core .transfer := by
      rw [related.administrative_clock i admitted.1]
      exact quiet_counters actual (Lifecycle.quiet i) (Lifecycle.quiet_input i)
    have tail := ih (related.step_administrative i admitted.1) admitted.2
    exact ⟨tail.1.trans first.1, tail.2.trans first.2⟩

theorem RoundAdmitted.releasing {actual : SramState.State} {round : CommandRound}
    (h : RoundAdmitted actual round) :
    Reactive.releasing.eval round.release (round.finished actual).core = 1 :=
  Lifecycle.release_exact round.release _ h.cold h.command h.retained h.generation h.transfer

theorem RoundAdmitted.after_scalar {actual : SramState.State} {round : CommandRound}
    (h : RoundAdmitted actual round) (register : Reactive.Register w) (scalar : Lifecycle.Scalar register) :
    (round.after actual).core register =
      Lifecycle.releaseTick (round.finished actual).core (round.release .rawInputs) register :=
  Lifecycle.release_scalar_step _ round.release h.cold h.command h.retained h.generation h.transfer
    register scalar

theorem round_counters {p : Program.Buffered.Program} {layout : GenericCertificate.Layout p}
    {actual : SramState.State} {logical : Transfer.State} {offset : Nat}
    (installed : InstalledSram p layout actual) (aligned : Aligned actual logical offset)
    {round : CommandRound} (admitted : RoundAdmitted actual round) :
    (round.after actual).core .generation = actual.core .generation ∧
      ((round.after actual).core .transfer).toNat = (actual.core .transfer).toNat + 1 := by
  have first := start_related installed aligned round.start admitted.starting
  have body := administrative_counters first round.body admitted.body
  have accepted : Sram.starting.eval (actual.inputs round.start) actual.registers = 1 := by
    rw [Lifecycle.starting_effective, Lifecycle.starting_direct]
    exact admitted.starting
  have transfer := Lifecycle.start_transfer_sequence actual round.start accepted
  have generation := generation_runtime actual round.start
    (SpiAdmission.starting_controls round.start actual.core admitted.starting).executing
  have releaseGeneration := admitted.after_scalar .generation trivial
  have releaseTransfer := admitted.after_scalar .transfer trivial
  change (round.after actual).core .generation = (round.finished actual).core .generation at releaseGeneration
  change (round.after actual).core .transfer = (round.finished actual).core .transfer at releaseTransfer
  exact ⟨releaseGeneration.trans (body.1.trans generation),
    (congrArg BitVec.toNat releaseTransfer).trans ((congrArg BitVec.toNat body.2).trans transfer)⟩

structure RoundResult (p : Program.Buffered.Program) (layout : GenericCertificate.Layout p)
    (actual : SramState.State) (logical : Transfer.State) (offset : Nat) (round : CommandRound) : Prop where
  related : RelatedSram p layout (round.start .txData) (round.finished actual)
    (Lifecycle.IdentityView.buffered offset (round.source p actual logical))
  completion : ∃ e outcome, (round.source p actual logical).buffers.slot = .completed ⟨e, outcome⟩ ∧
    (round.source p actual logical).core.control = .stopped (stopReason outcome) ∧
    Datapath (round.start .txData) (round.finished actual).core (Lifecycle.IdentityView.execution offset e) ∧
    e.request.identity = (round.source p actual logical).owner
  read : ∀ query : Values Reactive.Input, ∃ e outcome,
    (round.source p actual logical).buffers.slot = .completed ⟨e, outcome⟩ ∧
    Transfer.step capacity (round.source p actual logical).buffers (.read (round.source p actual logical).owner) =
      ⟨(round.source p actual logical).buffers, .result ⟨e, outcome⟩⟩ ∧
    (round.finished actual).observe query .readValid = BitVec.ofBool (decide ((query .readIndex).toNat < e.rx.length)) ∧
    (round.finished actual).observe query .readBit = BitVec.ofBool (e.rx.getD (query .readIndex).toNat false)
  release : Transfer.step capacity (round.source p actual logical).buffers
      (.release (round.source p actual logical).owner) =
    ⟨round.logicalAfter p actual logical, .released⟩
  installed : InstalledSram p layout (round.after actual)
  aligned : Aligned (round.after actual) (round.logicalAfter p actual logical) offset
  epoch : (round.logicalAfter p actual logical).epoch = logical.epoch
  sequence : (round.logicalAfter p actual logical).nextSequence = logical.nextSequence + 1
  generation : (round.after actual).core .generation = actual.core .generation
  transfer : ((round.after actual).core .transfer).toNat = (actual.core .transfer).toNat + 1

theorem round_result {p : Program.Buffered.Program} {layout : GenericCertificate.Layout p}
    {actual : SramState.State} {logical : Transfer.State} {offset : Nat}
    (installed : InstalledSram p layout actual) (aligned : Aligned actual logical offset)
    {round : CommandRound} (admitted : RoundAdmitted actual round) :
    RoundResult p layout actual logical offset round := by
  have related := round_related installed aligned admitted
  have completion := local_completed related admitted.retained
  have details := completion
  obtain ⟨e, outcome, slot, _, _, owner⟩ := details
  have released := GenericSession.source_release (round.source p actual logical) e outcome slot owner
  have freed : round.logicalAfter p actual logical = {(round.source p actual logical).buffers with slot := .free} :=
    congrArg Transfer.Transition.state released
  have allocation := round_allocation (p := p) aligned admitted
  have epoch : (round.logicalAfter p actual logical).epoch = logical.epoch := by rw [freed]; exact allocation.1
  have sequence : (round.logicalAfter p actual logical).nextSequence = logical.nextSequence + 1 := by
    rw [freed]
    exact allocation.2
  have counters := round_counters installed aligned admitted
  have execution : SramExecution.ExecutingInput round.release := by
    simp [SramExecution.ExecutingInput, SharedBranches.Runtime, admitted.cold, admitted.command]
  refine ⟨related, completion, fun query => local_read related admitted.retained query,
    by simpa only [freed] using released, related.installed.step round.release execution,
    ⟨by rw [freed], admitted.after_scalar .phase trivial, admitted.after_scalar .retained trivial, ?_⟩,
    epoch, sequence, counters.1, counters.2⟩
  rw [sequence, counters.2]
  have := aligned.sequence
  omega

theorem administrative_take {actual : SramState.State} {inputs : List (Values Reactive.Input)}
    (history : AdministrativeHistory actual inputs) (count : Nat) :
    AdministrativeHistory actual (inputs.take count) := by
  induction inputs generalizing actual count
  case nil => simp [AdministrativeHistory]
  case cons i rest ih =>
    cases count
    case zero => trivial
    case succ count => exact ⟨history.1, ih history.2 count⟩

theorem round_prefix_related {p : Program.Buffered.Program} {layout : GenericCertificate.Layout p}
    {actual : SramState.State} {logical : Transfer.State} {offset : Nat}
    (installed : InstalledSram p layout actual) (aligned : Aligned actual logical offset)
    {round : CommandRound} (admitted : RoundAdmitted actual round) (count : Nat) :
    RelatedSram p layout (round.start .txData) ((actual.step round.start).run (round.body.take count))
      (Lifecycle.IdentityView.buffered offset
        (sourceCommands p (started p actual round.start logical) (round.body.take count))) := by
  have result := (start_related installed aligned round.start admitted.starting).run_administrative
    (round.body.take count) (administrative_take admitted.body count)
  rw [sourceCommands_rename] at result
  exact result

def CommandRound.inputs (round : CommandRound) : List (Values Reactive.Input) :=
  @round.start :: round.body ++ [@round.release]

theorem CommandRound.after_eq_run (round : CommandRound) (actual : SramState.State) :
    round.after actual = actual.run round.inputs := by
  simp [CommandRound.after, CommandRound.finished, CommandRound.inputs, SramState.State.run,
    List.foldl_append]

end Pinwheel.Hardware.Buffered.LogicalSession
