import Pinwheel.Hardware.Buffered.GenericInstalledRuntime
import Pinwheel.Hardware.Buffered.GenericSramSimulation
import Pinwheel.Hardware.Buffered.GenericObservation
import Pinwheel.Hardware.Buffered.LifecycleRetained

/-! Arbitrary finite reuse of one certified SRAM image. Round admission is
stated entirely through actual START, retained observation and RELEASE inputs. -/
namespace Pinwheel.Hardware.Buffered.GenericSession
open Pinwheel.Hardware Pinwheel.Program Refinement

structure Round where
  start : Values Reactive.Input
  incoming : Nat → BitVec 2
  edges : Nat
  release : Values Reactive.Input

def Round.finished (round : Round) (actual : SramState.State) : SramState.State :=
  (actual.step round.start).run (SpiStart.clocks round.incoming round.edges)

def Round.after (round : Round) (actual : SramState.State) : SramState.State :=
  (round.finished actual).step round.release

def Round.source (round : Round) (p : Program.Buffered.Program)
    (actual : SramState.State) : Program.Buffered.State :=
  Program.Buffered.run p capacity (GenericStart.started p actual.core round.start)
    round.incoming round.edges

structure Admitted (actual : SramState.State) (round : Round) : Prop where
  starting : Reactive.starting.eval round.start actual.core = 1
  observed : (round.finished actual).observe round.release .retained = 1
  cold : round.release .initialize = 0
  command : round.release .command = 4
  generation : round.release .expectedGeneration = (round.finished actual).core .generation
  transfer : round.release .expectedTransfer = (round.finished actual).core .transfer

theorem Admitted.retained {actual : SramState.State} {round : Round}
    (h : Admitted actual round) : (round.finished actual).core .retained = 1 := by
  have observed := h.observed
  rw [Lifecycle.observe_effective] at observed
  exact observed

theorem round_related {p : Program.Buffered.Program} {layout : GenericCertificate.Layout p}
    {actual : SramState.State} (installed : InstalledSram p layout actual)
    {round : Round} (admitted : Admitted actual round) :
    RelatedSram p layout (round.start .txData) (round.finished actual) (round.source p actual) :=
  (installed.start round.start admitted.starting).run round.incoming round.edges

theorem completed {p : Program.Buffered.Program} {layout : GenericCertificate.Layout p}
    {payload : BitVec 32} {actual : SramState.State} {source : Program.Buffered.State}
    (h : RelatedSram p layout payload actual source) (retained : actual.core .retained = 1) :
    ∃ e outcome, source.buffers.slot = .completed ⟨e, outcome⟩ ∧
      source.core.control = .stopped (stopReason outcome) ∧
      Datapath payload actual.core e ∧ e.request.identity = source.owner := by
  rcases h with ⟨rows, dictionary, _, _, related⟩
  rcases related.completed_of_retained retained with ⟨e, outcome, stopped⟩
  exact ⟨e, outcome, stopped.slot, stopped.control,
    stopped.common.data.actual_core, stopped.common.owner⟩

theorem source_release (source : Program.Buffered.State) (e : Transfer.Execution)
    (outcome : Transfer.Outcome) (slot : source.buffers.slot = .completed ⟨e, outcome⟩)
    (owner : e.request.identity = source.owner) :
    Transfer.step capacity source.buffers (.release source.owner) =
      ⟨{source.buffers with slot := .free}, .released⟩ := by
  simp [Transfer.step, Transfer.Command.identity, Transfer.Slot.identity,
    Transfer.admittedStep, slot, owner]

theorem Admitted.releasing {actual : SramState.State} {round : Round}
    (h : Admitted actual round) :
    Reactive.releasing.eval round.release (round.finished actual).core = 1 :=
  Lifecycle.release_exact round.release _ h.cold h.command h.retained h.generation h.transfer

theorem Admitted.after_scalar {actual : SramState.State} {round : Round}
    (h : Admitted actual round) (register : Reactive.Register w) (scalar : Lifecycle.Scalar register) :
    (round.after actual).core register =
      Lifecycle.releaseTick (round.finished actual).core (round.release .rawInputs) register :=
  Lifecycle.release_scalar_step _ round.release h.cold h.command h.retained h.generation h.transfer
    register scalar

theorem round_installed {p : Program.Buffered.Program} {layout : GenericCertificate.Layout p}
    {actual : SramState.State} (installed : InstalledSram p layout actual)
    {round : Round} (admitted : Admitted actual round) :
    InstalledSram p layout (round.after actual) := by
  have execution : SramExecution.ExecutingInput round.release := by
    simp [SramExecution.ExecutingInput, SharedBranches.Runtime, admitted.cold, admitted.command]
  exact (round_related installed admitted).installed.step round.release execution

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

private theorem clocks_counters (actual : SramState.State) (incoming : Nat → BitVec 2) (edges : Nat) :
    (actual.run (SpiStart.clocks incoming edges)).core .generation = actual.core .generation ∧
      (actual.run (SpiStart.clocks incoming edges)).core .transfer = actual.core .transfer := by
  induction edges
  case zero => exact ⟨rfl, rfl⟩
  case succ n ih =>
    have next := quiet_counters (actual.run (SpiStart.clocks incoming n))
      (SpiStart.quietInput (incoming n)) ⟨rfl, rfl⟩
    simpa only [SpiStart.clocks, SramState.State.run, List.foldl_append,
      List.foldl_cons, List.foldl_nil] using And.intro (next.1.trans ih.1) (next.2.trans ih.2)

theorem Admitted.counters {actual : SramState.State} {round : Round}
    (h : Admitted actual round) :
    (round.after actual).core .generation = actual.core .generation ∧
      ((round.after actual).core .transfer).toNat = (actual.core .transfer).toNat + 1 := by
  have starting : Sram.starting.eval (actual.inputs round.start) actual.registers = 1 := by
    rw [Lifecycle.starting_effective, Lifecycle.starting_direct]
    exact h.starting
  have first := Lifecycle.start_transfer_sequence actual round.start starting
  have generation := generation_runtime actual round.start
    (SpiAdmission.starting_controls round.start actual.core h.starting).executing
  have sampled := clocks_counters (actual.step round.start) round.incoming round.edges
  have releaseGeneration := h.after_scalar .generation trivial
  have releaseTransfer := h.after_scalar .transfer trivial
  change (round.after actual).core .generation = (round.finished actual).core .generation at releaseGeneration
  change (round.after actual).core .transfer = (round.finished actual).core .transfer at releaseTransfer
  refine ⟨releaseGeneration.trans (sampled.1.trans generation), ?_⟩
  exact (congrArg BitVec.toNat releaseTransfer).trans ((congrArg BitVec.toNat sampled.2).trans first)

theorem exhausted_rejects_start (actual : SramState.State) (i : Values Reactive.Input)
    (full : actual.core .transfer = 65535) : Reactive.starting.eval i actual.core = 0 :=
  Reactive.exhausted_transfer_rejects_start i actual.core full

structure RoundResult (p : Program.Buffered.Program) (layout : GenericCertificate.Layout p)
    (actual : SramState.State) (round : Round) : Prop where
  related : RelatedSram p layout (round.start .txData) (round.finished actual) (round.source p actual)
  completion : ∃ e outcome, (round.source p actual).buffers.slot = .completed ⟨e, outcome⟩ ∧
    (round.source p actual).core.control = .stopped (stopReason outcome) ∧
    Datapath (round.start .txData) (round.finished actual).core e ∧
    e.request.identity = (round.source p actual).owner
  sourceReleased : Transfer.step capacity (round.source p actual).buffers
      (.release (round.source p actual).owner) =
    ⟨{(round.source p actual).buffers with slot := .free}, .released⟩
  releasing : Reactive.releasing.eval round.release (round.finished actual).core = 1
  installed : InstalledSram p layout (round.after actual)
  phase : (round.after actual).core .phase = 0
  retained : (round.after actual).core .retained = 0
  generation : (round.after actual).core .generation = actual.core .generation
  transfer : ((round.after actual).core .transfer).toNat = (actual.core .transfer).toNat + 1

theorem round_result {p : Program.Buffered.Program} {layout : GenericCertificate.Layout p}
    {actual : SramState.State} (installed : InstalledSram p layout actual)
    {round : Round} (admitted : Admitted actual round) : RoundResult p layout actual round := by
  have related := round_related installed admitted
  have completion := completed related admitted.retained
  refine ⟨related, completion, ?_, admitted.releasing, round_installed installed admitted,
    admitted.after_scalar .phase trivial, admitted.after_scalar .retained trivial,
    admitted.counters.1, admitted.counters.2⟩
  rcases completion with ⟨e, outcome, slot, _, _, owner⟩
  exact source_release (round.source p actual) e outcome slot owner

def run (actual : SramState.State) (rounds : List Round) : SramState.State :=
  rounds.foldl (fun current round => round.after current) actual

inductive AdmittedTrace : SramState.State → List Round → Prop where
  | nil (actual : SramState.State) : AdmittedTrace actual []
  | cons {actual : SramState.State} {round : Round} {rest : List Round} :
      Admitted actual round → AdmittedTrace (round.after actual) rest →
      AdmittedTrace actual (round :: rest)

def Results (p : Program.Buffered.Program) (layout : GenericCertificate.Layout p)
    (actual : SramState.State) : List Round → Prop
  | [] => True
  | round :: rest => RoundResult p layout actual round ∧ Results p layout (round.after actual) rest

theorem trace_result {p : Program.Buffered.Program} {layout : GenericCertificate.Layout p}
    {actual : SramState.State} {rounds : List Round} (admitted : AdmittedTrace actual rounds)
    (installed : InstalledSram p layout actual) :
    Results p layout actual rounds ∧ InstalledSram p layout (run actual rounds) ∧
      (run actual rounds).core .generation = actual.core .generation ∧
      ((run actual rounds).core .transfer).toNat = (actual.core .transfer).toNat + rounds.length := by
  induction admitted
  case nil => exact ⟨True.intro, installed, rfl, by simp [run]⟩
  case cons accepted tail ih =>
    rename_i before round restRounds
    have head := round_result installed accepted
    have rest := ih head.installed
    refine ⟨⟨head, rest.1⟩, rest.2.1, rest.2.2.1.trans head.generation, ?_⟩
    change ((run (round.after before) restRounds).core .transfer).toNat = _
    rw [rest.2.2.2, head.transfer]
    simp only [List.length_cons]
    omega

def Round.inputs (round : Round) : List (Values Reactive.Input) :=
  @round.start :: SpiStart.clocks round.incoming round.edges ++ [@round.release]

theorem Round.after_eq_run (round : Round) (actual : SramState.State) :
    round.after actual = actual.run round.inputs := by
  simp [Round.after, Round.finished, Round.inputs, SramState.State.run,
    List.foldl_append]

theorem run_eq_inputs (actual : SramState.State) (rounds : List Round) :
    run actual rounds = actual.run (rounds.flatMap Round.inputs) := by
  induction rounds generalizing actual
  case nil => rfl
  case cons round rest ih =>
    change run (round.after actual) rest = actual.run (round.inputs ++ rest.flatMap Round.inputs)
    rw [ih, Round.after_eq_run]
    simp [SramState.State.run, List.foldl_append]

theorem trace_bound {p : Program.Buffered.Program} {layout : GenericCertificate.Layout p}
    {actual : SramState.State} {rounds : List Round} (admitted : AdmittedTrace actual rounds)
    (installed : InstalledSram p layout actual) :
    (actual.core .transfer).toNat + rounds.length ≤ 65535 := by
  have exactCount := (trace_result admitted installed).2.2.2
  have bound := ((run actual rounds).core .transfer).isLt
  omega

private def allocation (s : Program.Buffered.State) : Nat × Nat :=
  (s.buffers.epoch, s.buffers.nextSequence)

private theorem terminal_allocation (p : Program.Buffered.Program) (s : Program.Buffered.State)
    (outcome : Transfer.Outcome) : allocation (Program.Buffered.terminal p capacity s outcome) = allocation s := by
  cases slot : s.buffers.slot
  all_goals simp [allocation, Program.Buffered.terminal, Transfer.step,
    Transfer.Command.identity, Transfer.Slot.identity, Transfer.admittedStep, Transfer.reject, slot]
  all_goals split <;> simp

private theorem settle_allocation (p : Program.Buffered.Program) (s : Program.Buffered.State) :
    allocation (Program.Buffered.settle p capacity s) = allocation s := by
  cases control : s.core.control
  case stopped reason =>
    cases reason
    all_goals simp only [Program.Buffered.settle, control]
    all_goals first | exact terminal_allocation p s _ | rfl
  all_goals simp only [Program.Buffered.settle, control]

private theorem consumed_allocation (s : Program.Buffered.State) :
    allocation (Program.Buffered.consumed capacity s).1 = allocation s := by
  cases slot : s.buffers.slot
  all_goals simp [allocation, Program.Buffered.consumed, Transfer.step,
    Transfer.Command.identity, Transfer.Slot.identity, Transfer.admittedStep, Transfer.reject, slot]
  all_goals split <;> try simp
  all_goals split <;> simp

private theorem appended_allocation (s : Program.Buffered.State) (input : Fin 2) (sampled : BitVec 2) :
    allocation (Program.Buffered.appended capacity s input sampled).1 = allocation s := by
  cases slot : s.buffers.slot
  all_goals simp [allocation, Program.Buffered.appended, Transfer.step,
    Transfer.Command.identity, Transfer.Slot.identity, Transfer.admittedStep, Transfer.reject, slot]
  all_goals split <;> try simp
  all_goals split <;> simp

private theorem effects_allocation (p : Program.Buffered.Program) (s : Program.Buffered.State)
    (pc : Program.Buffered.PC) (sampled : BitVec 2) :
    allocation (Program.Buffered.entryEffects p capacity s pc sampled) = allocation s := by
  unfold Program.Buffered.entryEffects
  split
  · rfl
  · cases fetch : p.fetch pc
    case none => exact terminal_allocation p s .fault
    case some instruction =>
      cases operation : instruction.operation
      all_goals cases append : instruction.append
      all_goals simp only [operation, append]
      all_goals try rfl
      all_goals try exact terminal_allocation p s _
      all_goals try simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      all_goals split
      all_goals try simp only [terminal_allocation, consumed_allocation, appended_allocation]
      all_goals split
      all_goals simp only [terminal_allocation, consumed_allocation, appended_allocation]

private theorem advance_allocation (p : Program.Buffered.Program) (s : Program.Buffered.State)
    (raw : BitVec 2) : allocation (Program.Buffered.advance p capacity s raw) = allocation s := by
  unfold Program.Buffered.advance
  split
  · rw [settle_allocation]
    split
    · rfl
    · exact effects_allocation p _ _ _
  · rfl

theorem source_run_allocation (p : Program.Buffered.Program) (s : Program.Buffered.State)
    (incoming : Nat → BitVec 2) (edges : Nat) :
    (Program.Buffered.run p capacity s incoming edges).buffers.epoch = s.buffers.epoch ∧
      (Program.Buffered.run p capacity s incoming edges).buffers.nextSequence = s.buffers.nextSequence := by
  have preserved : allocation (Program.Buffered.run p capacity s incoming edges) = allocation s := by
    induction edges
    case zero => rfl
    case succ n ih => exact (advance_allocation p _ _).trans ih
  exact Prod.mk.inj preserved

private theorem start_allocation (p : Program.Buffered.Program) (s : Program.Buffered.State) :
    allocation (Program.Buffered.start p capacity s) = allocation s := by
  unfold Program.Buffered.start
  split
  · exact (settle_allocation p _).trans (effects_allocation p _ _ _)
  · rfl

theorem round_source_allocation (round : Round) (p : Program.Buffered.Program)
    (actual : SramState.State) :
    (round.source p actual).buffers.epoch = 0 ∧
      (round.source p actual).buffers.nextSequence = (actual.core .transfer).toNat + 2 := by
  have initial : allocation (GenericStart.started p actual.core round.start) =
      (0, (actual.core .transfer).toNat + 2) :=
    start_allocation p (GenericStart.seed p actual.core round.start)
  have execution := source_run_allocation p (GenericStart.started p actual.core round.start)
    round.incoming round.edges
  exact ⟨execution.1.trans (congrArg Prod.fst initial), execution.2.trans (congrArg Prod.snd initial)⟩

theorem round_released_state {p : Program.Buffered.Program} {layout : GenericCertificate.Layout p}
    {actual : SramState.State} (installed : InstalledSram p layout actual)
    {round : Round} (admitted : Admitted actual round) :
    (Transfer.step capacity (round.source p actual).buffers
      (.release (round.source p actual).owner)).state =
      ⟨0, ((round.after actual).core .transfer).toNat + 1, .free⟩ := by
  rw [(round_result installed admitted).sourceReleased]
  change ({epoch := (round.source p actual).buffers.epoch, nextSequence := (round.source p actual).buffers.nextSequence, slot := .free} : Transfer.State) = _
  rw [(round_source_allocation round p actual).1, (round_source_allocation round p actual).2,
    admitted.counters.2]

theorem next_seed_admitted {p : Program.Buffered.Program} {layout : GenericCertificate.Layout p}
    {actual : SramState.State} (installed : InstalledSram p layout actual)
    {round : Round} (admitted : Admitted actual round) (next : Values Reactive.Input)
    (starting : Reactive.starting.eval next (round.after actual).core = 1) :
    (Transfer.run capacity
      (Transfer.step capacity (round.source p actual).buffers
        (.release (round.source p actual).owner)).state
      [.prepare ((round.after actual).core .generation).toNat
        (SpiPacking.txBits (next .txData) (next .txLength).toNat) (next .rxCapacity).toNat,
       .start (GenericStart.request (round.after actual).core next).identity
        ((round.after actual).core .generation).toNat]).state =
      (GenericStart.seed p (round.after actual).core next).buffers := by
  rw [round_released_state installed admitted]
  have facts := SpiCircuit.starting_facts next (round.after actual).core starting
  exact GenericStart.seed_admitted p (round.after actual).core next facts.txLength facts.rxCapacity

end Pinwheel.Hardware.Buffered.GenericSession
