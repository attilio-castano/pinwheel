import Pinwheel.Hardware.Buffered.LogicalSessionTrace

/-! Indexed observations at every continuous-session execution prefix.
Running storage rejects an owned read and returns no wire bit; retained
storage permits the ordinary owned read and exposes exactly its RX prefix. -/
namespace Pinwheel.Hardware.Buffered.LogicalSession
open Pinwheel.Hardware Pinwheel.Program Refinement

private theorem running_outputs (actual : SramState.State) (query : Values Reactive.Input)
    (retained : actual.core .retained = 0) :
    actual.observe query .readValid = 0 ∧ actual.observe query .readBit = 0 := by
  have valid : actual.observe query .readValid = 0 := by
    rw [Lifecycle.observe_effective]
    change actual.core .retained &&& _ = 0
    rw [retained]
    simp
  refine ⟨valid, ?_⟩
  rw [Lifecycle.observe_effective] at valid ⊢
  change Reactive.readValid.eval (Lifecycle.effectiveInputs actual query)
    (Lifecycle.effectiveState actual query) = 0 at valid
  change (if Reactive.readValid.eval (Lifecycle.effectiveInputs actual query)
    (Lifecycle.effectiveState actual query) = 1 then _ else 0) = 0
  simp only [valid, show (0 : BitVec 1) ≠ 1 from by decide, ↓reduceIte]

inductive ReadResult (actual : SramState.State) (source : Program.Buffered.State)
    (query : Values Reactive.Input) : Prop where
  | running (e : Transfer.Execution)
      (slot : source.buffers.slot = .running e)
      (read : Transfer.step capacity source.buffers (.read source.owner) =
        Transfer.reject source.buffers .wrongPhase)
      (valid : actual.observe query .readValid = 0)
      (bit : actual.observe query .readBit = 0) : ReadResult actual source query
  | completed (e : Transfer.Execution) (outcome : Transfer.Outcome)
      (slot : source.buffers.slot = .completed ⟨e, outcome⟩)
      (read : Transfer.step capacity source.buffers (.read source.owner) =
        ⟨source.buffers, .result ⟨e, outcome⟩⟩)
      (valid : actual.observe query .readValid = BitVec.ofBool (decide ((query .readIndex).toNat < e.rx.length)))
      (bit : actual.observe query .readBit = BitVec.ofBool (e.rx.getD (query .readIndex).toNat false)) :
      ReadResult actual source query

theorem read_result {p : Program.Buffered.Program} {layout : GenericCertificate.Layout p}
    {payload : BitVec 32} {actual : SramState.State} {source : Program.Buffered.State} {offset : Nat}
    (related : RelatedSram p layout payload actual (Lifecycle.IdentityView.buffered offset source))
    (query : Values Reactive.Input) : ReadResult actual source query := by
  have original := related
  rcases related with ⟨rows, dictionary, _, _, relation⟩
  rcases relation with ⟨wire, instruction, pc, running⟩ | ⟨wire, outcome, stopped⟩
  case inr =>
    have retained : actual.core .retained = 1 := stopped.retained
    obtain ⟨e, outcome, slot, read, valid, bit⟩ := local_read original retained query
    exact .completed e outcome slot read valid bit
  case inl =>
    have retained : actual.core .retained = 0 := running.retained
    have outputs := running_outputs actual query retained
    have wireSlot := running.slot
    have owner := running.common.owner
    cases stored : source.buffers.slot
    all_goals simp only [Lifecycle.IdentityView.buffered, Lifecycle.IdentityView.state,
      stored, Lifecycle.IdentityView.slot] at wireSlot
    all_goals try contradiction
    case running e =>
      have same : Lifecycle.IdentityView.execution offset e = wire := Transfer.Slot.running.inj wireSlot
      rw [← same] at owner
      have localOwner : e.request.identity = source.owner :=
        (Lifecycle.IdentityView.identity_injective offset _ _).mp owner
      refine .running e stored ?_ outputs.1 outputs.2
      simp [Transfer.step, Transfer.Command.identity, Transfer.Slot.identity,
        Transfer.admittedStep, stored, localOwner]

theorem round_prefix_read {p : Program.Buffered.Program} {layout : GenericCertificate.Layout p}
    {actual : SramState.State} {logical : Transfer.State} {offset : Nat}
    (installed : InstalledSram p layout actual) (aligned : Aligned actual logical offset)
    {round : CommandRound} (admitted : RoundAdmitted actual round) (count : Nat)
    (query : Values Reactive.Input) :
    ReadResult ((actual.step round.start).run (round.body.take count))
      (sourceCommands p (started p actual round.start logical) (round.body.take count)) query :=
  read_result (round_prefix_related installed aligned admitted count) query

end Pinwheel.Hardware.Buffered.LogicalSession
