import Pinwheel.Hardware.Buffered.SerialPackageRead
import Pinwheel.Hardware.Buffered.GenericObservation

/-! A captured serial response describes the source state immediately before
the capture edge. The controller clocks again on that edge; neither a stopped
sampler equality nor an unproved source wait-left relation is introduced. -/
namespace Pinwheel.Hardware.Buffered.SerialSourceReceipt
open Pinwheel.Hardware Pinwheel.Program

structure Fields (word : BitVec 192) (record : Serial.State)
    (status : Values Reactive.Output) : Prop where
  magic : word.extractLsb' 180 12 = 0x5A1
  code : word.extractLsb' 176 4 = Serial.responseCode.eval
    ({status := status} : Serial.Inputs).values record.values
  sequence : word.extractLsb' 160 16 = record.sequence
  rejected : word.extractLsb' 4 1 = BitVec.ofBool record.rejected
  valid : word.extractLsb' 0 1 = status .valid
  busy : word.extractLsb' 1 1 = status .busy
  retained : word.extractLsb' 2 1 = status .retained
  levels : word.extractLsb' 23 3 = status .levels
  enabled : word.extractLsb' 26 3 = status .enabled
  txConsumed : word.extractLsb' 29 6 = status .txConsumed
  rxLength : word.extractLsb' 35 6 = status .rxLength
  rxData : word.extractLsb' 41 32 = status .rxData
  generation : word.extractLsb' 75 16 = status .generation
  transfer : word.extractLsb' 91 16 = status .transfer
  phase : word.extractLsb' 128 3 = status .phase
  scratch : word.extractLsb' 139 16 = status .scratch

theorem captured_fields (record : Serial.State) (i : Serial.Inputs) :
    Fields (record.capturedResponse i) record i.status := by
  constructor
  all_goals rw [← Serial.capturedResponse_correct record i]
  all_goals simp (disch := decide) only [Serial.capturedResponse, Serial.packedStatus,
    Expr.eval, Serial.Inputs.values, Serial.State.values,
    BitVec.extractLsb'_append_eq_of_add_le, BitVec.extractLsb'_append_eq_of_le]
  all_goals simp only [Nat.reduceAdd, Nat.reduceSub, BitVec.extractLsb'_eq_self]
  all_goals rfl

structure TransferFields (word : BitVec 192) (source : Program.Buffered.State)
    (e : Transfer.Execution) : Prop where
  bounded : e.Bounded Refinement.capacity
  owner : e.request.identity = source.owner
  slot : source.buffers.slot = .running e ∨
    ∃ outcome, source.buffers.slot = .completed ⟨e, outcome⟩
  txConsumed : (word.extractLsb' 29 6).toNat = e.txConsumed
  rxLength : (word.extractLsb' 35 6).toNat = e.rx.length
  rxData : word.extractLsb' 41 32 = SpiPacking.rxWord e.rx
  generation : (word.extractLsb' 75 16).toNat = e.request.programGeneration
  transfer : (word.extractLsb' 91 16).toNat = e.request.identity.sequence

structure Meaning (word : BitVec 192) (record : Serial.State)
    (source : Program.Buffered.State) : Prop where
  magic : word.extractLsb' 180 12 = 0x5A1
  code : (word.extractLsb' 176 4).toNat =
    if record.code == 0 && record.rejected then 4 else record.code.toNat
  sequence : word.extractLsb' 160 16 = record.sequence
  rejected : word.extractLsb' 4 1 = BitVec.ofBool record.rejected
  valid : word.extractLsb' 0 1 = 1
  busy : word.extractLsb' 1 1 = BitVec.ofBool (Engine.Reactive.busy source.core)
  retained : word.extractLsb' 2 1 = BitVec.ofBool (Refinement.slotRetained source.buffers.slot)
  levels : word.extractLsb' 23 3 = source.core.pins.levels
  enabled : word.extractLsb' 26 3 = source.core.pins.enabled
  phase : word.extractLsb' 128 3 = Refinement.controlPhase source.core.control
  scratch : GenericPhase.Scratch (word.extractLsb' 139 16) source.core.samples
  data : ∃ e, TransferFields word source e

private theorem status_valid (s : SerialPackage.State) (p : SerialPackage.Pins) :
    s.status p .valid = s.controller.registers (.core .valid) := by
  rfl

private theorem status_busy (s : SerialPackage.State) (p : SerialPackage.Pins) :
    s.status p .busy = Reactive.busy.eval (s.coreInputs p)
      (SramExecution.core s.controller.registers) := by
  rfl

theorem fields_meaning {program : Program.Buffered.Program}
    {layout : GenericCertificate.Layout program} {payload : BitVec 32}
    {s : SerialPackage.State} {source : Program.Buffered.State}
    (related : Refinement.RelatedSram program layout payload s.controller source)
    (p : SerialPackage.Pins) (word : BitVec 192) (record : Serial.State)
    (fields : Fields word record (s.status p)) : Meaning word record source := by
  obtain ⟨e, data, owner, slot⟩ := related.datapath
  refine ⟨fields.magic, ?_, fields.sequence, fields.rejected, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ⟨e, data.bounded, owner, slot, ?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [fields.code]
    exact Serial.responseCode_toNat record {status := s.status p}
  · rw [fields.valid, status_valid]
    exact related.valid
  · rw [fields.busy, status_busy]
    exact related.busy (s.coreInputs p)
  · rw [fields.retained]
    change s.controller.registers (.core .retained) = _
    exact related.retained
  · rw [fields.levels]
    change s.controller.registers (.core .levels) = _
    exact (congrArg Engine.Reactive.Pins.levels related.pins).symm
  · rw [fields.enabled]
    change s.controller.registers (.core .enabled) = _
    exact (congrArg Engine.Reactive.Pins.enabled related.pins).symm
  · rw [fields.phase]
    change s.controller.registers (.core .phase) = _
    exact related.phase
  · rw [fields.scratch]
    exact related.scratch
  · rw [fields.txConsumed]
    exact data.consumed
  · rw [fields.rxLength]
    exact data.rxLength
  · rw [fields.rxData]
    exact data.received
  · rw [fields.generation]
    exact data.generation
  · rw [fields.transfer]
    exact data.transfer

theorem capture_source {program : Program.Buffered.Program}
    {layout : GenericCertificate.Layout program} {payload : BitVec 32}
    (s : SerialPackage.State) (source : Program.Buffered.State)
    (related : Refinement.RelatedSram program layout payload s.controller source)
    (p : SerialPackage.Pins) (cold : p.cold = false) (capture : s.record.capture = true) :
    Meaning (s.step p).record.response s.record source ∧
      (s.step p).record.ready = true ∧
      (s.step p).controller = s.controller.step (s.coreInputs p) := by
  have actual := s.capture_response p cold capture
  have fields := captured_fields s.record (s.inputs p)
  rw [← actual.1] at fields
  exact ⟨fields_meaning related p _ _ fields, actual.2⟩

end Pinwheel.Hardware.Buffered.SerialSourceReceipt
