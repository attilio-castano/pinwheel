import Pinwheel.Hardware.Buffered.SerialSessionWitnessReuse
import Pinwheel.Hardware.Buffered.LogicalWireInitialized

/-! The nonempty diagnostic witness also inhabits the carried logical/wire
trace: ordinary prepare/start, timeout, owned release and a second allocation
share one allocator rather than reconstructing unrelated transfer seeds. -/
namespace Pinwheel.Hardware.Buffered.SerialSessionWitness
open Pinwheel.Hardware Pinwheel.Program SerialWire Serial.Frames SerialSourceSession
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

def localAfter {before} (start : Transaction before) (logical : Transfer.State) : Program.Buffered.State :=
  SerialSourceRead.sourceRun I2cSource.source
    (LogicalWire.Delivery.localStarted (SerialStartAdmission.delivery start) logical) start.read.pins

def logicalStartTrace {before} (start : Transaction before) (logical : Transfer.State) (offset : Nat)
    (opcode : start.request.word.extractLsb' 144 4 = 3#4)
    (accepted : Reactive.starting.eval (start.framed.coreInputs start.dispatch) start.framed.controller.core = 1) :
    LogicalWire.Trace before (.free logical offset) .available start.pins start.after
      (.owned (start.request.word.extractLsb' 0 32) (localAfter start logical) offset) .available := by
  have trace := LogicalWire.Trace.cons
    (LogicalWire.Event.start (SerialStartAdmission.delivery start) logical offset opcode accepted)
    (LogicalWire.Trace.cons
      (LogicalWire.Event.read (SerialStartAdmission.attempt start)
        (.owned (start.request.word.extractLsb' 0 32)
          (LogicalWire.Delivery.localStarted (SerialStartAdmission.delivery start) logical) offset) start.read.length) .nil)
  simpa only [SerialStartAdmission.delivery, SerialStartAdmission.attempt, localAfter,
    Delivery.pins, Delivery.after, Attempt.pins, Attempt.after, LogicalWire.Cursor.advance,
    Transaction.pins, Transaction.captured, Transaction.delivered, Transaction.framed,
    Transaction.after, Read.pins, Read.after, List.append_assoc, List.cons_append,
    List.nil_append] using trace
  done

theorem localAfter_epoch {before} (start : Transaction before)
    (logical : Transfer.State) (offset : Nat)
    (aligned : LogicalSession.Aligned before.controller logical offset)
    (accepted : Reactive.starting.eval (start.framed.coreInputs start.dispatch) start.framed.controller.core = 1) :
    (localAfter start logical).buffers.epoch = logical.epoch := by
  have free := LogicalWire.aligned_quiet_run aligned (before.commands start.request.pins) start.request.quiet
  rw [← before.run_controller] at free
  have facts := SpiCircuit.starting_facts _ _ accepted
  have allocation := LogicalSession.started_allocation (p := I2cSource.source) free
    (start.framed.coreInputs start.dispatch) facts.txLength facts.rxCapacity
  have capture := LogicalWire.sourceRun_allocation I2cSource.source
    (LogicalSession.started I2cSource.source start.framed.controller (start.framed.coreInputs start.dispatch) logical)
    start.delivered [start.capture]
  have read := LogicalWire.sourceRun_allocation I2cSource.source
    (LogicalWire.Delivery.localStarted (SerialStartAdmission.delivery start) logical) start.captured start.read.pins
  exact read.1.trans (capture.1.trans allocation.1)
  done

structure ReleaseConditions {before} (release : Transaction before) : Prop where
  opcode : release.request.word.extractLsb' 144 4 = 4#4
  valid : codeOf release.request.word = 0#4
  retained : release.framed.controller.core .retained = 1
  generation : release.request.word.extractLsb' 0 16 = release.framed.controller.core .generation
  transfer : release.request.word.extractLsb' 16 16 = release.framed.controller.core .transfer

theorem release_conditions {before payload source} (release : Transaction before)
    (related : Refinement.RelatedSram I2cSource.source I2cCertificate.layout payload before.controller source)
    (timeout : source.core.control = .stopped .timeout) (sequence : BitVec 16)
    (word : release.request.word = releaseWord sequence (before.controller.core .generation) (before.controller.core .transfer)) :
    ReleaseConditions release := by
  have frame := SerialSourceRequest.frame_source before source related release.request.word
    release.request.assert release.request.close release.request.samples release.request.available
    release.request.low release.request.bits release.request.idle
  have sourceHeld := sourceRun_stopped I2cSource.source source .timeout timeout release.request.pins
  have framedRelated : Refinement.RelatedSram I2cSource.source I2cCertificate.layout payload release.framed.controller source := by
    have result := frame.2
    change Refinement.RelatedSram I2cSource.source I2cCertificate.layout payload release.framed.controller
      (SerialSourceRead.sourceRun I2cSource.source source release.request.pins) at result
    rw [sourceHeld] at result
    exact result
  have fields := release_fields sequence (before.controller.core .generation) (before.controller.core .transfer)
  refine ⟨?_, ?_, retained_of_stopped framedRelated .timeout timeout, ?_, ?_⟩
  · rw [word]
    exact fields.1
  · rw [word]
    exact Serial.Encoding.encode_accepted .release sequence _
  · rw [word, fields.2.1, SerialUpload.request_generation]
  · rw [word, fields.2.2, SerialUpload.request_transfer]
  done

def logicalReleaseTrace {before} (release : Transaction before) (payload : BitVec 32)
    (source : Program.Buffered.State) (offset : Nat) (conditions : ReleaseConditions release) :
    LogicalWire.Trace before (.owned payload source offset) .available release.pins release.after
      (.free (LogicalWire.Delivery.localReleased (SerialStartAdmission.delivery release) source) offset) .available := by
  have trace := LogicalWire.Trace.cons
    (LogicalWire.Event.release (SerialStartAdmission.delivery release) payload source offset conditions.opcode
      conditions.valid conditions.retained conditions.generation conditions.transfer)
    (LogicalWire.Trace.cons (LogicalWire.Event.read (SerialStartAdmission.attempt release)
      (.free (LogicalWire.Delivery.localReleased (SerialStartAdmission.delivery release) source) offset) release.read.length) .nil)
  simpa only [SerialStartAdmission.delivery, SerialStartAdmission.attempt, Delivery.pins, Delivery.after,
    Attempt.pins, Attempt.after, LogicalWire.Cursor.advance,
    Transaction.pins, Transaction.captured, Transaction.delivered, Transaction.framed,
    Transaction.after, Read.pins, Read.after, List.append_assoc, List.cons_append,
    List.nil_append] using trace
  done

theorem localReleased_epoch {before payload source offset} (release : Transaction before)
    (owned : LogicalWire.Owned before.controller payload source offset) (conditions : ReleaseConditions release) :
    (LogicalWire.Delivery.localReleased (SerialStartAdmission.delivery release) source).epoch = source.buffers.epoch := by
  have framed := owned.quiet_run release.request.pins release.request.quiet
  obtain ⟨e, outcome, slot, _, _, owner⟩ := LogicalSession.local_completed framed.related conditions.retained
  have released := GenericSession.source_release (SerialSourceRead.sourceRun I2cSource.source source release.request.pins)
    e outcome slot owner
  have epoch := congrArg (fun transition : Transfer.Transition => transition.state.epoch) released
  change (LogicalWire.Delivery.localReleased (SerialStartAdmission.delivery release) source).epoch =
    (SerialSourceRead.sourceRun I2cSource.source source release.request.pins).buffers.epoch at epoch
  exact epoch.trans (LogicalWire.sourceRun_allocation I2cSource.source source before release.request.pins).1
  done

noncomputable def appendLogicalTrace {before cursor frontend first middle next nextFrontend more after final finalFrontend}
    (head : LogicalWire.Trace before cursor frontend first middle next nextFrontend)
    (tail : LogicalWire.Trace middle next nextFrontend more after final finalFrontend) :
    LogicalWire.Trace before cursor frontend (first ++ more) after final finalFrontend := by
  induction head
  case nil => exact tail
  case cons event rest ih => simpa only [List.append_assoc] using LogicalWire.Trace.cons event (ih tail)
  done

structure LogicalRound (before : SerialPackage.State) (logical : Transfer.State) (offset : Nat) where
  start : Transaction before
  release : Transaction start.after
  finalLogical : Transfer.State
  trace : LogicalWire.Trace before (.free logical offset) .available (start.pins ++ release.pins)
    release.after (.free finalLogical offset) .available
  post : LogicalWire.Valid release.after (.free finalLogical offset) .available
  epoch : finalLogical.epoch = logical.epoch
  transfer : (release.after.controller.core .transfer).toNat = (before.controller.core .transfer).toNat + 1
  generation : release.after.controller.core .generation = before.controller.core .generation

def LogicalRound.after (round : LogicalRound before logical offset) : SerialPackage.State := round.release.after
def LogicalRound.pins (round : LogicalRound before logical offset) : List SerialPackage.Pins :=
  round.start.pins ++ round.release.pins

noncomputable opaque assembleLogicalRound (before : SerialPackage.State) (logical : Transfer.State) (offset : Nat)
    (installed : Refinement.InstalledSram I2cSource.source I2cCertificate.layout before.controller)
    (aligned : LogicalSession.Aligned before.controller logical offset) (available : Available before.record)
    (start : Transaction before) (release : Transaction start.after)
    (accepted : Reactive.starting.eval (start.framed.coreInputs start.dispatch) start.framed.controller.core = 1)
    (opcode : start.request.word.extractLsb' 144 4 = 3#4)
    (timeout : (SerialStartAdmission.sourceAfter I2cSource.source start).core.control = .stopped .timeout)
    (sequence : BitVec 16)
    (word : release.request.word = releaseWord sequence
      (start.after.controller.core .generation) (start.after.controller.core .transfer)) : LogicalRound before logical offset := by
  let started := logicalStartTrace start logical offset opcode accepted
  have post := started.preserves ⟨available, installed, aligned⟩
  have oldTrace := SerialStartAdmission.start_trace (program := I2cSource.source) start opcode accepted
  have oldPost := oldTrace.preserves ⟨available, installed, ⟨aligned.phase, aligned.retained⟩⟩
  have conditions := release_conditions release oldPost.2 timeout sequence word
  let released := logicalReleaseTrace release (start.request.word.extractLsb' 0 32) (localAfter start logical) offset conditions
  let trace := appendLogicalTrace started released
  have transfer := released_transfer release sequence word
  exact ⟨start, release, _, trace, trace.preserves ⟨available, installed, aligned⟩,
    (localReleased_epoch release post.2 conditions).trans (localAfter_epoch start logical offset aligned accepted),
    by rw [transfer]; exact started_transfer start accepted,
    (released_generation release sequence word).trans (started_generation start accepted)⟩
  done

noncomputable opaque makeLogicalRound (before : SerialPackage.State) (logical : Transfer.State) (offset : Nat)
    (installed : Refinement.InstalledSram I2cSource.source I2cCertificate.layout before.controller)
    (aligned : LogicalSession.Aligned before.controller logical offset) (available : Available before.record)
    (room : before.controller.core .transfer ≠ 65535) (startSequence releaseSequence : BitVec 16) :
    LogicalRound before logical offset :=
  let start := roundStart before available startSequence
  let release := roundRelease start.after start.exact.1 releaseSequence
  assembleLogicalRound before logical offset installed aligned available start release
    (roundStart_admitted before installed ⟨aligned.phase, aligned.retained⟩ available room startSequence)
    (roundStart_opcode before available startSequence) (roundStart_timeout before available startSequence)
    releaseSequence (roundRelease_word start.after start.exact.1 releaseSequence)

theorem append_package_run (before middle after : SerialPackage.State)
    (first rest : List SerialPackage.Pins) (head : before.run first = middle) (tail : middle.run rest = after) :
    before.run (first ++ rest) = after := by
  change List.foldl SerialPackage.State.step before (first ++ rest) = after
  rw [List.foldl_append]
  exact (congrArg (fun state : SerialPackage.State => state.run rest) head).trans tail
  done

theorem initialized_two_logical_rounds (before : SerialPackage.State) (previous : Transfer.State)
    (pin : SerialPackage.Pins) (cold : pin.cold = true) (idle : pin.csn = true) :
    ∃ loading : SerialUpload.Loading (before.step pin),
      ∃ first : LogicalRound loading.after (LogicalSession.resetLogical previous) 0,
      ∃ second : LogicalRound first.after first.finalLogical 0,
      ∃ trace : LogicalWire.Trace loading.after (.free (LogicalSession.resetLogical previous) 0) .available
        (first.pins ++ second.pins) second.after (.free second.finalLogical 0) .available,
      before.run ((pin :: loading.pins) ++ (first.pins ++ second.pins)) = second.after ∧
      LogicalWire.Valid second.after (.free second.finalLogical 0) .available ∧
      second.finalLogical.epoch = previous.epoch + 1 ∧ second.finalLogical.nextSequence = 3 ∧
      second.after.controller.core .generation = 1 ∧ second.after.controller.core .transfer = 2 ∧ trace.Observed := by
  let loading := SerialUpload.concreteLoading (before.step pin) (SerialUpload.cold_available before pin cold idle)
  have boot := SerialUpload.cold_install before pin cold idle loading
  have initial : LogicalWire.Valid loading.after (.free (LogicalSession.resetLogical previous) 0) .available := by
    refine ⟨boot.2.2.2.2.2.1, boot.1, ⟨rfl, boot.2.1, boot.2.2.1, ?_⟩⟩
    rw [boot.2.2.2.2.1]
    rfl
  have room : loading.after.controller.core .transfer ≠ 65535 := by rw [boot.2.2.2.2.1]; decide
  let first := makeLogicalRound loading.after (LogicalSession.resetLogical previous) 0
    initial.2.1 initial.2.2 initial.1 room 67 68
  have firstTransfer : first.after.controller.core .transfer = 1 := by
    apply BitVec.eq_of_toNat_eq
    change (first.release.after.controller.core .transfer).toNat = (1#16).toNat
    rw [first.transfer, boot.2.2.2.2.1]
    rfl
  have nextRoom : first.after.controller.core .transfer ≠ 65535 := by rw [firstTransfer]; decide
  let second := makeLogicalRound first.after first.finalLogical 0
    first.post.2.1 first.post.2.2 first.post.1 nextRoom 69 70
  have secondTransfer : second.after.controller.core .transfer = 2 := by
    apply BitVec.eq_of_toNat_eq
    change (second.release.after.controller.core .transfer).toNat = (2#16).toNat
    rw [second.transfer, firstTransfer]
    rfl
  let trace : LogicalWire.Trace loading.after (.free (LogicalSession.resetLogical previous) 0) .available
      (first.pins ++ second.pins) second.after (.free second.finalLogical 0) .available :=
    appendLogicalTrace first.trace second.trace
  refine ⟨loading, first, second, trace, ?_, second.post, ?_, ?_, ?_, secondTransfer, trace.observed initial⟩
  · exact append_package_run before loading.after second.after (pin :: loading.pins)
      (first.pins ++ second.pins) boot.2.2.2.2.2.2 trace.run_pins
  · exact second.epoch.trans first.epoch
  · have allocation := second.post.2.2.sequence
    change 0 + second.finalLogical.nextSequence = (second.after.controller.core .transfer).toNat + 1 at allocation
    rw [secondTransfer] at allocation
    simpa using allocation
  · exact second.generation.trans (first.generation.trans boot.2.2.2.1)
  done

end Pinwheel.Hardware.Buffered.SerialSessionWitness
