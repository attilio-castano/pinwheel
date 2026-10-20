import Pinwheel.Hardware.Buffered.SerialSessionWitnessLogical
import Pinwheel.Hardware.Buffered.GenericLogicalWireSession

/-! The nonempty diagnostic witness also inhabits the carried logical/wire
trace: ordinary prepare/start, timeout, owned release and a second allocation
share one allocator rather than reconstructing unrelated transfer seeds. -/
namespace Pinwheel.Hardware.Buffered.GenericLogicalWire.Witness
open Pinwheel.Hardware Pinwheel.Program SerialWire Serial.Frames SerialSourceSession
open SerialSessionWitness (ReleaseConditions sourceRun_stopped retained_of_stopped releaseWord release_fields released_transfer started_transfer released_generation started_generation)
variable {p : Program.Buffered.Program} {layout : GenericCertificate.Layout p}
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

def localAfter {before} (start : Transaction before) (logical : Transfer.State) : Program.Buffered.State :=
  SerialSourceRead.sourceRun p
    (GenericLogicalWire.Delivery.localStarted (p := p) (SerialStartAdmission.delivery start) logical) start.read.pins

def logicalStartTrace {before} (start : Transaction before) (logical : Transfer.State) (offset : Nat)
    (opcode : start.request.word.extractLsb' 144 4 = 3#4)
    (accepted : Reactive.starting.eval (start.framed.coreInputs start.dispatch) start.framed.controller.core = 1) :
    GenericLogicalWire.Trace p before (.free logical offset) .available start.pins start.after
      (.owned (start.request.word.extractLsb' 0 32) (localAfter (p := p) start logical) offset) .available := by
  have trace := GenericLogicalWire.Trace.cons
    (GenericLogicalWire.Event.start (SerialStartAdmission.delivery start) logical offset opcode accepted)
    (GenericLogicalWire.Trace.cons
      (GenericLogicalWire.Event.read (SerialStartAdmission.attempt start)
        (.owned (start.request.word.extractLsb' 0 32)
          (GenericLogicalWire.Delivery.localStarted (p := p) (SerialStartAdmission.delivery start) logical) offset) start.read.length) .nil)
  simpa only [SerialStartAdmission.delivery, SerialStartAdmission.attempt, localAfter,
    Delivery.pins, Delivery.after, Attempt.pins, Attempt.after, GenericLogicalWire.Cursor.advance,
    Transaction.pins, Transaction.captured, Transaction.delivered, Transaction.framed,
    Transaction.after, Read.pins, Read.after, List.append_assoc, List.cons_append,
    List.nil_append] using trace
  done

theorem localAfter_epoch {before} (start : Transaction before)
    (logical : Transfer.State) (offset : Nat)
    (aligned : LogicalSession.Aligned before.controller logical offset)
    (accepted : Reactive.starting.eval (start.framed.coreInputs start.dispatch) start.framed.controller.core = 1) :
    (localAfter (p := p) start logical).buffers.epoch = logical.epoch := by
  have free := LogicalWire.aligned_quiet_run aligned (before.commands start.request.pins) start.request.quiet
  rw [← before.run_controller] at free
  have facts := SpiCircuit.starting_facts _ _ accepted
  have allocation := LogicalSession.started_allocation (p := p) free
    (start.framed.coreInputs start.dispatch) facts.txLength facts.rxCapacity
  have capture := LogicalWire.sourceRun_allocation p
    (LogicalSession.started p start.framed.controller (start.framed.coreInputs start.dispatch) logical)
    start.delivered [start.capture]
  have read := LogicalWire.sourceRun_allocation p
    (GenericLogicalWire.Delivery.localStarted (p := p) (SerialStartAdmission.delivery start) logical) start.captured start.read.pins
  exact read.1.trans (capture.1.trans allocation.1)
  done

theorem release_conditions {before payload source} (release : Transaction before)
    (related : Refinement.RelatedSram p layout payload before.controller source)
    (timeout : source.core.control = .stopped .timeout) (sequence : BitVec 16)
    (word : release.request.word = releaseWord sequence (before.controller.core .generation) (before.controller.core .transfer)) :
    ReleaseConditions release := by
  have frame := SerialSourceRequest.frame_source before source related release.request.word
    release.request.assert release.request.close release.request.samples release.request.available
    release.request.low release.request.bits release.request.idle
  have sourceHeld := sourceRun_stopped p source .timeout timeout release.request.pins
  have framedRelated : Refinement.RelatedSram p layout payload release.framed.controller source := by
    have result := frame.2
    change Refinement.RelatedSram p layout payload release.framed.controller
      (SerialSourceRead.sourceRun p source release.request.pins) at result
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
    GenericLogicalWire.Trace p before (.owned payload source offset) .available release.pins release.after
      (.free (GenericLogicalWire.Delivery.localReleased (p := p) (SerialStartAdmission.delivery release) source) offset) .available := by
  have trace := GenericLogicalWire.Trace.cons
    (GenericLogicalWire.Event.release (SerialStartAdmission.delivery release) payload source offset conditions.opcode
      conditions.valid conditions.retained conditions.generation conditions.transfer)
    (GenericLogicalWire.Trace.cons (GenericLogicalWire.Event.read (SerialStartAdmission.attempt release)
      (.free (GenericLogicalWire.Delivery.localReleased (p := p) (SerialStartAdmission.delivery release) source) offset) release.read.length) .nil)
  simpa only [SerialStartAdmission.delivery, SerialStartAdmission.attempt, Delivery.pins, Delivery.after,
    Attempt.pins, Attempt.after, GenericLogicalWire.Cursor.advance,
    Transaction.pins, Transaction.captured, Transaction.delivered, Transaction.framed,
    Transaction.after, Read.pins, Read.after, List.append_assoc, List.cons_append,
    List.nil_append] using trace
  done

theorem localReleased_epoch {before payload source offset} (release : Transaction before)
    (owned : GenericLogicalWire.Owned (p := p) (layout := layout) before.controller payload source offset) (conditions : ReleaseConditions release) :
    (GenericLogicalWire.Delivery.localReleased (p := p) (SerialStartAdmission.delivery release) source).epoch = source.buffers.epoch := by
  have framed := owned.quiet_run release.request.pins release.request.quiet
  obtain ⟨e, outcome, slot, _, _, owner⟩ := LogicalSession.local_completed framed.related conditions.retained
  have released := GenericSession.source_release (SerialSourceRead.sourceRun p source release.request.pins)
    e outcome slot owner
  have epoch := congrArg (fun transition : Transfer.Transition => transition.state.epoch) released
  change (GenericLogicalWire.Delivery.localReleased (p := p) (SerialStartAdmission.delivery release) source).epoch =
    (SerialSourceRead.sourceRun p source release.request.pins).buffers.epoch at epoch
  exact epoch.trans (LogicalWire.sourceRun_allocation p source before release.request.pins).1
  done

noncomputable def appendLogicalTrace {before cursor frontend first middle next nextFrontend more after final finalFrontend}
    (head : GenericLogicalWire.Trace p before cursor frontend first middle next nextFrontend)
    (tail : GenericLogicalWire.Trace p middle next nextFrontend more after final finalFrontend) :
    GenericLogicalWire.Trace p before cursor frontend (first ++ more) after final finalFrontend := by
  induction head
  case nil => exact tail
  case cons event rest ih => simpa only [List.append_assoc] using GenericLogicalWire.Trace.cons event (ih tail)
  done

structure LogicalRound (before : SerialPackage.State) (logical : Transfer.State) (offset : Nat) where
  start : Transaction before
  release : Transaction start.after
  finalLogical : Transfer.State
  trace : GenericLogicalWire.Trace p before (.free logical offset) .available (start.pins ++ release.pins)
    release.after (.free finalLogical offset) .available
  post : GenericLogicalWire.Valid (p := p) (layout := layout) release.after (.free finalLogical offset) .available
  epoch : finalLogical.epoch = logical.epoch
  transfer : (release.after.controller.core .transfer).toNat = (before.controller.core .transfer).toNat + 1
  generation : release.after.controller.core .generation = before.controller.core .generation

def LogicalRound.after (round : LogicalRound (p := p) (layout := layout) before logical offset) : SerialPackage.State := round.release.after
def LogicalRound.pins (round : LogicalRound (p := p) (layout := layout) before logical offset) : List SerialPackage.Pins :=
  round.start.pins ++ round.release.pins

noncomputable opaque assembleLogicalRound (before : SerialPackage.State) (logical : Transfer.State) (offset : Nat)
    (installed : Refinement.InstalledSram p layout before.controller)
    (aligned : LogicalSession.Aligned before.controller logical offset) (available : Available before.record)
    (start : Transaction before) (release : Transaction start.after)
    (accepted : Reactive.starting.eval (start.framed.coreInputs start.dispatch) start.framed.controller.core = 1)
    (opcode : start.request.word.extractLsb' 144 4 = 3#4)
    (timeout : (SerialStartAdmission.sourceAfter p start).core.control = .stopped .timeout)
    (sequence : BitVec 16)
    (word : release.request.word = releaseWord sequence
      (start.after.controller.core .generation) (start.after.controller.core .transfer)) : LogicalRound (p := p) (layout := layout) before logical offset := by
  let started := logicalStartTrace (p := p) start logical offset opcode accepted
  have post := started.preserves ⟨available, installed, aligned⟩
  have oldTrace := SerialStartAdmission.start_trace (program := p) start opcode accepted
  have oldPost := oldTrace.preserves ⟨available, installed, ⟨aligned.phase, aligned.retained⟩⟩
  have conditions := release_conditions release oldPost.2 timeout sequence word
  let released := logicalReleaseTrace (p := p) release (start.request.word.extractLsb' 0 32) (localAfter (p := p) start logical) offset conditions
  let trace := appendLogicalTrace started released
  have transfer := released_transfer release sequence word
  exact ⟨start, release, _, trace, trace.preserves ⟨available, installed, aligned⟩,
    (localReleased_epoch release post.2 conditions).trans (localAfter_epoch start logical offset aligned accepted),
    by rw [transfer]; exact started_transfer start accepted,
    (released_generation release sequence word).trans (started_generation start accepted)⟩
  done

end Pinwheel.Hardware.Buffered.GenericLogicalWire.Witness
