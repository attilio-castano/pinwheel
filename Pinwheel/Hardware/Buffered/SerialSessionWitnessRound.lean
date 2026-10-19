import Pinwheel.Hardware.Buffered.SerialSessionWitnessTimeout

namespace Pinwheel.Hardware.Buffered.SerialSessionWitness
open Pinwheel.Hardware Pinwheel.Program SerialWire Serial.Frames SerialSourceSession
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

theorem sourceRun_stopped (program : Program.Buffered.Program) (source : Program.Buffered.State)
    (reason : Pinwheel.Engine.Reactive.Stop) (control : source.core.control = .stopped reason)
    (pins : List SerialPackage.Pins) : SerialSourceRead.sourceRun program source pins = source := by
  induction pins
  case nil => rfl
  case cons pin rest ih =>
    change SerialSourceRead.sourceRun program
      (Program.Buffered.advance program Refinement.capacity source pin.rawInputs) rest = source
    rw [SpiInterpreter.advance_stopped program Refinement.capacity source reason control, ih]
  done

theorem retained_of_stopped {program : Program.Buffered.Program} {layout : GenericCertificate.Layout program}
    {payload actual source} (related : Refinement.RelatedSram program layout payload actual source)
    (reason : Pinwheel.Engine.Reactive.Stop) (control : source.core.control = .stopped reason) :
    actual.core .retained = 1 := by
  obtain ⟨rows, dictionary, resident, ready, relation⟩ := related
  rcases relation with ⟨e, instruction, pc, running⟩ | ⟨e, outcome, stopped⟩
  · have impossible := running.control
    rw [control] at impossible
    exact False.elim impossible
  · exact stopped.retained
  done

def releaseWord (sequence generation transfer : BitVec 16) : BitVec 160 :=
  Serial.Encoding.encode .release sequence (transfer ++ generation)

theorem release_fields (sequence generation transfer : BitVec 16) :
    (releaseWord sequence generation transfer).extractLsb' 144 4 = 4#4 ∧
    (releaseWord sequence generation transfer).extractLsb' 0 16 = generation ∧
    (releaseWord sequence generation transfer).extractLsb' 16 16 = transfer := by
  unfold releaseWord Serial.Encoding.encode
  simp (disch := decide) only [Serial.Encoding.Operation.code,
    BitVec.extractLsb'_append_eq_of_add_le, BitVec.extractLsb'_append_eq_of_le,
    BitVec.extractLsb'_setWidth_of_le, BitVec.extractLsb'_eq_self]
  simp
  done

def releaseTrace {program : Program.Buffered.Program} {layout : GenericCertificate.Layout program}
    {before : SerialPackage.State} {payload : BitVec 32} {source : Program.Buffered.State}
    (transaction : Transaction before)
    (related : Refinement.RelatedSram program layout payload before.controller source)
    (reason : Pinwheel.Engine.Reactive.Stop) (control : source.core.control = .stopped reason)
    (sequence : BitVec 16)
    (word : transaction.request.word = releaseWord sequence
      (before.controller.core .generation) (before.controller.core .transfer)) :
    Trace program before (.owned payload source) .available transaction.pins transaction.after .free .available := by
  have frame := SerialSourceRequest.frame_source before source related transaction.request.word
    transaction.request.assert transaction.request.close transaction.request.samples transaction.request.available
    transaction.request.low transaction.request.bits transaction.request.idle
  have sourceHeld := sourceRun_stopped program source reason control transaction.request.pins
  have framedRelated : Refinement.RelatedSram program layout payload transaction.framed.controller source := by
    have result := frame.2
    change Refinement.RelatedSram program layout payload transaction.framed.controller
      (SerialSourceRead.sourceRun program source transaction.request.pins) at result
    rw [sourceHeld] at result
    exact result
  have retained := retained_of_stopped framedRelated reason control
  have valid : codeOf transaction.request.word = 0#4 := by
    rw [word]
    exact Serial.Encoding.encode_accepted .release sequence _
  have fields := release_fields sequence (before.controller.core .generation) (before.controller.core .transfer)
  have opcode : transaction.request.word.extractLsb' 144 4 = 4#4 := by rw [word]; exact fields.1
  have generation : transaction.request.word.extractLsb' 0 16 = transaction.framed.controller.core .generation := by
    rw [word, fields.2.1, SerialUpload.request_generation]
  have transfer : transaction.request.word.extractLsb' 16 16 = transaction.framed.controller.core .transfer := by
    rw [word, fields.2.2, SerialUpload.request_transfer]
  have trace := Trace.cons
    (Event.release (program := program) (SerialStartAdmission.delivery transaction) payload source opcode valid retained generation transfer)
    (Trace.cons (Event.read (program := program) (SerialStartAdmission.attempt transaction) .free transaction.read.length) .nil)
  simpa only [SerialStartAdmission.delivery, SerialStartAdmission.attempt, Delivery.pins,
    Delivery.after, Attempt.pins, Attempt.after, Cursor.advance,
    Transaction.pins, Transaction.captured, Transaction.delivered, Transaction.framed,
    Transaction.after, Read.pins, Read.after, List.append_assoc, List.cons_append,
    List.nil_append] using trace
  done

noncomputable def appendTrace {program before cursor frontend first middle next nextFrontend more after final finalFrontend}
    (head : Trace program before cursor frontend first middle next nextFrontend)
    (tail : Trace program middle next nextFrontend more after final finalFrontend) :
    Trace program before cursor frontend (first ++ more) after final finalFrontend := by
  induction head
  case nil => exact tail
  case cons event rest ih =>
    simpa only [List.append_assoc] using Trace.cons event (ih tail)
  done

theorem started_transfer {before} (transaction : Transaction before)
    (starting : Reactive.starting.eval (transaction.framed.coreInputs transaction.dispatch)
      transaction.framed.controller.core = 1) :
    (transaction.after.controller.core .transfer).toNat = (before.controller.core .transfer).toNat + 1 := by
  have start : Sram.starting.eval (transaction.framed.controller.inputs
      (transaction.framed.coreInputs transaction.dispatch)) transaction.framed.controller.registers = 1 := by
    rw [Lifecycle.starting_effective, Lifecycle.starting_direct]
    exact starting
  have increment := Lifecycle.start_transfer_sequence transaction.framed.controller
    (transaction.framed.coreInputs transaction.dispatch) start
  change (transaction.delivered.controller.core .transfer).toNat =
    (transaction.framed.controller.core .transfer).toNat + 1 at increment
  have held := SerialUpload.loader_transfer_run transaction.delivered.controller
    (SerialUpload.tailCommands transaction) (by
      intro i member
      have q := SerialUpload.tail_quiet transaction i member
      exact ⟨q.1, by simp [q.2], by simp [q.2]⟩)
  rw [SerialUpload.tail_run] at held
  rw [held, increment, SerialUpload.request_transfer]
  done

theorem released_transfer {before} (transaction : Transaction before) (sequence : BitVec 16)
    (word : transaction.request.word = releaseWord sequence
      (before.controller.core .generation) (before.controller.core .transfer)) :
    transaction.after.controller.core .transfer = before.controller.core .transfer := by
  have closed := transaction.request.closed
  have valid : codeOf transaction.request.word = 0#4 := by
    rw [word]
    exact Serial.Encoding.encode_accepted .release sequence _
  have opcode : transaction.request.word.extractLsb' 144 4 = 4#4 := by
    rw [word]
    exact (release_fields sequence _ _).1
  have input := SerialSourceRelease.operands transaction.framed transaction.dispatch
    transaction.request.word closed opcode valid transaction.dispatchIdle.1
  have loader := SerialUpload.transaction_loader transaction
    ⟨input.cold, by simp [input.command], by simp [input.command]⟩
  have held := SerialUpload.loader_transfer_run before.controller (before.commands transaction.pins) loader
  rw [← before.run_controller, transaction.run_pins] at held
  exact held
  done

end Pinwheel.Hardware.Buffered.SerialSessionWitness
