import Pinwheel.Hardware.Buffered.SerialUploadReset
import Pinwheel.Hardware.Buffered.SerialSourceSession

/-! A converse to START guard extraction. Installed, free hardware with finite
transfer room admits bounded matching operands; actual acceptance is derived.
The wire constructor exposes the same fact after every request bit is clocked. -/
namespace Pinwheel.Hardware.Buffered.SerialStartAdmission
open Pinwheel.Hardware SerialWire Serial.Frames
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

theorem admitted (i : Values Reactive.Input) (r : Values Reactive.Register)
    (cold : i .initialize = 0) (command : i .command = 3)
    (phase : r .phase = 0) (retained : r .retained = 0) (valid : r .valid = 1)
    (generation : i .expectedGeneration = r .generation) (room : r .transfer ≠ 65535#16)
    (tx : (i .txLength).toNat ≤ 32) (rx : (i .rxCapacity).toNat ≤ 32) :
    Reactive.starting.eval i r = 1 := by
  have txNot : ¬ 32 < (i .txLength).toNat := by omega
  have rxNot : ¬ 32 < (i .rxCapacity).toNat := by omega
  simp [Reactive.starting, Reactive.free, Reactive.resetting, Reactive.cold, Reactive.warm,
    Reactive.cmd, Reactive.busy, Reactive.space, Reactive.both, Reactive.either, Expr.eval,
    cold, command, phase, retained, valid, generation, room, txNot, rxNot]
  done

def startWord (sequence generation : BitVec 16) (payload : BitVec 32)
    (tx rx : BitVec 6) : BitVec 160 :=
  Serial.Encoding.encode .start sequence (((generation ++ rx) ++ tx) ++ payload)

theorem start_fields (sequence generation : BitVec 16) (payload : BitVec 32) (tx rx : BitVec 6) :
    (startWord sequence generation payload tx rx).extractLsb' 144 3 = 3#3 ∧
    (startWord sequence generation payload tx rx).extractLsb' 44 16 = generation ∧
    (startWord sequence generation payload tx rx).extractLsb' 0 32 = payload ∧
    (startWord sequence generation payload tx rx).extractLsb' 32 6 = tx ∧
    (startWord sequence generation payload tx rx).extractLsb' 38 6 = rx := by
  unfold startWord Serial.Encoding.encode
  simp (disch := decide) only [Serial.Encoding.Operation.code,
    BitVec.extractLsb'_append_eq_of_add_le, BitVec.extractLsb'_append_eq_of_le,
    BitVec.extractLsb'_setWidth_of_le, BitVec.extractLsb'_eq_self]
  simp
  done

structure Operands (i : Values Reactive.Input) (generation : BitVec 16)
    (payload : BitVec 32) (tx rx : BitVec 6) : Prop where
  cold : i .initialize = 0
  command : i .command = 3
  generation : i .expectedGeneration = generation
  payload : i .txData = payload
  tx : i .txLength = tx
  rx : i .rxCapacity = rx

theorem operands (s : SerialPackage.State) (pin : SerialPackage.Pins)
    (sequence generation : BitVec 16) (payload : BitVec 32) (tx rx : BitVec 6)
    (closed : Closed (startWord sequence generation payload tx rx) s.record)
    (cold : pin.cold = false) : Operands (s.coreInputs pin) generation payload tx rx := by
  have opcode : Serial.requestOpcode s.record = 3 := by
    simpa [Serial.requestOpcode, closed.request, startWord, Serial.Encoding.Operation.code] using
      Serial.Encoding.encode_opcode .start sequence (((generation ++ rx) ++ tx) ++ payload)
  have accepted : codeOf (startWord sequence generation payload tx rx) = 0 :=
    Serial.Encoding.encode_accepted .start sequence (((generation ++ rx) ++ tx) ++ payload)
  constructor
  all_goals rw [s.record_coreInputs]
  all_goals simp [Serial.State.coreInput, Serial.deliver, SerialPackage.State.inputs,
    SerialPackage.Pins.inputs, cold, closed.dispatch, closed.code, accepted, opcode,
    Serial.requestField_eq, closed.request]
  case command => exact (start_fields sequence generation payload tx rx).1
  case generation => exact (start_fields sequence generation payload tx rx).2.1
  case payload => exact (start_fields sequence generation payload tx rx).2.2.1
  case tx => exact (start_fields sequence generation payload tx rx).2.2.2.1
  case rx => exact (start_fields sequence generation payload tx rx).2.2.2.2
  all_goals done

def delivery {before} (transaction : Transaction before) : SerialSourceSession.Delivery before :=
  ⟨transaction.request, transaction.dispatch, transaction.capture,
    transaction.dispatchIdle, transaction.captureIdle⟩

theorem request_free {before} (transaction : Transaction before)
    (free : SerialSourceRelease.Free before.controller) :
    SerialSourceRelease.Free transaction.framed.controller := by
  have held := SerialUpload.quiet_run_idle before.controller
    (before.commands transaction.request.pins) transaction.request.quiet free.1 free.2
  rw [← before.run_controller] at held
  exact held
  done

theorem transaction_admitted {program : Pinwheel.Program.Buffered.Program}
    {layout : GenericCertificate.Layout program} {before : SerialPackage.State}
    (transaction : Transaction before)
    (installed : Refinement.InstalledSram program layout before.controller)
    (free : SerialSourceRelease.Free before.controller)
    (sequence : BitVec 16) (payload : BitVec 32) (tx rx : BitVec 6)
    (word : transaction.request.word = startWord sequence (before.controller.core .generation) payload tx rx)
    (room : before.controller.core .transfer ≠ 65535) (txBound : tx.toNat ≤ 32) (rxBound : rx.toNat ≤ 32) :
    Reactive.starting.eval (transaction.framed.coreInputs transaction.dispatch)
      transaction.framed.controller.core = 1 := by
  have frame := SerialSourceStart.frame_installed before installed transaction.request.word
    transaction.request.assert transaction.request.close transaction.request.samples
    transaction.request.available transaction.request.low transaction.request.bits transaction.request.idle
  have closed := transaction.request.closed
  rw [word] at closed
  have input := operands transaction.framed transaction.dispatch sequence _ payload tx rx closed transaction.dispatchIdle.1
  have idle := request_free transaction free
  have generation := SerialUpload.request_generation transaction
  have transfer := SerialUpload.request_transfer transaction
  obtain ⟨rows, dictionary, resident, ready, image, valid⟩ := frame.2
  exact admitted _ _ input.cold input.command idle.1 idle.2 valid
    (input.generation.trans generation.symm) (by rw [transfer]; exact room)
    (by rw [input.tx]; exact txBound) (by rw [input.rx]; exact rxBound)
  done

theorem start_opcode (sequence generation : BitVec 16) (payload : BitVec 32) (tx rx : BitVec 6) :
    (startWord sequence generation payload tx rx).extractLsb' 144 4 = 3#4 :=
  (Serial.Encoding.encode_fields .start sequence (((generation ++ rx) ++ tx) ++ payload)).2.1

def concreteStart (before : SerialPackage.State) (available : Available before.record)
    (sequence : BitVec 16) (payload : BitVec 32) (tx rx : BitVec 6) (raw : BitVec 2 := 0) :
    Transaction before :=
  concrete before available (startWord sequence (before.controller.core .generation) payload tx rx) raw

theorem concrete_admitted {program : Pinwheel.Program.Buffered.Program}
    {layout : GenericCertificate.Layout program} (before : SerialPackage.State)
    (installed : Refinement.InstalledSram program layout before.controller)
    (free : SerialSourceRelease.Free before.controller) (available : Available before.record)
    (sequence : BitVec 16) (payload : BitVec 32) (tx rx : BitVec 6) (raw : BitVec 2)
    (room : before.controller.core .transfer ≠ 65535) (txBound : tx.toNat ≤ 32) (rxBound : rx.toNat ≤ 32) :
    let transaction := concreteStart before available sequence payload tx rx raw
    Reactive.starting.eval (transaction.framed.coreInputs transaction.dispatch)
      transaction.framed.controller.core = 1 :=
  transaction_admitted _ installed free sequence payload tx rx (concrete_word ..) room txBound rxBound

def attempt {before} (transaction : Transaction before) : SerialSourceSession.Attempt transaction.captured :=
  ⟨transaction.read.assert, transaction.read.close, transaction.read.bits,
    transaction.read.samples, transaction.ready, transaction.read.low,
    transaction.read.wire, transaction.read.idle⟩

def sourceAfter (program : Pinwheel.Program.Buffered.Program) {before} (transaction : Transaction before) :
    Pinwheel.Program.Buffered.State :=
  SerialSourceRead.sourceRun program ((delivery transaction).started program) transaction.read.pins

def start_trace {program : Pinwheel.Program.Buffered.Program} {before} (transaction : Transaction before)
    (opcode : transaction.request.word.extractLsb' 144 4 = 3#4)
    (starting : Reactive.starting.eval (transaction.framed.coreInputs transaction.dispatch)
      transaction.framed.controller.core = 1) :
    SerialSourceSession.Trace program before .free .available transaction.pins transaction.after
      (.owned (transaction.request.word.extractLsb' 0 32) (sourceAfter program transaction)) .available := by
  have trace := SerialSourceSession.Trace.cons
    (SerialSourceSession.Event.start (delivery transaction) opcode starting)
    (SerialSourceSession.Trace.cons
      (SerialSourceSession.Event.read (attempt transaction)
        (.owned (transaction.request.word.extractLsb' 0 32) ((delivery transaction).started program)) transaction.read.length)
      .nil)
  simpa only [delivery, attempt, sourceAfter, SerialSourceSession.Delivery.pins,
    SerialSourceSession.Delivery.after, SerialSourceSession.Attempt.pins,
    SerialSourceSession.Attempt.after, SerialSourceSession.Cursor.advance,
    Transaction.pins, Transaction.captured, Transaction.delivered, Transaction.framed,
    Transaction.after, Read.pins, Read.after, List.append_assoc, List.cons_append,
    List.nil_append] using trace
  done

end Pinwheel.Hardware.Buffered.SerialStartAdmission
