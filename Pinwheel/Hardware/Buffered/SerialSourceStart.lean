import Pinwheel.Hardware.Buffered.SerialSourceTransaction
import Pinwheel.Hardware.Buffered.GenericInstalledRuntime

/-! A START reaches the source through sampled wire bits and the actual
dispatch admission guard. Capture and receipt read then retain a source
snapshot while continuing every controller execution clock. -/
namespace Pinwheel.Hardware.Buffered.SerialSourceStart
open Pinwheel.Hardware Pinwheel.Program Serial.Frames

structure Operands (input : Values Reactive.Input) (word : BitVec 160) : Prop where
  command : input .command = 3
  txData : input .txData = word.extractLsb' 0 32
  txLength : input .txLength = word.extractLsb' 32 6
  rxCapacity : input .rxCapacity = word.extractLsb' 38 6
  generation : input .expectedGeneration = word.extractLsb' 44 16

theorem frame_installed {program : Program.Buffered.Program}
    {layout : GenericCertificate.Layout program}
    (s : SerialPackage.State) (installed : Refinement.InstalledSram program layout s.controller)
    (word : BitVec 160) (assert close : SerialPackage.Pins) (samples : List SerialPackage.Pins)
    (available : Available s.record) (low : Low (s.inputs assert))
    (bits : IsBits (wordBits word) ((s.step assert).frontendInputs samples))
    (idle : close.cold = false ∧ close.csn = true) :
    let framed := s.run (assert :: (samples ++ [close]))
    Closed word framed.record ∧ Refinement.InstalledSram program layout framed.controller := by
  refine ⟨s.frame_closed word assert close samples available low bits idle, ?_⟩
  rw [s.run_controller]
  apply installed.run
  intro i member
  have quiet := s.frame_quiet word assert close samples available low bits idle i member
  simp [SramExecution.ExecutingInput, SharedBranches.Runtime, quiet.1, quiet.2]

theorem operands (s : SerialPackage.State) (pin : SerialPackage.Pins)
    (word : BitVec 160) (closed : Closed word s.record)
    (opcode : word.extractLsb' 144 4 = 3#4)
    (starting : Reactive.starting.eval (s.coreInputs pin) s.controller.core = 1) :
    Operands (s.coreInputs pin) word := by
  have op3 : Serial.requestOpcode s.record = 3 := by
    have value := congrArg BitVec.toNat opcode
    simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow] at value
    change word.toNat / 2^144 % 16 = 3 at value
    simpa only [Serial.requestOpcode, closed.request] using value
  refine ⟨(SpiCircuit.starting_facts (s.coreInputs pin) s.controller.core starting).command,
    ?_, ?_, ?_, ?_⟩
  all_goals rw [s.record_coreInputs]
  all_goals simp [Serial.State.coreInput, Serial.requestField_eq, op3, closed.request]

theorem code_zero (s : SerialPackage.State) (pin : SerialPackage.Pins)
    (word : BitVec 160) (closed : Closed word s.record)
    (starting : Reactive.starting.eval (s.coreInputs pin) s.controller.core = 1) : codeOf word = 0#4 := by
  by_cases valid : codeOf word = 0#4
  · exact valid
  · have command := (SpiCircuit.starting_facts (s.coreInputs pin) s.controller.core starting).command
    rw [s.record_coreInputs] at command
    simp [Serial.State.coreInput, Serial.deliver, closed.code, valid] at command

theorem accepted_not_rejected {program : Program.Buffered.Program}
    {layout : GenericCertificate.Layout program} {actual : SramState.State}
    (installed : Refinement.InstalledSram program layout actual) (input : Values Reactive.Input)
    (starting : Reactive.starting.eval input actual.core = 1) :
    actual.observe input .rejected = 0 := by
  obtain ⟨rows, dictionary, resident, ready, image, valid⟩ := installed
  have accepted : Reactive.starting.eval input (SramExecution.reference actual rows dictionary) = 1 :=
    (SramExecution.starting_withWords input actual.core _).trans starting
  have executing := (SpiAdmission.starting_controls input actual.core starting).executing
  rw [SramExecution.observe_eq actual input rows dictionary executing.1 resident ready]
  change Reactive.rejected.eval input (SramExecution.reference actual rows dictionary) = 0
  simp [Reactive.rejected, Reactive.both, Reactive.either, Expr.eval, accepted]

theorem start_transaction {program : Program.Buffered.Program}
    {layout : GenericCertificate.Layout program}
    (s : SerialPackage.State) (installed : Refinement.InstalledSram program layout s.controller)
    (word : BitVec 160) (assert close : SerialPackage.Pins) (samples : List SerialPackage.Pins)
    (available : Available s.record) (low : Low (s.inputs assert))
    (bits : IsBits (wordBits word) ((s.step assert).frontendInputs samples))
    (idle : close.cold = false ∧ close.csn = true) (opcode : word.extractLsb' 144 4 = 3#4)
    (dispatch capture : SerialPackage.Pins)
    (dispatchIdle : dispatch.cold = false ∧ dispatch.csn = true)
    (captureIdle : capture.cold = false ∧ capture.csn = true)
    (starting : Reactive.starting.eval
      ((s.run (assert :: (samples ++ [close]))).coreInputs dispatch)
      (s.run (assert :: (samples ++ [close]))).controller.core = 1)
    (readAssert readClose : SerialPackage.Pins) (readBits : List Bool)
    (readSamples : List SerialPackage.Pins)
    (readLow : Low (((s.run (assert :: (samples ++ [close]))).step dispatch |>.step capture).inputs readAssert))
    (readWire : IsBits readBits
      ((((s.run (assert :: (samples ++ [close]))).step dispatch |>.step capture).step readAssert).frontendInputs readSamples))
    (readIdle : readClose.cold = false ∧ readClose.csn = true) (length : readBits.length = 192) :
    let framed := s.run (assert :: (samples ++ [close]))
    let input : Values Reactive.Input := framed.coreInputs dispatch
    Operands input word ∧ codeOf word = 0#4 ∧
      SerialSourceTransaction.ReadResult program layout (word.extractLsb' 0 32)
        (framed.step dispatch) (GenericStart.started program framed.controller.core input)
        word false capture readAssert readClose readSamples := by
  let framed := s.run (assert :: (samples ++ [close]))
  have frame := frame_installed s installed word assert close samples available low bits idle
  have fields := operands framed dispatch word frame.1 opcode starting
  have delivered := frame.2.start (framed.coreInputs dispatch) starting
  have deliveredWire : Refinement.RelatedSram program layout (word.extractLsb' 0 32)
      (framed.step dispatch).controller
      (GenericStart.started program framed.controller.core (framed.coreInputs dispatch)) := by
    rw [← fields.txData]
    exact delivered
  have rejection : framed.status dispatch .rejected = 0 :=
    accepted_not_rejected frame.2 (framed.coreInputs dispatch) starting
  have pending : Capturing word false (framed.step dispatch).record := by
    rw [framed.record_step]
    simpa only [show (framed.inputs dispatch).status .rejected = 0 from rejection,
      show ((0 : BitVec 1) == 1) = false from rfl, Bool.and_false] using
      frame.1.step_dispatch (framed.inputs dispatch) dispatchIdle
  exact ⟨fields, code_zero framed dispatch word frame.1 starting,
    SerialSourceRead.capture_read (framed.step dispatch) _ deliveredWire word false pending
      capture captureIdle readAssert readClose readBits readSamples readLow readWire readIdle length⟩

end Pinwheel.Hardware.Buffered.SerialSourceStart
