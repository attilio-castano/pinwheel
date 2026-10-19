import Pinwheel.Hardware.Buffered.SerialSourceStart
import Pinwheel.Hardware.Buffered.LifecycleRetained
import Pinwheel.Hardware.Buffered.LifecycleUpload

/-! A sampled matching RELEASE frees the owned source transfer and restores
the installed controller for another START. Its held wire receipt reports the
post-release phase, with all subsequent capture/read clocks still present. -/
namespace Pinwheel.Hardware.Buffered.SerialSourceRelease
open Pinwheel.Hardware Pinwheel.Program Serial.Frames

def Free (actual : SramState.State) : Prop := actual.core .phase = 0 ∧ actual.core .retained = 0

theorem free_step {actual : SramState.State} (free : Free actual)
    (input : Values Reactive.Input) (quiet : SpiCircuit.Quiet input) : Free (actual.step input) :=
  LifecycleUpload.idle_step actual input
    ⟨quiet.1, by simp [quiet.2], by simp [quiet.2]⟩ free.1 free.2

theorem free_run (actual : SramState.State) (inputs : List (Values Reactive.Input))
    (free : Free actual) (quiet : ∀ i ∈ inputs, SpiCircuit.Quiet i) : Free (actual.run inputs) := by
  induction inputs generalizing actual with
  | nil => exact free
  | cons input rest ih =>
    exact ih (actual.step input) (free_step free input (quiet input (by simp)))
      (fun i member => quiet i (List.mem_cons.mpr (Or.inr member)))

theorem quiet_run {program : Program.Buffered.Program} {layout : GenericCertificate.Layout program}
    (s : SerialPackage.State) (installed : Refinement.InstalledSram program layout s.controller)
    (free : Free s.controller) (pins : List SerialPackage.Pins)
    (quiet : ∀ i ∈ s.commands pins, SpiCircuit.Quiet i) :
    Refinement.InstalledSram program layout (s.run pins).controller ∧ Free (s.run pins).controller := by
  rw [s.run_controller]
  exact ⟨installed.run (s.commands pins) (fun input member => by
      have h := quiet input member
      simp [SramExecution.ExecutingInput, SharedBranches.Runtime, h.1, h.2]),
    free_run s.controller (s.commands pins) free quiet⟩

structure Operands (input : Values Reactive.Input) (word : BitVec 160) : Prop where
  cold : input .initialize = 0
  command : input .command = 4
  generation : input .expectedGeneration = word.extractLsb' 0 16
  transfer : input .expectedTransfer = word.extractLsb' 16 16

theorem operands (s : SerialPackage.State) (pin : SerialPackage.Pins)
    (word : BitVec 160) (closed : Closed word s.record)
    (opcode : word.extractLsb' 144 4 = 4#4) (valid : codeOf word = 0#4)
    (cold : pin.cold = false) : Operands (s.coreInputs pin) word := by
  have value := congrArg BitVec.toNat opcode
  simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow] at value
  change word.toNat / 2^144 % 16 = 4 at value
  have op4 : Serial.requestOpcode s.record = 4 := by
    simpa only [Serial.requestOpcode, closed.request] using value
  have lowOpcode : word.extractLsb' 144 3 = 4#3 := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
    change word.toNat / 2^144 % 8 = 4
    omega
  constructor
  all_goals rw [s.record_coreInputs]
  all_goals simp [Serial.State.coreInput, Serial.deliver, SerialPackage.State.inputs,
    SerialPackage.Pins.inputs, cold, closed.dispatch, closed.code, valid, op4,
    Serial.requestField_eq, closed.request, lowOpcode]

theorem source_release {program : Program.Buffered.Program}
    {layout : GenericCertificate.Layout program} {payload : BitVec 32}
    {actual : SramState.State} {source : Program.Buffered.State}
    (related : Refinement.RelatedSram program layout payload actual source)
    (retained : actual.core .retained = 1) :
    ∃ e outcome, source.buffers.slot = .completed ⟨e, outcome⟩ ∧
      e.request.identity = source.owner ∧
      Transfer.step Refinement.capacity source.buffers (.release source.owner) =
        ⟨{source.buffers with slot := .free}, .released⟩ := by
  obtain ⟨e, data, owner, slot⟩ := related.datapath
  rcases slot with running | ⟨outcome, complete⟩
  · have stored := related.retained
    simp only [running, Refinement.slotRetained, BitVec.ofBool_false] at stored
    have impossible : (1 : BitVec 1) = 0 := retained.symm.trans stored
    contradiction
  · refine ⟨e, outcome, complete, owner, ?_⟩
    simp [Transfer.step, Transfer.Command.identity, Transfer.Slot.identity,
      Transfer.admittedStep, complete, owner]

theorem accepted_not_rejected {program : Program.Buffered.Program}
    {layout : GenericCertificate.Layout program} {actual : SramState.State}
    (installed : Refinement.InstalledSram program layout actual) (input : Values Reactive.Input)
    (fields : Operands input word) (retained : actual.core .retained = 1)
    (generation : input .expectedGeneration = actual.core .generation)
    (transfer : input .expectedTransfer = actual.core .transfer) :
    actual.observe input .rejected = 0 := by
  obtain ⟨rows, dictionary, resident, ready, image, valid⟩ := installed
  have executing : SramExecution.ExecutingInput input := by
    simp [SramExecution.ExecutingInput, SharedBranches.Runtime, fields.cold, fields.command]
  have release : Reactive.releasing.eval input (SramExecution.reference actual rows dictionary) = 1 :=
    Lifecycle.release_exact input _ fields.cold fields.command retained generation transfer
  rw [SramExecution.observe_eq actual input rows dictionary executing.1 resident ready]
  change Reactive.rejected.eval input (SramExecution.reference actual rows dictionary) = 0
  simp [Reactive.rejected, Reactive.both, Reactive.either, Expr.eval, release]

structure Receipt (response : BitVec 192) (word : BitVec 160) : Prop where
  magic : response.extractLsb' 180 12 = 0x5A1
  code : response.extractLsb' 176 4 = 0
  sequence : response.extractLsb' 160 16 = word.extractLsb' 128 16
  rejected : response.extractLsb' 4 1 = 0
  valid : response.extractLsb' 0 1 = 1
  busy : response.extractLsb' 1 1 = 0
  retained : response.extractLsb' 2 1 = 0
  phase : response.extractLsb' 128 3 = 0

def ReadResult (program : Program.Buffered.Program) (layout : GenericCertificate.Layout program)
    (s : SerialPackage.State) (word : BitVec 160) (capture assert close : SerialPackage.Pins)
    (samples : List SerialPackage.Pins) : Prop :=
  let receipt := (s.step capture).record.response
  let read := assert :: (samples ++ [close])
  Receipt receipt word ∧
    Refinement.InstalledSram program layout ((s.step capture).run read).controller ∧
    Free ((s.step capture).run read).controller ∧
    Available ((s.step capture).run read).record ∧
    ((s.step capture).run read).record.response = receipt ∧
    (s.step capture).readObserved read =
      (List.range 192).map (fun k => receipt.getLsbD (191-k))

theorem capture_read {program : Program.Buffered.Program} {layout : GenericCertificate.Layout program}
    (s : SerialPackage.State) (installed : Refinement.InstalledSram program layout s.controller)
    (free : Free s.controller) (word : BitVec 160) (valid : codeOf word = 0#4)
    (capturing : Capturing word false s.record)
    (capture : SerialPackage.Pins) (captureIdle : capture.cold = false ∧ capture.csn = true)
    (assert close : SerialPackage.Pins) (bits : List Bool) (samples : List SerialPackage.Pins)
    (low : Low ((s.step capture).inputs assert))
    (wire : IsBits bits (((s.step capture).step assert).frontendInputs samples))
    (idle : close.cold = false ∧ close.csn = true) (length : bits.length = 192) :
    ReadResult program layout s word capture assert close samples := by
  have captured := s.capture_response capture captureIdle.1 capturing.capture
  have fields := SerialSourceReceipt.captured_fields s.record (s.inputs capture)
  rw [← captured.1] at fields
  have ready : ReceiptReady (s.step capture).record := by
    rw [s.record_step]
    exact (capturing.step_capture (s.inputs capture) captureIdle).1
  have read := (s.step capture).receipt_exact_read assert close bits samples ready low wire idle length
  have quiet := SerialSourceRead.core_quiet s capture captureIdle.1 capturing.dispatch
  have captureInstalled := installed.step (s.coreInputs capture)
    (by simp [SramExecution.ExecutingInput, SharedBranches.Runtime, quiet.1, quiet.2])
  have captureFree := free_step free (s.coreInputs capture) quiet
  have suffix := quiet_run (s.step capture) captureInstalled captureFree (assert :: (samples ++ [close]))
    ((s.step capture).receipt_read_quiet assert close bits samples ready low wire idle)
  refine ⟨?_, suffix.1, suffix.2, read.1, read.2.1, read.2.2⟩
  refine ⟨fields.magic, ?_, fields.sequence.trans capturing.sequence, ?_, ?_, ?_, ?_, ?_⟩
  · rw [fields.code]
    simp [Serial.responseCode, Serial.both, Expr.eval, Serial.State.values,
      capturing.code, capturing.rejected, valid]
  · rw [fields.rejected, capturing.rejected]
    rfl
  · rw [fields.valid]
    change s.controller.core .valid = 1
    rcases installed with ⟨_, _, _, _, _, valid⟩
    exact valid
  · rw [fields.busy]
    change Reactive.busy.eval (s.coreInputs capture) s.controller.core = 0
    simp [Reactive.busy, Reactive.both, Expr.eval, free.1]
  · rw [fields.retained]
    exact free.2
  · rw [fields.phase]
    exact free.1

theorem release_transaction {program : Program.Buffered.Program}
    {layout : GenericCertificate.Layout program} {payload : BitVec 32}
    (s : SerialPackage.State) (source : Program.Buffered.State)
    (related : Refinement.RelatedSram program layout payload s.controller source)
    (word : BitVec 160) (assert close : SerialPackage.Pins) (samples : List SerialPackage.Pins)
    (available : Available s.record) (low : Low (s.inputs assert))
    (bits : IsBits (wordBits word) ((s.step assert).frontendInputs samples))
    (idle : close.cold = false ∧ close.csn = true)
    (opcode : word.extractLsb' 144 4 = 4#4) (valid : codeOf word = 0#4)
    (dispatch capture : SerialPackage.Pins)
    (dispatchIdle : dispatch.cold = false ∧ dispatch.csn = true)
    (captureIdle : capture.cold = false ∧ capture.csn = true)
    (retained : (s.run (assert :: (samples ++ [close]))).controller.core .retained = 1)
    (generation : word.extractLsb' 0 16 =
      (s.run (assert :: (samples ++ [close]))).controller.core .generation)
    (transfer : word.extractLsb' 16 16 =
      (s.run (assert :: (samples ++ [close]))).controller.core .transfer)
    (readAssert readClose : SerialPackage.Pins) (readBits : List Bool)
    (readSamples : List SerialPackage.Pins)
    (readLow : Low (((s.run (assert :: (samples ++ [close]))).step dispatch |>.step capture).inputs readAssert))
    (readWire : IsBits readBits
      ((((s.run (assert :: (samples ++ [close]))).step dispatch |>.step capture).step readAssert).frontendInputs readSamples))
    (readIdle : readClose.cold = false ∧ readClose.csn = true) (length : readBits.length = 192) :
    let framed := s.run (assert :: (samples ++ [close]))
    let current := SerialSourceRead.sourceRun program source (assert :: (samples ++ [close]))
    let input : Values Reactive.Input := framed.coreInputs dispatch
    Operands input word ∧ Reactive.releasing.eval input framed.controller.core = 1 ∧
      (∃ e outcome, current.buffers.slot = .completed ⟨e, outcome⟩ ∧
        e.request.identity = current.owner ∧
        Transfer.step Refinement.capacity current.buffers (.release current.owner) =
          ⟨{current.buffers with slot := .free}, .released⟩) ∧
      ReadResult program layout (framed.step dispatch) word capture readAssert readClose readSamples := by
  let framed := s.run (assert :: (samples ++ [close]))
  have frame := SerialSourceRequest.frame_source s source related word assert close samples
    available low bits idle
  have fields := operands framed dispatch word frame.1 opcode valid dispatchIdle.1
  have matchingGeneration := fields.generation.trans generation
  have matchingTransfer := fields.transfer.trans transfer
  have release := Lifecycle.release_exact (framed.coreInputs dispatch) framed.controller.core
    fields.cold fields.command retained matchingGeneration matchingTransfer
  have installed := frame.2.installed
  have executing : SramExecution.ExecutingInput (framed.coreInputs dispatch) := by
    simp [SramExecution.ExecutingInput, SharedBranches.Runtime, fields.cold, fields.command]
  have releasedInstalled := installed.step (framed.coreInputs dispatch) executing
  have releasedFree : Free (framed.step dispatch).controller :=
    ⟨Lifecycle.release_scalar_step framed.controller (framed.coreInputs dispatch)
      fields.cold fields.command retained matchingGeneration matchingTransfer .phase trivial,
     Lifecycle.release_scalar_step framed.controller (framed.coreInputs dispatch)
      fields.cold fields.command retained matchingGeneration matchingTransfer .retained trivial⟩
  have rejection : framed.status dispatch .rejected = 0 :=
    accepted_not_rejected installed (framed.coreInputs dispatch) fields retained matchingGeneration matchingTransfer
  have pending : Capturing word false (framed.step dispatch).record := by
    rw [framed.record_step]
    simpa only [show (framed.inputs dispatch).status .rejected = 0 from rejection,
      show ((0 : BitVec 1) == 1) = false from rfl, Bool.and_false] using
      frame.1.step_dispatch (framed.inputs dispatch) dispatchIdle
  exact ⟨fields, release, source_release frame.2 retained,
    capture_read (framed.step dispatch) releasedInstalled releasedFree word valid pending
      capture captureIdle readAssert readClose readBits readSamples readLow readWire readIdle length⟩

end Pinwheel.Hardware.Buffered.SerialSourceRelease
