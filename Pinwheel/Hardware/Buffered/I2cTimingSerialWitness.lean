import Pinwheel.Hardware.Buffered.I2cTimingSerialTimeout
import Pinwheel.Hardware.Buffered.GenericLogicalWireWitness

/-! Two real accepted allocations and matching releases for every symbolic
timing pair, carrying the same ordinary transfer state across both rounds. -/
namespace Pinwheel.Hardware.Buffered.I2cTiming.SerialWitness
open Pinwheel.Hardware Pinwheel.Program SerialWire Serial.Frames
open GenericLogicalWire.Witness (LogicalRound appendLogicalTrace)
open SerialSessionWitness (roundStart roundRelease roundStart_opcode roundRelease_word append_package_run)
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

theorem roundStart_admitted (duration budget : Fin 256) (before : SerialPackage.State)
    (installed : Refinement.InstalledSram (source duration budget) (layout duration budget) before.controller)
    (free : SerialSourceRelease.Free before.controller) (available : Available before.record)
    (room : before.controller.core .transfer ≠ 65535) (sequence : BitVec 16) :
    Reactive.starting.eval ((roundStart before available sequence).framed.coreInputs
      (roundStart before available sequence).dispatch)
      (roundStart before available sequence).framed.controller.core = 1 := by
  unfold roundStart
  exact SerialStartAdmission.concrete_admitted before installed free available sequence 0 0 0 0
    room (by decide) (by decide)

theorem roundStart_timeout (duration budget : Fin 256) (before : SerialPackage.State)
    (available : Available before.record) (sequence : BitVec 16) :
    (SerialStartAdmission.sourceAfter (source duration budget)
      (roundStart before available sequence)).core.control = .stopped .timeout := by
  unfold roundStart
  exact concrete_timeout duration budget before available sequence 0 0 0

noncomputable opaque makeLogicalRound (duration budget : Fin 256) (before : SerialPackage.State)
    (logical : Transfer.State) (offset : Nat)
    (installed : Refinement.InstalledSram (source duration budget) (layout duration budget) before.controller)
    (aligned : LogicalSession.Aligned before.controller logical offset) (available : Available before.record)
    (room : before.controller.core .transfer ≠ 65535) (startSequence releaseSequence : BitVec 16) :
    LogicalRound (p := source duration budget) (layout := layout duration budget) before logical offset :=
  let start := roundStart before available startSequence
  let release := roundRelease start.after start.exact.1 releaseSequence
  GenericLogicalWire.Witness.assembleLogicalRound before logical offset installed aligned available start release
    (roundStart_admitted duration budget before installed ⟨aligned.phase,aligned.retained⟩ available room startSequence)
    (roundStart_opcode before available startSequence)
    (roundStart_timeout duration budget before available startSequence)
    releaseSequence (roundRelease_word start.after start.exact.1 releaseSequence)

theorem initialized_two_logical_rounds (duration budget : Fin 256) (before : SerialPackage.State)
    (previous : Transfer.State) (pin : SerialPackage.Pins) (cold : pin.cold = true) (idle : pin.csn = true) :
    ∃ loading : SerialUpload.Loading duration budget (before.step pin),
      ∃ first : LogicalRound (p := source duration budget) (layout := layout duration budget)
        loading.after (LogicalSession.resetLogical previous) 0,
      ∃ second : LogicalRound (p := source duration budget) (layout := layout duration budget)
        first.after first.finalLogical 0,
      ∃ trace : GenericLogicalWire.Trace (source duration budget) loading.after
        (.free (LogicalSession.resetLogical previous) 0) .available
        (first.pins ++ second.pins) second.after (.free second.finalLogical 0) .available,
      before.run ((pin :: loading.pins) ++ (first.pins ++ second.pins)) = second.after ∧
      LogicalWire.Valid duration budget second.after (.free second.finalLogical 0) .available ∧
      second.finalLogical.epoch = previous.epoch + 1 ∧ second.finalLogical.nextSequence = 3 ∧
      second.after.controller.core .generation = 1 ∧ second.after.controller.core .transfer = 2 ∧ trace.Observed := by
  let loading := SerialUpload.concreteLoading duration budget (before.step pin)
    (Buffered.SerialUpload.cold_available before pin cold idle)
  have boot := SerialUpload.cold_install duration budget before pin cold idle loading
  have initial : LogicalWire.Valid duration budget loading.after
      (.free (LogicalSession.resetLogical previous) 0) .available := by
    refine ⟨boot.2.2.2.2.2.1,boot.1,⟨rfl,boot.2.1,boot.2.2.1,?_⟩⟩
    rw [boot.2.2.2.2.1]
    rfl
  have room : loading.after.controller.core .transfer ≠ 65535 := by rw [boot.2.2.2.2.1]; decide
  let first := makeLogicalRound duration budget loading.after (LogicalSession.resetLogical previous) 0
    initial.2.1 initial.2.2 initial.1 room 67 68
  have firstTransfer : first.after.controller.core .transfer = 1 := by
    apply BitVec.eq_of_toNat_eq
    change (first.release.after.controller.core .transfer).toNat = (1#16).toNat
    rw [first.transfer,boot.2.2.2.2.1]
    rfl
  have nextRoom : first.after.controller.core .transfer ≠ 65535 := by rw [firstTransfer]; decide
  let second := makeLogicalRound duration budget first.after first.finalLogical 0
    first.post.2.1 first.post.2.2 first.post.1 nextRoom 69 70
  have secondTransfer : second.after.controller.core .transfer = 2 := by
    apply BitVec.eq_of_toNat_eq
    change (second.release.after.controller.core .transfer).toNat = (2#16).toNat
    rw [second.transfer,firstTransfer]
    rfl
  let trace : GenericLogicalWire.Trace (source duration budget) loading.after
      (.free (LogicalSession.resetLogical previous) 0) .available
      (first.pins ++ second.pins) second.after (.free second.finalLogical 0) .available :=
    appendLogicalTrace first.trace second.trace
  refine ⟨loading,first,second,trace,?_,second.post,?_,?_,?_,secondTransfer,trace.observed initial⟩
  · exact append_package_run before loading.after second.after (pin :: loading.pins)
      (first.pins ++ second.pins) boot.2.2.2.2.2.2 trace.run_pins
  · exact second.epoch.trans first.epoch
  · have allocation := second.post.2.2.sequence
    change 0 + second.finalLogical.nextSequence = (second.after.controller.core .transfer).toNat + 1 at allocation
    rw [secondTransfer] at allocation
    simpa using allocation
  · exact second.generation.trans (first.generation.trans boot.2.2.2.1)

/-- The nonempty witness inhabits the same outer trace that admits arbitrary
padding, retries, wire reloads and interior request/read interruptions. -/
theorem initialized_two_fused_rounds (duration budget : Fin 256) (before : SerialPackage.State)
    (previous : Transfer.State) (pin : SerialPackage.Pins) (cold : pin.cold = true) (idle : pin.csn = true) :
    ∃ loading : SerialUpload.Loading duration budget (before.step pin),
      ∃ first : LogicalRound (p := source duration budget) (layout := layout duration budget)
        loading.after (LogicalSession.resetLogical previous) 0,
      ∃ second : LogicalRound (p := source duration budget) (layout := layout duration budget)
        first.after first.finalLogical 0,
      ∃ trace : LogicalWire.Trace duration budget loading.after
        (.free (LogicalSession.resetLogical previous) 0) .available
        (first.pins ++ second.pins) second.after (.free second.finalLogical 0) .available,
      before.run ((pin :: loading.pins) ++ (first.pins ++ second.pins)) = second.after ∧
      LogicalWire.Valid duration budget second.after (.free second.finalLogical 0) .available ∧
      second.finalLogical.epoch = previous.epoch + 1 ∧ second.finalLogical.nextSequence = 3 ∧
      second.after.controller.core .generation = 1 ∧ second.after.controller.core .transfer = 2 ∧ trace.Observed := by
  obtain ⟨loading,first,second,runtime,run,valid,epoch,allocation,generation,transfer,_⟩ :=
    initialized_two_logical_rounds duration budget before previous pin cold idle
  let trace : LogicalWire.Trace duration budget loading.after
      (.free (LogicalSession.resetLogical previous) 0) .available
      (first.pins ++ second.pins) second.after (.free second.finalLogical 0) .available := by
    simpa only [List.append_nil] using LogicalWire.Trace.cons (LogicalWire.Event.segment runtime) .nil
  have boot := SerialUpload.cold_install duration budget before pin cold idle loading
  have initial : LogicalWire.Valid duration budget loading.after
      (.free (LogicalSession.resetLogical previous) 0) .available := by
    refine ⟨boot.2.2.2.2.2.1,boot.1,⟨rfl,boot.2.1,boot.2.2.1,?_⟩⟩
    rw [boot.2.2.2.2.1]
    rfl
  exact ⟨loading,first,second,trace,run,valid,epoch,allocation,generation,transfer,trace.observed initial⟩

end Pinwheel.Hardware.Buffered.I2cTiming.SerialWitness
