import Pinwheel.Hardware.Buffered.GenericWireReloadWitness

/-! Witness assembly is separate from representation/refinement: a round
factory proves a terminating diagnostic for its particular source program.
Arbitrary certified programs need not terminate. No such factory is required
by the universal initialized session theorem. -/
namespace Pinwheel.Hardware.Buffered.GenericWireSession
open Pinwheel.Hardware Pinwheel.Program Refinement Serial.Frames
open GenericLogicalWire.Witness (LogicalRound)
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

def RoundFactory (image : ProgramImage) : Type :=
  ∀ before logical offset,
    InstalledSram image.program image.layout before.controller →
    LogicalSession.Aligned before.controller logical offset → Available before.record →
    before.controller.core .transfer ≠ 65535 → BitVec 16 → BitVec 16 →
      LogicalRound (p := image.program) (layout := image.layout) before logical offset

theorem initialized_warm_switch_two_rounds (image nextImage : ProgramImage)
    (firstFactory : RoundFactory image) (secondFactory : RoundFactory nextImage)
    (before : SerialPackage.State) (previous : Transfer.State)
    (pin : SerialPackage.Pins) (cold : pin.cold = true) (idle : pin.csn = true) :
    ∃ loading : GenericUpload.Serial.Loading image.image (before.step pin),
      ∃ first : LogicalRound (p := image.program) (layout := image.layout)
        loading.after (LogicalSession.resetLogical previous) 0,
      ∃ reload : WarmReload image nextImage first.after first.finalLogical 0,
      ∃ second : LogicalRound (p := nextImage.program) (layout := nextImage.layout)
        reload.after (LogicalSession.resetLogical first.finalLogical) reload.offset,
      ∃ trace : Trace loading.after image (.free (LogicalSession.resetLogical previous) 0) .available
        (first.pins ++ (reload.pins ++ second.pins)) second.after nextImage
        (.free second.finalLogical reload.offset) .available,
      before.run ((pin :: loading.pins) ++ (first.pins ++ (reload.pins ++ second.pins))) = second.after ∧
      Valid nextImage second.after (.free second.finalLogical reload.offset) .available ∧
      second.finalLogical.epoch = previous.epoch + 2 ∧ second.finalLogical.nextSequence = 2 ∧
      second.after.controller.core .generation = 3 ∧ second.after.controller.core .transfer = 2 ∧
      reload.offset = 1 ∧ trace.Observed := by
  let loading := GenericUpload.Serial.concreteLoading image.image (before.step pin)
    (Buffered.SerialUpload.cold_available before pin cold idle)
  have boot := GenericUpload.Serial.cold_install image.image before pin cold idle loading
  have initial : Valid image loading.after (.free (LogicalSession.resetLogical previous) 0) .available := by
    refine ⟨boot.2.2.2.2.2.1,boot.1,⟨rfl,boot.2.1,boot.2.2.1,?_⟩⟩
    rw [boot.2.2.2.2.1]
    rfl
  have room : loading.after.controller.core .transfer ≠ 65535 := by rw [boot.2.2.2.2.1]; decide
  let first := firstFactory loading.after (LogicalSession.resetLogical previous) 0
    initial.2.1 initial.2.2 initial.1 room 100 101
  have firstTransfer : first.after.controller.core .transfer = 1 := by
    apply BitVec.eq_of_toNat_eq
    change (first.release.after.controller.core .transfer).toNat = (1#16).toNat
    rw [first.transfer,boot.2.2.2.2.1]
    rfl
  have firstGeneration : first.after.controller.core .generation = 1 := first.generation.trans boot.2.2.2.1
  let reload := makeWarmReload image nextImage first.after first.finalLogical 0 first.post
    (by rw [firstGeneration]; decide)
  have reloadedTransfer : reload.after.controller.core .transfer = 1 := reload.transfer.trans firstTransfer
  have reloadedGeneration : reload.after.controller.core .generation = 3 := by
    apply BitVec.eq_of_toNat_eq
    change (reload.loading.after.controller.core .generation).toNat = (3#16).toNat
    rw [reload.generation,firstGeneration]
    rfl
  have reloadOffset : reload.offset = 1 := by
    change (reload.after.controller.core .transfer).toNat = 1
    rw [reloadedTransfer]
    rfl
  have nextRoom : reload.after.controller.core .transfer ≠ 65535 := by rw [reloadedTransfer]; decide
  let second := secondFactory reload.after (LogicalSession.resetLogical first.finalLogical) reload.offset
    reload.post.2.1 reload.post.2.2 reload.post.1 nextRoom 200 201
  have secondTransfer : second.after.controller.core .transfer = 2 := by
    apply BitVec.eq_of_toNat_eq
    change (second.release.after.controller.core .transfer).toNat = (2#16).toNat
    rw [second.transfer,reloadedTransfer]
    rfl
  let trace : Trace loading.after image (.free (LogicalSession.resetLogical previous) 0) .available
      (first.pins ++ (reload.pins ++ second.pins)) second.after nextImage
      (.free second.finalLogical reload.offset) .available :=
    appendTrace (runtimeTrace image first.trace) (appendTrace reload.trace (runtimeTrace nextImage second.trace))
  refine ⟨loading,first,reload,second,trace,?_,second.post,?_,?_,?_,secondTransfer,reloadOffset,trace.observed initial⟩
  · exact SerialSessionWitness.append_package_run before loading.after second.after
      (pin :: loading.pins) _ boot.2.2.2.2.2.2 trace.run_pins
  · have epoch := second.epoch
    change second.finalLogical.epoch = first.finalLogical.epoch+1 at epoch
    rw [first.epoch] at epoch
    exact epoch
  · have allocation := second.post.2.2.sequence
    change reload.offset + second.finalLogical.nextSequence =
      (second.after.controller.core .transfer).toNat+1 at allocation
    rw [secondTransfer] at allocation
    change reload.offset + second.finalLogical.nextSequence = 3 at allocation
    omega
  · exact second.generation.trans reloadedGeneration

end Pinwheel.Hardware.Buffered.GenericWireSession
