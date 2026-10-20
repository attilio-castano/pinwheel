import Pinwheel.Hardware.Buffered.GenericWireUpload
import Pinwheel.Hardware.Buffered.SerialUploadConcrete

/-! Concrete actual-wire installation of any static certified shared image.
The witness has 16 dictionary writes, count row writes and one COMMIT, with
complete sampled requests and 192-bit receipt reads between all writes. -/
namespace Pinwheel.Hardware.Buffered.GenericUpload.Serial
open Pinwheel.Hardware Pinwheel.Program SerialWire
variable {p : Program.Buffered.Program} {layout : GenericCertificate.Layout p}
set_option maxRecDepth 4096

theorem Loading.controller_run {image : Image p layout} {before} (loading : Loading image before) :
    before.controller.run (before.commands loading.pins) = loading.after.controller := by
  rw [← before.run_controller,loading.run_pins]

theorem cold_install (image : Image p layout) (s : SerialPackage.State) (pin : SerialPackage.Pins)
    (cold : pin.cold = true) (idle : pin.csn = true) (loading : Loading image (s.step pin)) :
    Refinement.InstalledSram p layout loading.after.controller ∧
      loading.after.controller.core .phase = 0 ∧ loading.after.controller.core .retained = 0 ∧
      loading.after.controller.core .generation = 1 ∧ loading.after.controller.core .transfer = 0 ∧
      Serial.Frames.Available loading.after.record ∧ s.run (pin :: loading.pins) = loading.after := by
  have result := loading.result (Buffered.SerialUpload.cold_progress s pin cold) (by decide)
    (Buffered.SerialUpload.cold_available s pin cold idle)
  have coldInit := Buffered.SerialUpload.cold_input s pin cold
  have reset : Reactive.resetting.eval (s.coreInputs pin) s.controller.core = 1 := by
    simp [Reactive.resetting,Reactive.cold,Reactive.either,Expr.eval,coldInit]
  have installed := reset_installed image s.controller (s.coreInputs pin) reset
    ((s.step pin).commands loading.pins) result.2.1
  change ((s.step pin).controller.run ((s.step pin).commands loading.pins)).core .valid = 1 →
    Refinement.InstalledSram p layout ((s.step pin).controller.run ((s.step pin).commands loading.pins)) at installed
  rw [loading.controller_run] at installed
  have progress := Buffered.SerialUpload.cold_progress s pin cold
  have transfer := (LifecycleUpload.run (s.step pin).controller _ result.2.2.1 progress.phase progress.retained).2.2.1
  rw [loading.controller_run] at transfer
  refine ⟨installed result.1.valid,result.1.phase,result.1.retained,?_,?_,result.2.2.2,?_⟩
  · apply BitVec.eq_of_toNat_eq
    exact result.1.generation
  · exact transfer.trans (Lifecycle.cold_counters s.controller (s.coreInputs pin) coldInit).2
  · exact loading.run_pins

structure TableTrace (image : Image p layout) (before : SerialPackage.State) (n : Nat) where
  after : SerialPackage.State
  trace : Tables image n before after
  available : Serial.Frames.Available after.record

def concreteTables (image : Image p layout) (before : SerialPackage.State)
    (available : Serial.Frames.Available before.record) (sequence : Nat → BitVec 16)
    (raw : BitVec 2) : (n : Nat) → TableTrace image before n
  | 0 => ⟨before,.nil before,available⟩
  | n+1 =>
    let previous := concreteTables image before available sequence raw n
    let transaction := concrete previous.after previous.available (tableWord image (sequence n) (BitVec.ofNat 4 n)) raw
    ⟨transaction.after,.snoc previous.trace transaction (sequence n) (concrete_word ..),transaction.exact.1⟩

structure RowTrace (image : Image p layout) (before : SerialPackage.State) (n : Nat) where
  after : SerialPackage.State
  trace : Rows image n before after
  available : Serial.Frames.Available after.record

def concreteRows (image : Image p layout) (before : SerialPackage.State)
    (available : Serial.Frames.Available before.record) (sequence : Nat → BitVec 16)
    (raw : BitVec 2) : (n : Nat) → RowTrace image before n
  | 0 => ⟨before,.nil before,available⟩
  | n+1 =>
    let previous := concreteRows image before available sequence raw n
    let transaction := concrete previous.after previous.available (rowWord image (sequence n) (BitVec.ofNat 6 n)) raw
    ⟨transaction.after,.snoc previous.trace transaction (sequence n) (concrete_word ..),transaction.exact.1⟩

def concreteLoading (image : Image p layout) (before : SerialPackage.State)
    (available : Serial.Frames.Available before.record)
    (sequence : Nat → BitVec 16 := BitVec.ofNat 16) (raw : BitVec 2 := 0) : Loading image before :=
  let tables := concreteTables image before available sequence raw 16
  let rows := concreteRows image tables.after tables.available (fun n => sequence (16+n)) raw layout.count.val
  let commit := concrete rows.after rows.available (commitWord p layout (sequence (16+layout.count.val))) raw
  ⟨tables.after,tables.trace,rows.after,rows.trace,commit,sequence (16+layout.count.val),concrete_word ..⟩

theorem initialized_exists (image : Image p layout) (s : SerialPackage.State) (pin : SerialPackage.Pins)
    (cold : pin.cold = true) (idle : pin.csn = true)
    (sequence : Nat → BitVec 16 := BitVec.ofNat 16) (raw : BitVec 2 := 0) :
    ∃ loading : Loading image (s.step pin),
      Refinement.InstalledSram p layout loading.after.controller ∧
      loading.after.controller.core .phase = 0 ∧ loading.after.controller.core .retained = 0 ∧
      loading.after.controller.core .generation = 1 ∧ loading.after.controller.core .transfer = 0 ∧
      Serial.Frames.Available loading.after.record ∧ s.run (pin :: loading.pins) = loading.after :=
  ⟨concreteLoading image (s.step pin) (Buffered.SerialUpload.cold_available s pin cold idle) sequence raw,
    cold_install image s pin cold idle _⟩

end Pinwheel.Hardware.Buffered.GenericUpload.Serial
