import Pinwheel.Hardware.Buffered.I2cTimingSerialUpload

/-! Nonvacuous initialization for every timing pair, from arbitrary preboot
frontend, SRAM contents and retained memory responses. VALID is derived. -/
namespace Pinwheel.Hardware.Buffered.I2cTiming.SerialUpload
open Pinwheel.Hardware SerialWire
set_option maxRecDepth 4096

theorem cold_install (duration budget : Fin 256) (s : SerialPackage.State)
    (pin : SerialPackage.Pins) (cold : pin.cold = true) (idle : pin.csn = true)
    (loading : Loading duration budget (s.step pin)) :
    Refinement.InstalledSram (source duration budget) (layout duration budget) loading.after.controller ∧
      loading.after.controller.core .phase = 0 ∧ loading.after.controller.core .retained = 0 ∧
      loading.after.controller.core .generation = 1 ∧ loading.after.controller.core .transfer = 0 ∧
      Serial.Frames.Available loading.after.record ∧
      s.run (pin :: loading.pins) = loading.after := by
  have result := loading.result (Buffered.SerialUpload.cold_progress s pin cold) (by decide)
    (Buffered.SerialUpload.cold_available s pin cold idle)
  have coldInit := Buffered.SerialUpload.cold_input s pin cold
  have reset : Reactive.resetting.eval (s.coreInputs pin) s.controller.core = 1 := by
    simp [Reactive.resetting,Reactive.cold,Reactive.either,Expr.eval,coldInit]
  have installed := I2cTiming.Upload.reset_installed duration budget s.controller
    (s.coreInputs pin) reset ((s.step pin).commands loading.pins) result.2.1
  change ((s.step pin).controller.run ((s.step pin).commands loading.pins)).core .valid = 1 →
    Refinement.InstalledSram (source duration budget) (layout duration budget)
      ((s.step pin).controller.run ((s.step pin).commands loading.pins)) at installed
  rw [loading.controller_run] at installed
  have progress := Buffered.SerialUpload.cold_progress s pin cold
  have transfer := (LifecycleUpload.run (s.step pin).controller _ result.2.2.1
    progress.phase progress.retained).2.2.1
  rw [loading.controller_run] at transfer
  refine ⟨installed result.1.valid,result.1.phase,result.1.retained,?_,?_,result.2.2.2,?_⟩
  · apply BitVec.eq_of_toNat_eq
    exact result.1.generation
  · exact transfer.trans (Lifecycle.cold_counters s.controller (s.coreInputs pin) coldInit).2
  · exact loading.run_pins

structure RowTrace (duration budget : Fin 256) (before : SerialPackage.State) (n : Nat) where
  after : SerialPackage.State
  trace : Rows duration budget n before after
  available : Serial.Frames.Available after.record

def concreteRows (duration budget : Fin 256) (before : SerialPackage.State)
    (available : Serial.Frames.Available before.record) (sequence : Nat → BitVec 16)
    (raw : BitVec 2) : (n : Nat) → RowTrace duration budget before n
  | 0 => ⟨before,.nil before,available⟩
  | n+1 =>
    let previous := concreteRows duration budget before available sequence raw n
    let transaction := concrete previous.after previous.available
      (rowWord duration budget (sequence n) (BitVec.ofNat 6 n)) raw
    ⟨transaction.after,.snoc previous.trace transaction (sequence n) (concrete_word ..),transaction.exact.1⟩

def concreteLoading (duration budget : Fin 256) (before : SerialPackage.State)
    (available : Serial.Frames.Available before.record)
    (sequence : Nat → BitVec 16 := BitVec.ofNat 16) (raw : BitVec 2 := 0) : Loading duration budget before :=
  let tables := Buffered.SerialUpload.concreteTables before available sequence raw 16
  let rows := concreteRows duration budget tables.after tables.available (fun n => sequence (16+n)) raw 50
  let commit := concrete rows.after rows.available (Buffered.SerialUpload.commitWord (sequence 66)) raw
  ⟨tables.after,tables.trace,rows.after,rows.trace,commit,sequence 66,concrete_word ..⟩

theorem initialized_exists (duration budget : Fin 256) (s : SerialPackage.State)
    (pin : SerialPackage.Pins) (cold : pin.cold = true) (idle : pin.csn = true)
    (sequence : Nat → BitVec 16 := BitVec.ofNat 16) (raw : BitVec 2 := 0) :
    ∃ loading : Loading duration budget (s.step pin),
      Refinement.InstalledSram (source duration budget) (layout duration budget) loading.after.controller ∧
      loading.after.controller.core .phase = 0 ∧ loading.after.controller.core .retained = 0 ∧
      loading.after.controller.core .generation = 1 ∧ loading.after.controller.core .transfer = 0 ∧
      Serial.Frames.Available loading.after.record ∧
      s.run (pin :: loading.pins) = loading.after :=
  ⟨concreteLoading duration budget (s.step pin) (Buffered.SerialUpload.cold_available s pin cold idle)
    sequence raw,cold_install duration budget s pin cold idle _⟩

end Pinwheel.Hardware.Buffered.I2cTiming.SerialUpload
