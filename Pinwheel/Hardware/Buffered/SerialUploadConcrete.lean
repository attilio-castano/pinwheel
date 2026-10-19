import Pinwheel.Hardware.Buffered.SerialUploadInstallation
import Pinwheel.Hardware.Buffered.SerialWireConcrete

/-! A concrete physical witness for every stage of the 67-command upload.
Two sampled edges per serial bit suffice; no decoded trace, known SRAM cell,
or supplied VALID bit is needed. -/
namespace Pinwheel.Hardware.Buffered.SerialUpload
open Pinwheel.Hardware SerialWire
set_option maxRecDepth 4096

structure TableTrace (before : SerialPackage.State) (n : Nat) where
  after : SerialPackage.State
  trace : Tables n before after
  available : Serial.Frames.Available after.record

def concreteTables (before : SerialPackage.State) (available : Serial.Frames.Available before.record)
    (sequence : Nat → BitVec 16) (raw : BitVec 2) : (n : Nat) → TableTrace before n
  | 0 => ⟨before, .nil before, available⟩
  | n+1 =>
    let previous := concreteTables before available sequence raw n
    let transaction := concrete previous.after previous.available (tableWord (sequence n) (BitVec.ofNat 4 n)) raw
    ⟨transaction.after, .snoc previous.trace transaction (sequence n) (concrete_word ..), transaction.exact.1⟩

structure RowTrace (before : SerialPackage.State) (n : Nat) where
  after : SerialPackage.State
  trace : Rows n before after
  available : Serial.Frames.Available after.record

def concreteRows (before : SerialPackage.State) (available : Serial.Frames.Available before.record)
    (sequence : Nat → BitVec 16) (raw : BitVec 2) : (n : Nat) → RowTrace before n
  | 0 => ⟨before, .nil before, available⟩
  | n+1 =>
    let previous := concreteRows before available sequence raw n
    let transaction := concrete previous.after previous.available (rowWord (sequence n) (BitVec.ofNat 6 n)) raw
    ⟨transaction.after, .snoc previous.trace transaction (sequence n) (concrete_word ..), transaction.exact.1⟩

def concreteLoading (before : SerialPackage.State) (available : Serial.Frames.Available before.record)
    (sequence : Nat → BitVec 16 := BitVec.ofNat 16) (raw : BitVec 2 := 0) : Loading before :=
  let tables := concreteTables before available sequence raw 16
  let rows := concreteRows tables.after tables.available (fun n => sequence (16+n)) raw 50
  let commit := concrete rows.after rows.available (commitWord (sequence 66)) raw
  ⟨tables.after, tables.trace, rows.after, rows.trace, commit, sequence 66, concrete_word ..⟩

theorem initialized_exists (s : SerialPackage.State) (pin : SerialPackage.Pins)
    (cold : pin.cold = true) (idle : pin.csn = true)
    (sequence : Nat → BitVec 16 := BitVec.ofNat 16) (raw : BitVec 2 := 0) :
    ∃ loading : Loading (s.step pin),
      Refinement.InstalledSram I2cSource.source I2cCertificate.layout loading.after.controller ∧
      loading.after.controller.core .phase = 0 ∧ loading.after.controller.core .retained = 0 ∧
      loading.after.controller.core .generation = 1 ∧ loading.after.controller.core .transfer = 0 ∧
      Serial.Frames.Available loading.after.record ∧
      s.run (pin :: loading.pins) = loading.after := by
  exact ⟨concreteLoading (s.step pin) (cold_available s pin cold idle) sequence raw,
    cold_install s pin cold idle _⟩
  done

end Pinwheel.Hardware.Buffered.SerialUpload
