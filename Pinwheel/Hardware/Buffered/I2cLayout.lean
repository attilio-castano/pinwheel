import Pinwheel.Hardware.Buffered.I2cSource
import Pinwheel.Hardware.Buffered.GenericLayout

/-! Static source-derived coordinates and binary-field certificates for the
fixed reactive I²C program. These certificates inspect addresses and immutable
source/image data, never controller transitions or observed traces. -/
namespace Pinwheel.Hardware.Buffered.I2cLayout
open Pinwheel.Hardware Pinwheel.Program

abbrev coordinates : Program.Buffered.PC → GenericLayout.Coordinates :=
  GenericLayout.sourceCoordinates I2cSource.source

def row (pc : Program.Buffered.PC) : BitVec 6 := (coordinates pc).row.extractLsb' 0 6

def pc (v : Fin 270) : Program.Buffered.PC := ⟨v.val, Nat.lt_trans v.isLt (by decide)⟩

theorem fault_stop_coordinates : coordinates 265 = ⟨45, 0, 0⟩ := by
  rfl

set_option maxRecDepth 10000 in
set_option maxHeartbeats 12000000 in
theorem bounds : ∀ v : Fin 270, (coordinates (pc v)).row.toNat < 50 ∧
    (coordinates (pc v)).outer.toNat < 8 ∧ (coordinates (pc v)).inner.toNat < 8 := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 24000000 in
theorem records : ∀ v : Fin 270,
    (I2cSource.source.fetch (pc v)).map
      (GenericLayout.record coordinates (I2cSource.control (row (pc v)))) =
      some (I2cSource.fullWords (row (pc v))) := by
  decide +kernel

def next (v : Fin 269) : Program.Buffered.PC := ⟨v.val + 1, by have := v.isLt; omega⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 12000000 in
theorem successors : ∀ v : Fin 269,
    GenericLayout.sequential
      ((I2cSource.control (row ⟨v.val, Nat.lt_trans v.isLt (by decide)⟩)).extractLsb' 0 22)
      (coordinates ⟨v.val, Nat.lt_trans v.isLt (by decide)⟩) = coordinates (next v) := by
  decide +kernel

theorem initial_coordinates : coordinates 0 = ⟨0, 0, 0⟩ := by
  rfl

theorem coordinate_bound (p : Program.Buffered.PC) (within : p.val < 270) :
    (coordinates p).row.toNat < 50 :=
  (bounds ⟨p.val, within⟩).1

theorem source_record (p : Program.Buffered.PC) (within : p.val < 270)
    (instruction : Program.Buffered.Instruction) (fetch : I2cSource.source.fetch p = some instruction) :
    I2cSource.fullWords (row p) =
      GenericLayout.record coordinates (I2cSource.control (row p)) instruction := by
  have h := records ⟨p.val, within⟩
  simpa only [show pc ⟨p.val, within⟩ = p from rfl, fetch, Option.map_some,
    Option.some.injEq] using h.symm

theorem sequential_coordinates (p : Program.Buffered.PC) (within : p.val < 269) :
    GenericLayout.sequential ((I2cSource.control (row p)).extractLsb' 0 22)
      (coordinates p) = coordinates ⟨p.val + 1, by have := p.isLt; omega⟩ :=
  successors ⟨p.val, within⟩

end Pinwheel.Hardware.Buffered.I2cLayout
