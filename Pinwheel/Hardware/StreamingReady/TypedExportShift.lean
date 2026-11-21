import Pinwheel.Hardware.StreamingReady.TxShiftCore
import Pinwheel.Hardware.StreamingReady.TypedExport

/-! Export the shift core with the same public ports and a complete register
inventory that omits the two ring pointers. -/
namespace Pinwheel.Hardware.StreamingReady.TypedExportShift
open Pinwheel.Hardware

private abbrev ring := TypedExport.core 1 (.inl rfl)
private abbrev droppedAt := Core.registerIndex (.txHead : Core.Register 1 1)

private theorem ringSize : ring.registers.size = 105 := by decide +kernel

private theorem retained_iff (r : Core.Register 1 w) :
    TxShiftCore.retained r ↔
      (ring.registers.position r).val < droppedAt ∨
      droppedAt + 2 ≤ (ring.registers.position r).val := by
  change TxShiftCore.retained r ↔ Core.registerIndex r < 89 ∨ 91 ≤ Core.registerIndex r
  cases r <;> try decide
  all_goals
    rename_i k
    have hk := k.isLt
    simp at hk
    simp [TxShiftCore.retained, Core.registerIndex, Streaming.Core.registerIndex]
    omega
  done

private def ringSlot (k : Fin 103) : Fin ring.registers.size :=
  ⟨if k.val < droppedAt then k.val else k.val + 2, by
    rw [ringSize]
    have hk := k.isLt
    change (if k.val < 89 then k.val else k.val + 2) < 105
    split <;> omega⟩

private def position (r : TxShiftCore.Register w) : Fin 103 :=
  let n := (ring.registers.position r.val).val
  ⟨if n < droppedAt then n else n - 2, by
    have hn : n < 105 := (congrArg (fun bound => n < bound) ringSize).mp
      (ring.registers.position r.val).isLt
    change (if n < 89 then n else n - 2) < 103
    split <;> omega⟩

private theorem ringSlot_position (r : TxShiftCore.Register w) :
    ringSlot (position r) = ring.registers.position r.val := by
  apply Fin.ext
  let n := (ring.registers.position r.val).val
  have kept : n < 89 ∨ 91 ≤ n := (retained_iff r.val).mp r.property
  change (if (if n < 89 then n else n - 2) < 89 then
    (if n < 89 then n else n - 2) else (if n < 89 then n else n - 2) + 2) = n
  rcases kept with h | h
  · simp [h]
  · have hn : ¬ n < 89 := by omega
    have hp : ¬ n - 2 < 89 := by omega
    simp only [if_neg hn, if_neg hp]
    omega
  done

private theorem retained_signal (k : Fin 103) :
    TxShiftCore.retained (ring.registers.signal (ringSlot k)).2 := by
  apply (retained_iff _).mpr
  rw [ring.registers.position_signal]
  change (if k.val < 89 then k.val else k.val + 2) < 89 ∨
    91 ≤ (if k.val < 89 then k.val else k.val + 2)
  by_cases hk : k.val < 89
  · exact Or.inl (by simpa only [if_pos hk] using hk)
  · apply Or.inr
    rw [if_neg hk]
    omega

private def signal (k : Fin 103) : Sigma TxShiftCore.Register :=
  let raw := ring.registers.signal (ringSlot k)
  ⟨raw.1, ⟨raw.2, retained_signal k⟩⟩

private def forget (r : Sigma TxShiftCore.Register) : Sigma (Core.Register 1) :=
  ⟨r.1, r.2.val⟩

private theorem forget_injective : Function.Injective forget := by
  intro ⟨w, ⟨r, hr⟩⟩ ⟨v, ⟨s, hs⟩⟩ eq
  cases eq
  rfl

private theorem ringSlot_injective : Function.Injective ringSlot := by
  intro a b eq
  apply Fin.ext
  have value := congrArg Fin.val eq
  change (if a.val < 89 then a.val else a.val + 2) =
    (if b.val < 89 then b.val else b.val + 2) at value
  by_cases ha : a.val < 89 <;> by_cases hb : b.val < 89 <;>
    simp only [ha, hb, if_true, if_false] at value <;> omega

def core : TypedModule Core.Input TxShiftCore.Register Core.Output where
  name := ring.name
  circuit := TxShiftCore.circuit
  inputs := ring.inputs
  registers := {
    size := 103
    signal := signal
    position := position
    signal_position := by
      intro _ r
      apply forget_injective
      change ring.registers.signal (ringSlot (position r)) = ⟨_, r.val⟩
      rw [ringSlot_position, ring.registers.signal_position]
    label := fun r => Core.registerLabel r.val
    unique := by
      intro a b h
      apply ringSlot_injective
      exact ring.registers.unique _ _ h }
  outputs := ring.outputs

end Pinwheel.Hardware.StreamingReady.TypedExportShift
