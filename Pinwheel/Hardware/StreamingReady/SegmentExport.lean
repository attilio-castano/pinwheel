import Pinwheel.Hardware.StreamingReady.SegmentCore
import Pinwheel.Hardware.StreamingReady.TypedExport

/-! Both segmented stores expose the existing Ready core ABI. The branch
    decision, capture validity, TX closure, and fetch latch are private. -/
namespace Pinwheel.Hardware.StreamingReady.SegmentExport

open Pinwheel.Hardware SegmentCore

private def label (base : Interface (Core.Register a)) : Register a w → String
  | .base r => base.label r
  | .lastCapture => "last_capture"
  | .captureValid => "capture_valid"
  | .txClosed => "tx_closed"
  | .fetched => "fetched"

private def extra : Fin 4 → Sigma (Register a)
  | 0 => ⟨1, .lastCapture⟩
  | 1 => ⟨1, .captureValid⟩
  | 2 => ⟨1, .txClosed⟩
  | _ => ⟨64, .fetched⟩

private def signal (base : Interface (Core.Register a)) (k : Fin (base.size + 4)) : Sigma (Register a) :=
  if h : k.val < base.size then
    let q := base.signal ⟨k.val, h⟩
    ⟨q.1, .base q.2⟩
  else extra ⟨k.val - base.size, by have := k.isLt; omega⟩

private def position (base : Interface (Core.Register a)) : Register a w → Fin (base.size + 4)
  | .base r => ⟨(base.position r).val, by have := (base.position r).isLt; omega⟩
  | .lastCapture => ⟨base.size, by omega⟩
  | .captureValid => ⟨base.size + 1, by omega⟩
  | .txClosed => ⟨base.size + 2, by omega⟩
  | .fetched => ⟨base.size + 3, by omega⟩

private theorem signal_position (base : Interface (Core.Register a)) (r : Register a w) :
    signal base (position base r) = ⟨w, r⟩ := by
  cases r with
  | base r =>
    unfold signal position
    rw [dif_pos (base.position r).isLt]
    change (let q := base.signal (base.position r); (⟨q.1, .base q.2⟩ : Sigma (Register a))) = _
    rw [base.signal_position]
  | lastCapture => simp [signal, position, extra]
  | captureValid => simp [signal, position, extra, show ¬ base.size + 1 < base.size by omega]
  | txClosed => simp [signal, position, extra, show ¬ base.size + 2 < base.size by omega]
  | fetched => simp [signal, position, extra, show ¬ base.size + 3 < base.size by omega]

private theorem extra_label (base : Interface (Core.Register a)) (j : Fin 4) :
    label base (extra j).2 = #["last_capture", "capture_valid", "tx_closed", "fetched"][j.val] := by
  have cases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
  rcases cases with rfl | rfl | rfl | rfl <;> rfl

set_option maxRecDepth 4096 in
private theorem extra_names_unused (supported : a = 1 ∨ a = 2) :
    let base := (TypedExport.core a supported).registers
    ∀ (k : Fin base.size) (j : Fin 4), base.label (base.signal k).2 ≠ label base (extra j).2 := by
  rcases supported with rfl | rfl <;> decide +kernel

private theorem extra_unique (base : Interface (Core.Register a)) (j k : Fin 4)
    (same : label base (extra j).2 = label base (extra k).2) : j = k := by
  rw [extra_label, extra_label] at same
  have unique : ∀ (idx jdx : Fin 4),
      #["last_capture", "capture_valid", "tx_closed", "fetched"][idx.val] =
        #["last_capture", "capture_valid", "tx_closed", "fetched"][jdx.val] → idx = jdx := by decide +kernel
  exact unique j k same

private theorem label_at (base : Interface (Core.Register a)) (k : Fin (base.size + 4)) :
    label base (signal base k).2 =
      if h : k.val < base.size then base.label (base.signal ⟨k.val, h⟩).2
      else label base (extra ⟨k.val - base.size, by have := k.isLt; omega⟩).2 := by
  by_cases bound : k.val < base.size
  · rw [dif_pos bound]
    have selected : signal base k =
        ⟨(base.signal ⟨k.val, bound⟩).1, .base (base.signal ⟨k.val, bound⟩).2⟩ := dif_pos bound
    exact congrArg (fun port : Sigma (Register a) => label base port.2) selected
  · rw [dif_neg bound]
    have selected : signal base k = extra ⟨k.val - base.size, by have := k.isLt; omega⟩ := dif_neg bound
    exact congrArg (fun port : Sigma (Register a) => label base port.2) selected

private theorem labels_unique (base : Interface (Core.Register a))
    (unused : ∀ (k : Fin base.size) (j : Fin 4), base.label (base.signal k).2 ≠ label base (extra j).2)
    (k l : Fin (base.size + 4)) (same : label base (signal base k).2 = label base (signal base l).2) :
    k = l := by
  rw [label_at, label_at] at same
  by_cases hk : k.val < base.size <;> by_cases hl : l.val < base.size
  · rw [dif_pos hk, dif_pos hl] at same
    exact Fin.ext (congrArg (fun n : Fin base.size => n.val) (base.unique _ _ same))
  · rw [dif_pos hk, dif_neg hl] at same
    exact (unused _ _ same).elim
  · rw [dif_neg hk, dif_pos hl] at same
    exact (unused _ _ same.symm).elim
  · rw [dif_neg hk, dif_neg hl] at same
    have sameIndex := congrArg Fin.val (extra_unique base _ _ same)
    apply Fin.ext
    change k.val - base.size = l.val - base.size at sameIndex
    change k.val = l.val
    omega

def core (a : Nat) (supported : a = 1 ∨ a = 2) (registered : Bool) :
    TypedModule Core.Input (Register a) Core.Output :=
  let base := TypedExport.core a supported
  { name := base.name
    circuit := SegmentCore.circuit a registered
    inputs := base.inputs
    registers := ⟨base.registers.size + 4, signal base.registers, position base.registers,
      signal_position base.registers, label base.registers,
      labels_unique base.registers (extra_names_unused supported)⟩
    outputs := base.outputs }

end Pinwheel.Hardware.StreamingReady.SegmentExport
