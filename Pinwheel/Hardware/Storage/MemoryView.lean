import Pinwheel.Hardware.Memory.Flops
import Pinwheel.Hardware.Storage.Backend

/-! The storage the design already has, seen through the memory contract. The
functional image of the atomic loader is two memories of latency zero (the
dictionary and the address map) plus two metadata registers; the upload cursor is
their decoded write port, and the two instruction reads are two read ports of
their composition. The selected general backend's per-word registers step as the
flip-flop implementation does. Nothing here changes an expression, so the
emitted RTL and its read-back proofs are untouched. -/
namespace Pinwheel.Hardware.Loader.Store
open Pinwheel.Hardware.Memory

def dictionary (m : Image) : Contents 6 64 := fun k => m (.word k)
def indexMap (m : Image) : Contents 8 6 := fun k => m (.index k)

/-- The instruction read: an address-map lookup followed by a dictionary lookup. -/
def composite (m : Image) : Contents 8 64 := fun a => dictionary m (indexMap m a)

theorem read_composite (m : Image) (a : BitVec 8) : read m a = composite m a := rfl

/-- The upload cursor addresses the dictionary below 64 and the map from 64 to 319. -/
def dictionaryWrite (i : Inputs) : Write 6 64 :=
  ⟨i.write && decide (i.cursor < 64#9), i.cursor.setWidth 6, i.data⟩

def indexWrite (i : Inputs) : Write 8 6 :=
  ⟨i.write && decide (64#9 ≤ i.cursor ∧ i.cursor < 320#9), (i.cursor - 64#9).setWidth 8,
    i.data.extractLsb' 0 6⟩

private theorem word_hit (c : BitVec 9) (k : BitVec 6) :
    (c = k.setWidth 9) ↔ (c < 64#9 ∧ c.setWidth 6 = k) := by
  have hk := k.isLt
  have hc := c.isLt
  simp only [BitVec.toNat_eq, BitVec.toNat_setWidth, BitVec.lt_def, BitVec.toNat_ofNat]
  omega

private theorem index_hit (c : BitVec 9) (k : BitVec 8) :
    (c = BitVec.ofNat 9 (64 + k.toNat)) ↔ ((64#9 ≤ c ∧ c < 320#9) ∧ (c - 64#9).setWidth 8 = k) := by
  have hk := k.isLt
  have hc := c.isLt
  simp only [BitVec.toNat_eq, BitVec.toNat_setWidth, BitVec.lt_def, BitVec.le_def, BitVec.toNat_ofNat,
    BitVec.toNat_sub]
  omega

theorem tick_dictionary (i : Inputs) (m : Image) :
    dictionary (tick i m) = (dictionary m).write (dictionaryWrite i) := by
  funext k
  have hc : (i.cursor == BitVec.ofNat 9 k.toNat) =
      (decide (i.cursor < 64#9) && (i.cursor.setWidth 6 == k)) := by
    rw [Bool.eq_iff_iff, BitVec.ofNat_toNat]
    simp only [beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq]
    exact word_hit i.cursor k
  simp only [dictionary, tick, offset, Contents.write, dictionaryWrite, hc, Bool.and_assoc,
    BitVec.extractLsb'_eq_self]

theorem tick_index (i : Inputs) (m : Image) :
    indexMap (tick i m) = (indexMap m).write (indexWrite i) := by
  funext k
  have hc : (i.cursor == BitVec.ofNat 9 (64 + k.toNat)) =
      (decide (64#9 ≤ i.cursor ∧ i.cursor < 320#9) && ((i.cursor - 64#9).setWidth 8 == k)) := by
    rw [Bool.eq_iff_iff]
    simp only [beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq]
    exact index_hit i.cursor k
  simp only [indexMap, tick, offset, Contents.write, indexWrite, hc, Bool.and_assoc]

/-- Neither memory sees the other's writes: the cursor decodes to at most one of them. -/
theorem writes_exclusive (i : Inputs) :
    (dictionaryWrite i).enable = false ∨ (indexWrite i).enable = false := by
  simp only [dictionaryWrite, indexWrite]
  by_cases h : i.cursor < 64#9
  · right
    simp [show ¬ (64#9 ≤ i.cursor ∧ i.cursor < 320#9) from fun ⟨h1, _⟩ => by bv_omega]
  · left
    simp [h]

end Pinwheel.Hardware.Loader.Store

namespace Pinwheel.Hardware.Loader.Machine
open Pinwheel.Hardware.Memory

/-- Each bank of the atomic machine is a pair of memories written from the cursor. -/
theorem next_dictionary (i : Inputs) (s : State) (b : Bool) :
    Store.dictionary ((next i s).memory b) =
      (Store.dictionary (s.memory b)).write (Store.dictionaryWrite (memoryInput i s b)) := by
  simp [next, Store.tick_dictionary]

theorem next_indexMap (i : Inputs) (s : State) (b : Bool) :
    Store.indexMap ((next i s).memory b) =
      (Store.indexMap (s.memory b)).write (Store.indexWrite (memoryInput i s b)) := by
  simp [next, Store.tick_index]

/-- The scheduler's two instruction reads are two read ports of the selected
bank's composite memory, at the current and the target address. -/
def readRequest (i : Inputs) (s : State) : Request 8 64 2 :=
  ⟨⟨false, 0, 0⟩, fun port => if port = 0 then s.core.pc else Reactive.targetValue (baseInput i s) s.core⟩

theorem reads_correct (i : Inputs) (s : State) :
    (schedulerInput i s).current = (Store.composite (s.memory (selected i s))).reads (readRequest i s) 0 ∧
    (schedulerInput i s).successor = (Store.composite (s.memory (selected i s))).reads (readRequest i s) 1 := by
  simp [schedulerInput, baseInput, Reactive.Fetch.resolve, Reactive.Fetch.Request.address,
    Contents.reads, readRequest, Store.read_composite]

end Pinwheel.Hardware.Loader.Machine

namespace Pinwheel.Hardware.Storage.Backend
open Loader Pinwheel.Hardware.Memory

/-- The 32 dense words of one bank of the selected general backend. -/
def dictionary (s : State) (b : Bool) : Contents 5 55 := fun k => (s.words b)[k.toNat]

/-- Their write port: the bank's write, the low cursor bits, the compressed word. -/
def dictionaryWrite (i : Machine.Inputs) (s : State) (b : Bool) : Write 5 55 :=
  let m := Machine.memoryInput (adapt i s) s.reference.machine b
  ⟨m.write && decide (m.cursor < 32#9), m.cursor.setWidth 5, Dense.compress i.data⟩

private theorem dense_hit (c : BitVec 9) (k : BitVec 5) :
    (c = k.setWidth 9) ↔ (c < 32#9 ∧ c.setWidth 5 = k) := by
  have hk := k.isLt
  have hc := c.isLt
  simp only [BitVec.toNat_eq, BitVec.toNat_setWidth, BitVec.lt_def, BitVec.toNat_ofNat]
  omega

/-- Each bank's dictionary registers step as a flip-flop memory of latency zero
under that port: the backend contains two `Memory.Flops` dictionaries. -/
theorem next_dictionary (i : Machine.Inputs) (s : State) (b : Bool) :
    dictionary (next i s) b = (dictionary s b).write (dictionaryWrite i s b) := by
  funext k
  have hc : ((Machine.memoryInput (adapt i s) s.reference.machine b).cursor == BitVec.ofNat 9 k.toNat) =
      (decide ((Machine.memoryInput (adapt i s) s.reference.machine b).cursor < 32#9) &&
        ((Machine.memoryInput (adapt i s) s.reference.machine b).cursor.setWidth 5 == k)) := by
    rw [Bool.eq_iff_iff, BitVec.ofNat_toNat]
    simp only [beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq]
    exact dense_hit _ k
  have hk : (BitVec.ofFin ⟨k.toNat, k.isLt⟩ : BitVec 5) = k := rfl
  simp only [dictionary, next, Vector.getElem_ofFn, writing, hk, Contents.write, dictionaryWrite,
    hc, Bool.and_assoc]

/-- The structural registers follow, through the proved interpretation. -/
theorem word_registers (i : Machine.Inputs) (s : State) (b : Bool) (k : BitVec 5) :
    circuit.step i.values s.values (.word b k) = (dictionary s b).write (dictionaryWrite i s b) k := by
  rw [next_correct i s (.word b k), ← next_dictionary]
  rfl

end Pinwheel.Hardware.Storage.Backend
