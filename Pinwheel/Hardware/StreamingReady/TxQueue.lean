import Init.Data.BitVec

/-! The two-entry sampled-ready transmit FIFO writes and reads using
pre-edge occupancy. A simultaneous pop transfers the old head.
Slot records are polymorphic so a word and its valid-bit count move together. -/
namespace Pinwheel.Hardware.StreamingReady.TxQueue

structure Ring (α : Type u) where
  head : BitVec 1
  tail : BitVec 1
  count : BitVec 4
  slot : BitVec 1 → α

structure Shift (α : Type u) where
  count : BitVec 4
  slot : BitVec 1 → α

def stepCount (count : BitVec 4) (put take : Bool) : BitVec 4 :=
  if put then (if take then count else count + 1) else
    (if take then count - 1 else count)

def Ring.WellFormed (q : Ring α) : Prop :=
  q.count ≤ 2 ∧ q.tail = q.head + q.count.extractLsb' 0 1

/-- There is neither empty bypass nor full replacement. -/
def Ring.Legal (q : Ring α) (put take : Bool) : Prop :=
  (put = true → q.count < 2) ∧ (take = true → q.count ≠ 0)

def Ring.encode (q : Ring α) : Shift α :=
  ⟨q.count, fun index => q.slot (q.head + index)⟩

def Ring.step (q : Ring α) (clear put take : Bool) (incoming resetValue : α) : Ring α :=
  if clear then ⟨0, 0, 0, fun _ => resetValue⟩
  else
    ⟨if take then q.head + 1 else q.head,
      if put then q.tail + 1 else q.tail,
      stepCount q.count put take,
      fun index => if put && index == q.tail then incoming else q.slot index⟩

/-- When popping, the inactive slot receives the former head. Keeping this
inactive value lets the encoding relate both slots without imposing any
constraint on the data stored in an empty queue. -/
def Shift.step (q : Shift α) (clear put take : Bool) (incoming resetValue : α) : Shift α :=
  if clear then ⟨0, fun _ => resetValue⟩
  else
    ⟨stepCount q.count put take, fun index =>
      let oldIndex := if take then index + 1 else index
      if put && oldIndex == q.count.extractLsb' 0 1 then incoming else q.slot oldIndex⟩

private theorem advance_index : ∀ (head index : BitVec 1) (take : Bool),
    (if take then head + 1 else head) + index = head + (if take then index + 1 else index) := by
  decide +kernel

private theorem tail_index : ∀ (head index countBit : BitVec 1),
    (head + index == head + countBit) = (index == countBit) := by
  decide +kernel

/-- The ring's circular origin is absent from the shift layout. -/
theorem Ring.encode_step (q : Ring α) (clear put take : Bool) (incoming resetValue : α)
    (well : q.WellFormed) :
    (q.step clear put take incoming resetValue).encode =
      q.encode.step clear put take incoming resetValue := by
  cases clear
  · simp only [step, encode, Shift.step, Bool.false_eq_true, ↓reduceIte]
    congr 1
    funext index
    simp only [advance_index, well.2, tail_index]
    rfl
  · rfl

private theorem control_step : ∀ (head tail : BitVec 1) (count : BitVec 4) (put take : Bool),
    count ≤ 2 → tail = head + count.extractLsb' 0 1 →
    (put = true → count < 2) → (take = true → count ≠ 0) →
    stepCount count put take ≤ 2 ∧
      (if put then tail + 1 else tail) =
        (if take then head + 1 else head) + (stepCount count put take).extractLsb' 0 1 := by
  decide +kernel

theorem Ring.wellFormed_clear (q : Ring α) (put take : Bool) (incoming resetValue : α) :
    (q.step true put take incoming resetValue).WellFormed := by
  change 0#4 ≤ 2 ∧ 0#1 = 0#1 + (0#4).extractLsb' 0 1
  decide +kernel

theorem Ring.wellFormed_step (q : Ring α) (clear put take : Bool) (incoming resetValue : α)
    (well : q.WellFormed) (legal : q.Legal put take) :
    (q.step clear put take incoming resetValue).WellFormed := by
  cases clear
  · exact control_step q.head q.tail q.count put take well.1 well.2 legal.1 legal.2
  · exact q.wellFormed_clear put take incoming resetValue

/-- A full queue rejects a simultaneous incoming chunk even on a pop edge. -/
theorem Ring.full_pop_blocks_push (q : Ring α) (put : Bool) (full : q.count = 2)
    (legal : q.Legal put true) : put = false := by
  cases put
  · rfl
  · have impossible : (2 : BitVec 4) < 2 := by simpa only [full] using legal.1 rfl
    exact False.elim ((by decide +kernel : ¬ (2 : BitVec 4) < 2) impossible)

/-- An empty queue still cannot supply a head on the edge of its first push. -/
theorem Ring.empty_push_blocks_pop (q : Ring α) (take : Bool) (empty : q.count = 0)
    (legal : q.Legal true take) : take = false := by
  cases take
  · rfl
  · exact False.elim (legal.2 rfl empty)

end Pinwheel.Hardware.StreamingReady.TxQueue
