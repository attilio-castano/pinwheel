import Pinwheel.Hardware.Memory

/-! Digital contract for replicated single-port synchronous SRAMs.

Each physical copy accepts the same full-word write or an independent read.
Reads update Q on the edge; writes hold Q. This models the binding's mutually
exclusive read/write enables, not a simultaneous read/write mode. Array and Q
contents at power-up are arbitrary. The partial model only promises values
after a write/read establishes them; reset does not clear the physical arrays.
Macro electrical behavior and the emitted controller's addresses/enables are
separate obligations. -/
namespace Pinwheel.Hardware.Memory.Sram

structure State (a w : Nat) where
  contents : Contents a w
  q : BitVec w

def State.step (s : State a w) (write : Write a w) (address : BitVec a) : State a w :=
  ⟨s.contents.write write, if write.enable then s.q else s.contents address⟩

/-- The same write reaches every copy; reads use distinct addresses. -/
def step (i : Request a w p) (s : Fin p → State a w) : Fin p → State a w :=
  fun port => (s port).step i.write (i.read port)

structure Model (a w p : Nat) where
  contents : BitVec a → Option (BitVec w)
  q : Fin p → Option (BitVec w)

def Model.initial : Model a w p := ⟨fun _ => none, fun _ => none⟩

def Model.step (t : Model a w p) (i : Request a w p) : Model a w p :=
  ⟨fun k => if i.write.enable && i.write.address == k then some i.write.data else t.contents k,
    fun port => if i.write.enable then t.q port else t.contents (i.read port)⟩

/-- A word has been initialized by a full-word write. -/
def Model.Defined (t : Model a w p) (k : BitVec a) : Prop := ∃ v, t.contents k = some v

theorem Model.defined_step (t : Model a w p) (i : Request a w p) (k : BitVec a)
    (h : t.Defined k) : (t.step i).Defined k := by
  simp only [Defined, step]
  split <;> simp_all [Defined]
  done

theorem Model.write_defined (t : Model a w p) (i : Request a w p)
    (h : i.write.enable = true) : (t.step i).Defined i.write.address := by
  simp [Defined, step, h]

/-- Unknown cells and responses impose no equality on independent SRAM copies. -/
def Related (s : Fin p → State a w) (t : Model a w p) : Prop :=
  ∀ port, (∀ k v, t.contents k = some v → (s port).contents k = v) ∧
    (∀ v, t.q port = some v → (s port).q = v)

theorem related_step (i : Request a w p) (s : Fin p → State a w) (t : Model a w p)
    (h : Related s t) : Related (step i s) (t.step i) := by
  intro port
  constructor
  · intro k v hv
    by_cases hw : i.write.enable && i.write.address == k
    · simpa only [step, State.step, Contents.write, Model.step, hw, if_true,
        Option.some.injEq] using hv
    · simpa only [step, State.step, Contents.write, hw, Bool.false_eq_true, if_false] using
        (h port).1 k v (by simpa only [Model.step, hw, Bool.false_eq_true, if_false] using hv)
  · intro v hv
    cases hw : i.write.enable
    · simpa [step, State.step, hw] using
        (h port).1 (i.read port) v (by simpa [Model.step, hw] using hv)
    · simpa [step, State.step, hw] using
        (h port).2 v (by simpa [Model.step, hw] using hv)

/-- No power-up equality, zero-filled array, or initialized Q is assumed. -/
theorem related_initial (s : Fin p → State a w) : Related s Model.initial := by
  simp [Related, Model.initial]

/-- The relation holds after every finite request history, including partial
uploads; a read of an unwritten cell remains unspecified in the model. -/
theorem related_run (inputs : List (Request a w p))
    (s : Fin p → State a w) (t : Model a w p) (h : Related s t) :
    Related (inputs.foldl (fun s i => step i s) s) (inputs.foldl Model.step t) := by
  induction inputs generalizing s t with
  | nil => exact h
  | cons i inputs ih => exact ih _ _ (related_step i s t h)

/-- Both logical banks occupy disjoint halves of each SRAM copy. -/
def bankAddress (bank : Bool) (index : BitVec a) : BitVec (1 + a) :=
  BitVec.ofBool bank ++ index

theorem bankAddress_ne (left right : Bool) (i j : BitVec a) (h : left ≠ right) :
    bankAddress left i ≠ bankAddress right j := by
  intro heq
  have hb := congrArg (fun v : BitVec (1 + a) => v.extractLsb' a 1) heq
  simp only [bankAddress, BitVec.extractLsb'_append_eq_left] at hb
  cases left <;> cases right <;> simp_all

/-- An upload write cannot modify any word in the active bank, even when the
two copies began with unrelated, uninitialized contents. -/
theorem inactive_write_preserves_active (s : State (1 + a) w) (active : Bool)
    (index other : BitVec a) (data : BitVec w) (enable : Bool) (read : BitVec (1 + a)) :
    (s.step ⟨enable, bankAddress (!active) index, data⟩ read).contents
      (bankAddress active other) = s.contents (bankAddress active other) := by
  exact write_other _ _ _ (bankAddress_ne _ _ _ _ (by cases active <;> decide))

/-- An accepted full-word write initializes the addressed cell in every copy. -/
theorem broadcast_write (i : Request a w p) (s : Fin p → State a w)
    (hw : i.write.enable = true) (port : Fin p) :
    (step i s port).contents i.write.address = i.write.data := by
  exact write_same _ _ hw

/-- The registered response survives an unrelated upload write. -/
theorem write_holds_q (i : Request a w p) (s : Fin p → State a w)
    (hw : i.write.enable = true) (port : Fin p) : (step i s port).q = (s port).q := by
  simp [step, State.step, hw]

/-- A read of a defined address returns the promised word on the next edge. -/
theorem read_defined (i : Request a w p) (s : Fin p → State a w) (t : Model a w p)
    (h : Related s t) (hw : i.write.enable = false) (port : Fin p) (v : BitVec w)
    (hv : t.contents (i.read port) = some v) : (step i s port).q = v := by
  simpa [step, State.step, hw] using (h port).1 (i.read port) v hv

end Pinwheel.Hardware.Memory.Sram
