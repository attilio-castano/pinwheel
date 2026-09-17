import Pinwheel.Hardware.Timed

/-! A memory as a contract: one write port, `p` read ports, and a read latency
`ℓ`. Every implementation — flip-flops, latches, a macro — is judged against
`spec a w p ℓ`; every machine that uses storage is written against a latency,
not against an implementation. Reads observe the pre-edge contents
("read first"); a write and a read of the same word on one edge see the old word. -/
namespace Pinwheel.Hardware.Memory

/-- One word per `a`-bit address. -/
abbrev Contents (a w : Nat) := BitVec a → BitVec w

/-- The write port on one edge. -/
structure Write (a w : Nat) where
  enable : Bool
  address : BitVec a
  data : BitVec w

def Contents.write (c : Contents a w) (req : Write a w) : Contents a w :=
  fun k => if req.enable && req.address == k then req.data else c k

@[simp] theorem write_same (c : Contents a w) (req : Write a w) (h : req.enable = true) :
    c.write req req.address = req.data := by
  simp [Contents.write, h]

@[simp] theorem write_other (c : Contents a w) (req : Write a w) (k : BitVec a)
    (h : req.address ≠ k) : c.write req k = c k := by
  simp [Contents.write, h]

@[simp] theorem write_disabled (c : Contents a w) (req : Write a w) (h : req.enable = false) :
    c.write req = c := by
  funext k
  simp [Contents.write, h]

/-- Everything a memory sees on one edge: the write port and every read address. -/
structure Request (a w p : Nat) where
  write : Write a w
  read : Fin p → BitVec a

/-- The words behind the read ports, as a read of `c` at the request's addresses. -/
def Contents.reads (c : Contents a w) (i : Request a w p) : Fin p → BitVec w :=
  fun port => c (i.read port)

/-- Contents plus `ℓ` outstanding read results per port, oldest first. -/
structure State (a w p ℓ : Nat) where
  contents : Contents a w
  pending : Fin ℓ → Fin p → BitVec w

/-- The result a read port shows on an edge: with no latency the read of the
current contents, otherwise the oldest outstanding result. -/
def State.observe (s : State a w p ℓ) (i : Request a w p) : Fin p → BitVec w :=
  if h : 0 < ℓ then s.pending ⟨0, h⟩ else s.contents.reads i

/-- The next state: the write lands, and this edge's read enters the pipeline
behind the results still outstanding. -/
def State.step (s : State a w p ℓ) (i : Request a w p) : State a w p ℓ where
  contents := s.contents.write i.write
  pending := fun k => if h : k.val + 1 < ℓ then s.pending ⟨k.val + 1, h⟩ else s.contents.reads i

/-- The contract. -/
def spec (a w p ℓ : Nat) : Timed.Component (Request a w p) (State a w p ℓ) (Fin p → BitVec w) :=
  ⟨fun i s => s.step i, fun i s => s.observe i⟩

theorem spec_step (i : Request a w p) (s : State a w p ℓ) : (spec a w p ℓ).step i s = s.step i := rfl
theorem spec_observe (i : Request a w p) (s : State a w p ℓ) :
    (spec a w p ℓ).observe i s = s.observe i := rfl

/-- Without latency a read is combinational on the pre-edge contents. -/
theorem observe_zero (s : State a w p 0) (i : Request a w p) : s.observe i = s.contents.reads i := by
  simp [State.observe]

/-- With latency the observation does not depend on this edge's request at all. -/
theorem observe_registered (s : State a w p (ℓ + 1)) (i j : Request a w p) :
    s.observe i = s.observe j := by
  simp [State.observe]

/-! ## Registering an output

An output register on any component adds one cycle of latency. Applied to a
memory of latency `ℓ` it is a memory of latency `ℓ + 1`; this is the law an
implementation with a registered read port appeals to. -/

/-- A component followed by an output register that holds its last observation. -/
def registered (c : Timed.Component I S O) : Timed.Component I (S × O) O :=
  ⟨fun i s => (c.step i s.1, c.observe i s.1), fun _ s => s.2⟩

/-- The registered memory of latency `ℓ` refines the memory of latency `ℓ + 1`:
the output register holds the oldest outstanding result. -/
def registered_refines (a w p ℓ : Nat) :
    Timed.Refinement (registered (spec a w p ℓ)) (spec a w p (ℓ + 1)) where
  Rel := fun s t => t.contents = s.1.contents ∧ ∀ k : Fin (ℓ + 1),
    t.pending k = if h : 0 < k.val then s.1.pending ⟨k.val - 1, by omega⟩ else s.2
  step := by
    intro i s t ⟨hc, hp⟩
    refine ⟨by simp [registered, spec, State.step, hc], ?_⟩
    intro k
    simp only [registered, spec, State.step, State.observe, hp, hc]
    by_cases hk : 0 < k.val
    · by_cases h : k.val + 1 < ℓ + 1
      · have hl : k.val < ℓ := by omega
        simp [hk, h, hl, show k.val - 1 + 1 = k.val by omega]
      · simp [hk, h, show ¬ k.val - 1 + 1 < ℓ by omega]
    · have hz : k.val = 0 := by omega
      by_cases h : 0 < ℓ
      · simp [hz, h]
      · simp [hz, h]
  observe := by
    intro i s t ⟨hc, hp⟩
    funext port
    simp [registered, spec, State.observe, hp]

/-- Contents are the same whatever the latency: only the reads move. -/
theorem step_contents (s : State a w p ℓ) (i : Request a w p) :
    (s.step i).contents = s.contents.write i.write := rfl

/-- A read of a word no write has touched since it was issued returns that word;
this is the form a machine uses when its writes never target the bank it runs. -/
theorem read_untouched (s : State a w p 1) (i j : Request a w p) (port : Fin p)
    (untouched : i.write.enable = false ∨ i.write.address ≠ i.read port) :
    (s.step i).observe j port = (s.step i).contents (i.read port) := by
  have obs : (s.step i).observe j port = s.contents (i.read port) := by
    simp [State.observe, State.step, Contents.reads]
  rw [obs, step_contents]
  rcases untouched with h | h
  · rw [write_disabled _ _ h]
  · rw [write_other _ _ _ h]

end Pinwheel.Hardware.Memory
