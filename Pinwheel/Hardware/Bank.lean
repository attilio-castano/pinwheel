import Pinwheel.Hardware.Interface
import Std.Data.String.ToNat

namespace Pinwheel.Hardware

/-- Replicate a typed interface without forgetting the identity or width of a
member. The same construction serves input, register, and output banks. -/
inductive Bank (count : Nat) (Port : Nat → Type) : Nat → Type where
  | at (index : Fin count) : Port w → Bank count Port w

def Bank.values (v : Fin count → Values P) : Values (Bank count P)
  | _, .at k p => v k p

def Bank.position (d : Interface P) : Bank count P w → Fin (count * d.size)
  | .at k p => ⟨k.val * d.size + (d.position p).val, by
      have h₁ := Nat.add_lt_add_left (d.position p).isLt (k.val * d.size)
      have h₂ := Nat.mul_le_mul_right d.size (Nat.succ_le_of_lt k.isLt)
      simp only [Nat.succ_mul] at h₂
      omega⟩

def Bank.signal (d : Interface P) (k : Fin (count * d.size)) : Sigma (Bank count P) :=
  have hs : 0 < d.size := Nat.pos_of_ne_zero (by intro h; have := k.isLt; simp [h] at this)
  let index : Fin count := ⟨k.val / d.size, (Nat.div_lt_iff_lt_mul hs).mpr k.isLt⟩
  let p := d.signal ⟨k.val % d.size, Nat.mod_lt _ hs⟩
  ⟨p.1, .at index p.2⟩

theorem Bank.signal_position (d : Interface P) (p : Bank count P w) :
    signal d (position d p) = ⟨w, p⟩ := by
  cases p with
  | «at» k p =>
    have hs : 0 < d.size := Nat.lt_of_le_of_lt (Nat.zero_le _) (d.position p).isLt
    have hd : (k.val * d.size + (d.position p).val) / d.size = k.val := by
      simp [Nat.add_div hs, Nat.mul_div_cancel _ hs, Nat.div_eq_of_lt (d.position p).isLt,
        Nat.mod_eq_of_lt (d.position p).isLt]
    have hm : (k.val * d.size + (d.position p).val) % d.size = (d.position p).val := by
      simp [Nat.add_mod, Nat.mod_eq_of_lt (d.position p).isLt]
    unfold signal position
    have he : (⟨(k.val * d.size + (d.position p).val) % d.size, by omega⟩ : Fin d.size) =
        d.position p := Fin.ext hm
    simp only [hd]
    change (fun q : Sigma P => (⟨q.1, .at k q.2⟩ : Sigma (Bank count P)))
      (d.signal ⟨(k.val * d.size + (d.position p).val) % d.size, _⟩) = _
    rw [he, d.signal_position]
    done

theorem Bank.position_signal (d : Interface P) (k : Fin (count * d.size)) :
    position d (signal d k).2 = k := by
  apply Fin.ext
  simpa only [signal, position, d.position_signal, Nat.mul_comm] using Nat.div_add_mod k.val d.size

/-- Row-major enumeration is complete even for an empty bank or empty member
interface. Ordinal labels keep names collision-free under replication. -/
def Bank.interface (count : Nat) (d : Interface P) : Interface (Bank count P) where
  size := count * d.size
  signal := signal d
  position := position d
  signal_position := signal_position d
  label := fun p => "bank_" ++ Nat.repr (position d p).val
  unique := by
    intro a b h
    simp only [position_signal, String.append_right_inj] at h
    exact Fin.ext (Nat.repr_injective h)

/-- Independent copies preserve typed wiring and can subsequently be connected
with expression substitution. No textual name participates in the wiring. -/
def Bank.circuit (count : Nat) (c : Circuit I R O) :
    Circuit (Bank count I) (Bank count R) (Bank count O) where
  next := fun p => match p with
    | .at k p => (c.next p).bind (fun i => .input (.at k i)) (fun r => .reg (.at k r))
  output := fun p => match p with
    | .at k p => (c.output p).bind (fun i => .input (.at k i)) (fun r => .reg (.at k r))

theorem Bank.circuit_step (c : Circuit I R O) (i : Fin count → Values I)
    (s : Fin count → Values R) (k : Fin count) (r : R w) :
    (circuit count c).step (values i) (values s) (.at k r) = c.step (i k) (s k) r := by
  simp only [circuit, Circuit.step, Expr.eval_bind, Expr.eval, values]

theorem Bank.circuit_output (c : Circuit I R O) (i : Fin count → Values I)
    (s : Fin count → Values R) (k : Fin count) (o : O w) :
    (circuit count c).observe (values i) (values s) (.at k o) = c.observe (i k) (s k) o := by
  simp only [circuit, Circuit.observe, Expr.eval_bind, Expr.eval, values]

end Pinwheel.Hardware
