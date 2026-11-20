import Pinwheel.Hardware.StreamingReady.SegmentExport
import Pinwheel.Hardware.StreamingReady.SegmentCausal

/-! Materialize an edge's register values through the proved typed interface.
    The finite table prevents a long replay from repeatedly expanding the
    closures of all previous circuit steps. -/
namespace Pinwheel.Hardware.StreamingReady.SegmentClockTable

open Pinwheel.Hardware SegmentCore

structure Table (R : Nat → Type) where
  ports : Interface R
  values : Vector Nat ports.size

def Table.read (table : Table R) (r : R w) : BitVec w :=
  BitVec.ofNat w table.values[(table.ports.position r).val]

@[noinline] def capture (ports : Interface R) (values : Values R) : Table R :=
  ⟨ports, Vector.ofFn (fun k => (values (ports.signal k).2).toNat)⟩

theorem capture_read (ports : Interface R) (values : Values R) (r : R w) :
    (capture ports values).read r = values r := by
  simp only [Table.read, capture, Vector.getElem_ofFn]
  rw [ports.signal_position r]
  simp

def store (a : Nat) (supported : a = 1 ∨ a = 2) (registered : Bool) (s : Values (Register a)) :
    Table (Register a) :=
  capture (SegmentExport.core a supported registered).registers s

theorem store_eq (a : Nat) (supported : a = 1 ∨ a = 2) (registered : Bool)
    (s : Values (Register a)) (r : Register a w) :
    (store a supported registered s).read r = s r :=
  capture_read _ s r

def cached (supported : a = 1 ∨ a = 2) (registered : Bool) (s : SegmentCausal.State a H P) :
    SegmentCausal.State a H P :=
  let table := store a supported registered s.core
  {s with core := fun r => table.read r}

theorem cached_eq (supported : a = 1 ∨ a = 2) (registered : Bool) (s : SegmentCausal.State a H P) :
    cached supported registered s = s := by
  have eq : (fun {w} (r : Register a w) => (store a supported registered s.core).read r) = @s.core := by
    funext w r
    exact store_eq a supported registered s.core r
  simp only [cached, eq]

/-- A finite causal history includes both the initial state and the state
    after the final physical clock. Each snapshot uses the emitter's register
    interface and decodes to the same actual circuit state. -/
def history (supported : a = 1 ∨ a = 2) (registered : Bool) (host : SegmentCausal.Host H)
    (peer : SegmentCausal.Peer P) (s : SegmentCausal.State a H P) : Nat → List (SegmentCausal.State a H P)
  | 0 => [s]
  | n + 1 => s :: history supported registered host peer (cached supported registered (SegmentCausal.step registered host peer s)) n

theorem history_at (supported : a = 1 ∨ a = 2) (registered : Bool) (host : SegmentCausal.Host H)
    (peer : SegmentCausal.Peer P) (s : SegmentCausal.State a H P) (n k : Nat) (within : k ≤ n) :
    (history supported registered host peer s n)[k]? = some (SegmentCausal.run registered host peer s k) := by
  induction n generalizing s k with
  | zero =>
    have zero : k = 0 := by omega
    subst k
    rfl
  | succ n ih =>
    cases k with
    | zero => rfl
    | succ k =>
      simp only [history, List.getElem?_cons_succ, cached_eq, SegmentCausal.run]
      exact ih (SegmentCausal.step registered host peer s) k (Nat.le_of_succ_le_succ within)

end Pinwheel.Hardware.StreamingReady.SegmentClockTable
