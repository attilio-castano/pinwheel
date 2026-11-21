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

@[noinline] private def capture (ports : Interface R) (values : Values R) : Table R :=
  ⟨ports, Vector.ofFn (fun k => (values (ports.signal k).2).toNat)⟩

private theorem capture_read (ports : Interface R) (values : Values R) :
    (fun {w} (r : R w) => (capture ports values).read r) = @values := by
  funext w r
  simp only [Table.read, capture, Vector.getElem_ofFn]
  rw [ports.signal_position r]
  simp

/-- Retain the actual typed next-register expressions across clocks. -/
structure Machine (a : Nat) where
  inputs : Interface Core.Input
  ports : Interface (Register a)
  expressions : Vector (Sigma (E a)) ports.size

@[noinline] def compile (a : Nat) (supported : a = 1 ∨ a = 2) (registered : Bool) : Machine a :=
  let core := SegmentExport.core a supported registered
  let ports := core.registers
  ⟨core.inputs, ports, Vector.ofFn fun k => ⟨_, core.circuit.next (ports.signal k).2⟩⟩

@[noinline] def Machine.edge (m : Machine a) (i : Values Core.Input) (s : Values (Register a)) :
    Table (Register a) :=
  let inputs := capture m.inputs i
  ⟨m.ports, m.expressions.map fun ⟨_, e⟩ => (e.eval (fun r => inputs.read r) s).toNat⟩

private theorem prepared_read (inputPorts : Interface Core.Input) (ports : Interface (Register a))
    (c : Circuit Core.Input (Register a) Core.Output)
    (i : Values Core.Input) (s : Values (Register a)) (r : Register a w) :
    ((Machine.mk inputPorts ports (Vector.ofFn fun k => ⟨_, c.next (ports.signal k).2⟩)).edge i s).read r = c.step i s r := by
  simp only [Table.read, Machine.edge, Vector.getElem_map]
  rw [Vector.getElem_ofFn]
  let evaluate (p : Sigma (Register a)) : Nat :=
    ((c.next p.2).eval (fun r => (capture inputPorts i).read r) s).toNat
  change BitVec.ofNat w (evaluate (ports.signal (ports.position r))) = _
  rw [ports.signal_position r]
  dsimp only [evaluate, Circuit.step]
  rw [capture_read inputPorts i]
  simp

theorem edge_read (supported : a = 1 ∨ a = 2) (registered : Bool)
    (i : Values Core.Input) (s : Values (Register a)) (r : Register a w) :
    ((compile a supported registered).edge i s).read r = (circuit a registered).step i s r :=
  prepared_read _ _ _ i s r

private def advance (m : Machine a) (registered : Bool) (host : SegmentCausal.Host H)
    (peer : SegmentCausal.Peer P) (s : SegmentCausal.State a H P) : SegmentCausal.State a H P :=
  let step := SegmentCausal.step registered host peer s
  let table := m.edge (SegmentCausal.input registered host peer s) s.core
  {step with core := fun r => table.read r}

private theorem advance_eq (supported : a = 1 ∨ a = 2) (registered : Bool) (host : SegmentCausal.Host H)
    (peer : SegmentCausal.Peer P) (s : SegmentCausal.State a H P) :
    advance (compile a supported registered) registered host peer s = SegmentCausal.step registered host peer s := by
  have same : (fun {w} (r : Register a w) =>
      ((compile a supported registered).edge (SegmentCausal.input registered host peer s) s.core).read r) =
      @(SegmentCausal.step registered host peer s).core := by
    funext w r
    exact edge_read supported registered _ s.core r
  dsimp only [advance]
  rw [same]

private def snapshots (step : SegmentCausal.State a H P → SegmentCausal.State a H P)
    (s : SegmentCausal.State a H P) : Nat → List (SegmentCausal.State a H P)
  | 0 => [s]
  | n + 1 => s :: snapshots step (step s) n

/-- A finite causal history includes both the initial state and the state
    after the final physical clock. Each snapshot uses the emitter's register
    interface and decodes to the same actual circuit state. -/
def history (supported : a = 1 ∨ a = 2) (registered : Bool) (host : SegmentCausal.Host H)
    (peer : SegmentCausal.Peer P) (s : SegmentCausal.State a H P) (n : Nat) : List (SegmentCausal.State a H P) :=
  snapshots (advance (compile a supported registered) registered host peer) s n

theorem history_at (supported : a = 1 ∨ a = 2) (registered : Bool) (host : SegmentCausal.Host H)
    (peer : SegmentCausal.Peer P) (s : SegmentCausal.State a H P) (n k : Nat) (within : k ≤ n) :
    (history supported registered host peer s n)[k]? = some (SegmentCausal.run registered host peer s k) := by
  unfold history
  induction n generalizing s k with
  | zero =>
    have zero : k = 0 := by omega
    subst k
    rfl
  | succ n ih =>
    cases k with
    | zero => rfl
    | succ k =>
      simp only [snapshots, List.getElem?_cons_succ, advance_eq, SegmentCausal.run]
      exact ih (SegmentCausal.step registered host peer s) k (Nat.le_of_succ_le_succ within)

end Pinwheel.Hardware.StreamingReady.SegmentClockTable
