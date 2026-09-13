import Pinwheel.Hardware.Circuit
import Pinwheel.Engine.Proofs

namespace Pinwheel.Hardware.Countdown

inductive Input : Nat → Type where
  | reset : Input 1
  | load : Input 1
  | duration : Input 8

inductive Register : Nat → Type where
  | remaining : Register 8
  | active : Register 1

inductive Output : Nat → Type where
  | remaining : Output 8
  | active : Output 1
  | boundary : Output 1

abbrev E := Expr Input Register

def nonzero : E 1 := .inv (.zero (.reg .remaining))
def progressing : E 1 := .band (.reg .active) nonzero

/-- Boundary is consumed at the next edge, using pre-edge state; reset suppresses it.
    Loading on an expiration edge finishes the old action and starts the next one together. -/
def circuit : Circuit Input Register Output where
  next
    | .remaining => .mux (.input .reset) (.lit 0)
        (.mux (.input .load) (.input .duration)
          (.mux progressing (.sub (.reg .remaining) (.lit 1)) (.reg .remaining)))
    | .active => .mux (.input .reset) (.lit 0)
        (.mux (.input .load) (.lit 1) progressing)
  output
    | .remaining => .reg .remaining
    | .active => .reg .active
    | .boundary => .band (.inv (.input .reset)) (.band (.reg .active) (.zero (.reg .remaining)))

structure Inputs where
  reset : Bool := false
  load : Bool := false
  duration : BitVec 8 := 0
  deriving Repr

structure State where
  remaining : BitVec 8
  active : BitVec 1
  deriving DecidableEq, Repr

def Inputs.values (i : Inputs) : Values Input
  | _, .reset => BitVec.ofBool i.reset
  | _, .load => BitVec.ofBool i.load
  | _, .duration => i.duration

def State.values (s : State) : Values Register
  | _, .remaining => s.remaining
  | _, .active => s.active

def tick (i : Inputs) (s : State) : State :=
  let next : Values Register := circuit.step i.values s.values
  ⟨next .remaining, next .active⟩

def boundary (i : Inputs) (s : State) : Bool :=
  decide (circuit.observe i.values s.values .boundary = 1)

/-- Bounded reference state: the same remaining-count convention as Engine.Control.active. -/
structure Abstract where
  remaining : Fin 256
  active : Bool
  deriving DecidableEq, Repr

def embed (a : Abstract) : State := ⟨BitVec.ofFin a.remaining, BitVec.ofBool a.active⟩

def reference (i : Inputs) (a : Abstract) : Abstract :=
  if i.reset then ⟨0, false⟩
  else if i.load then ⟨i.duration.toFin, true⟩
  else if a.active then
    if h : 0 < a.remaining.val then ⟨⟨a.remaining.val - 1, by omega⟩, true⟩
    else ⟨a.remaining, false⟩
  else a

theorem tick_refines (i : Inputs) (a : Abstract) : tick i (embed a) = embed (reference i a) := by
  simp only [tick, circuit, Circuit.step, Expr.eval, progressing, nonzero, Inputs.values,
    State.values, embed, reference]
  by_cases hr : i.reset = true <;> by_cases hl : i.load = true <;> by_cases ha : a.active = true <;> simp_all
  by_cases hz : 0 < a.remaining.val <;> simp_all [BitVec.toNat_eq]
  have hn : a.remaining ≠ 0 := by omega
  simp [hn]
  omega

theorem boundary_refines (i : Inputs) (a : Abstract) :
    boundary i (embed a) = (!i.reset && a.active && decide (a.remaining.val = 0)) := by
  by_cases hr : i.reset = true <;> by_cases ha : a.active = true <;>
    simp_all [boundary, circuit, Circuit.observe, Expr.eval, Inputs.values, State.values,
      embed, BitVec.toNat_eq]
  by_cases hz : a.remaining = 0 <;> simp [hz]

def run (s : State) : Nat → State
  | 0 => s
  | n + 1 => tick {} (run s n)

/-- During an action, the structural circuit uses exactly the engine's remaining count. -/
theorem countdown (remaining : Fin 256) (n : Nat) (h : n ≤ remaining.val) :
    run (embed ⟨remaining, true⟩) n = embed ⟨⟨remaining.val - n, by omega⟩, true⟩ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [run, ih (by omega), tick_refines]
    simp [reference, show 0 < remaining.val - n by omega, Nat.sub_sub]

/-- This observation is consumed on edge n+1: the boundary edge is remaining+1, i.e. D. -/
theorem boundary_exact (remaining : Fin 256) (n : Nat) (h : n ≤ remaining.val) :
    boundary {} (run (embed ⟨remaining, true⟩) n) = decide (n = remaining.val) := by
  rw [countdown remaining n h, boundary_refines]
  simp only [Bool.not_false, Bool.true_and, decide_eq_decide]
  omega

theorem completed_exact (remaining : Fin 256) :
    run (embed ⟨remaining, true⟩) (remaining.val + 1) = embed ⟨0, false⟩ := by
  rw [run, countdown remaining remaining.val (Nat.le_refl _), tick_refines]
  simp [reference]

def project (s : Engine.State) : Abstract :=
  match s.control with
  | .active _ remaining => ⟨remaining, true⟩
  | .stopped _ => ⟨0, false⟩

/-- Direct correspondence to the existing engine, up to its next instruction entry. -/
theorem engine_countdown (p : Engine.Program) (pc : Fin 32) (remaining : Fin 256)
    (levels : Engine.Levels) (slots : Engine.Samples) (incoming : Nat → Bool)
    (n : Nat) (h : n ≤ remaining.val) :
    run (embed ⟨remaining, true⟩) n =
      embed (project (Engine.run p ⟨.active pc remaining, levels, slots⟩ incoming n)) := by
  rw [countdown remaining n h, Engine.countdown p pc remaining levels slots incoming n h]
  rfl

theorem reset_priority (s : State) (load : Bool) (duration : BitVec 8) :
    tick ⟨true, load, duration⟩ s = ⟨0, 0⟩ := rfl

theorem load_priority (s : State) (duration : BitVec 8) :
    tick ⟨false, true, duration⟩ s = ⟨duration, 1⟩ := rfl

end Pinwheel.Hardware.Countdown
