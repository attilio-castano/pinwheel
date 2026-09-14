import Pinwheel.Hardware.Storage.Capacity

namespace Pinwheel.Hardware.Storage.Small
open Loader

abbrev Input := Machine.Input
abbrev Output := Machine.Output

inductive Register : Nat → Type where
  | control : Loader.Register w → Register w
  | core : Reactive.Register w → Register w
  | word : Bool → BitVec 5 → Register 64
  | index : Bool → BitVec 8 → Register 5
  | idle : Bool → Register 6
  | last : Bool → Register 8

structure State where
  control : Loader.State
  core : Reactive.State
  words : Bool → Vector (BitVec 64) 32
  indices : Bool → Vector (BitVec 5) 256
  idle : Bool → BitVec 6
  last : Bool → BitVec 8

def State.values (s : State) : Values Register
  | _, .control r => s.control.values r | _, .core r => s.core.values r
  | _, .word b k => (s.words b)[k.toNat] | _, .index b k => (s.indices b)[k.toNat]
  | _, .idle b => s.idle b | _, .last b => s.last b

def State.reference (s : State) : Machine.State :=
  ⟨s.control, s.core, fun b {_} r => match r with
    | .word k => if h : k.toNat < 32 then (s.words b)[k.toNat] else 4
    | .index k => (0#1) ++ (s.indices b)[k.toNat]
    | .idle => s.idle b | .last => s.last b⟩

def project (s : Machine.State) : State :=
  ⟨s.control, s.core,
    fun b => Vector.ofFn fun k => s.memory b (.word (BitVec.ofNat 6 k.val)),
    fun b => Vector.ofFn fun k => (s.memory b (.index (BitVec.ofFin k))).extractLsb' 0 5,
    fun b => s.memory b .idle, fun b => s.memory b .last⟩

/-- Keep the 322-word host stream: upper dictionary slots are mandatory halt padding.
This permits direct trace comparison while physically retaining only 32 words. -/
def capacity (cursor : BitVec 9) (data : BitVec 64) : Bool :=
  if cursor.toNat < 32 then true
  else if cursor.toNat < 64 then data == 4
  else if cursor.toNat < 320 then data.toNat < 32
  else true

def adapt (i : Machine.Inputs) (s : State) : Machine.Inputs :=
  {i with command := if i.command == 2 && !capacity s.control.cursor i.data then 6 else i.command}

def next (i : Machine.Inputs) (s : State) : State := project (Machine.next (adapt i s) s.reference)

abbrev E := Expr Input Register

def logical : {w : Nat} → Machine.Register w → E w
  | _, .control r => .reg (.control r) | _, .core r => .reg (.core r)
  | _, .memory b (.word k) => if k.toNat < 32 then .reg (.word b (k.extractLsb' 0 5)) else .lit 4
  | _, .memory b (.index k) => .concat (.lit (0#1)) (.reg (.index b k) : E 5)
  | _, .memory b .idle => .reg (.idle b) | _, .memory b .last => .reg (.last b)

def capacityGate : E 1 :=
  .mux (.ult (.reg (.control .cursor)) (.lit 32)) (.lit 1)
    (.mux (.ult (.reg (.control .cursor)) (.lit 64)) (.equal (.input .data) (.lit 4))
      (.mux (.ult (.reg (.control .cursor)) (.lit 320)) (.ult (.input .data) (.lit 32)) (.lit 1)))

def inputs : {w : Nat} → Input w → E w
  | _, .command => .mux (.band (.equal (.input .command) (.lit 2)) (.inv capacityGate)) (.lit 6) (.input .command)
  | _, r => .input r

def circuit : Circuit Input Register Output where
  next := fun r => match r with
    | .control r => (Machine.circuit.next (.control r)).bind inputs logical
    | .core r => (Machine.circuit.next (.core r)).bind inputs logical
    | .word b k => (Machine.circuit.next (.memory b (.word (BitVec.ofNat 6 k.toNat)))).bind inputs logical
    | .index b k => .slice 0 5 (by decide) ((Machine.circuit.next (.memory b (.index k))).bind inputs logical)
    | .idle b => (Machine.circuit.next (.memory b .idle)).bind inputs logical
    | .last b => (Machine.circuit.next (.memory b .last)).bind inputs logical
  output := fun o => (Machine.circuit.output o).bind inputs logical

set_option backward.isDefEq.respectTransparency false in
theorem capacity_correct (i : Machine.Inputs) (s : State) :
    capacityGate.eval i.values s.values = BitVec.ofBool (capacity s.control.cursor i.data) := by
  by_cases h32 : s.control.cursor.toNat < 32 <;>
    by_cases h64 : s.control.cursor.toNat < 64 <;>
    by_cases h320 : s.control.cursor.toNat < 320 <;>
    simp [capacityGate, Expr.eval, State.values, Loader.State.values, Machine.Inputs.values,
      capacity, Bool.beq_eq_decide_eq, h32, h64, h320]
  done

theorem logical_correct (i : Machine.Inputs) (s : State) (r : Machine.Register w) :
    (logical r).eval i.values s.values = s.reference.values r := by
  cases r with
  | control r => rfl
  | core r => rfl
  | memory b r =>
    cases r <;> simp [logical, Expr.eval, State.values, State.reference, Machine.State.values]
    split <;> simp_all [Expr.eval, State.values, BitVec.extractLsb'_toNat, Nat.mod_eq_of_lt]
  done

set_option backward.isDefEq.respectTransparency false in
theorem inputs_correct (i : Machine.Inputs) (s : State) (p : Input w) :
    (inputs p).eval i.values s.values = (adapt i s).values p := by
  cases p <;> simp [inputs, Expr.eval, capacity_correct, Machine.Inputs.values, adapt, Bool.beq_eq_decide_eq]
  done

set_option backward.isDefEq.respectTransparency false in
theorem next_correct (i : Machine.Inputs) (s : State) (r : Register w) :
    circuit.step i.values s.values r = (next i s).values r := by
  have h {n} (p : Machine.Register n) := Machine.next_correct (adapt i s) s.reference p
  simp only [Circuit.step] at h
  cases r <;> simp only [circuit, Circuit.step, Expr.eval, Expr.eval_bind, inputs_correct,
    logical_correct, next, project, State.values, Vector.getElem_ofFn]
  all_goals first | exact h _ | exact congrArg (BitVec.extractLsb' 0 5) (h _)
  done

def Fits (s : Machine.State) : Prop :=
  (∀ b k, 32 ≤ k.toNat → s.memory b (.word k) = 4) ∧
  (∀ b k, (s.memory b (.index k)).toNat < 32)

theorem reference_fits (s : State) : Fits s.reference := by
  constructor
  · intro b k hk
    simp [State.reference, show ¬ k.toNat < 32 by omega]
  · intro b k
    simpa only [State.reference, BitVec.toNat_append, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod,
      Nat.zero_shiftLeft, Nat.zero_or] using (s.indices b)[k.toNat].isLt
  done

theorem reference_project (s : Machine.State) (h : Fits s) : (project s).reference = s := by
  cases s with
  | mk control core memory =>
    simp only [project, State.reference]
    congr 1
    funext b w r
    cases r with
    | word k =>
      simp only [Vector.getElem_ofFn]
      split
      · congr 2
        apply BitVec.eq_of_toNat_eq
        simp
      · exact (h.1 b k (by omega)).symm
    | index k =>
      apply BitVec.eq_of_toNat_eq
      simp only [Vector.getElem_ofFn, BitVec.toNat_append, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod,
        Nat.zero_shiftLeft, Nat.zero_or, BitVec.extractLsb'_toNat, Nat.shiftRight_zero]
      exact Nat.mod_eq_of_lt (h.2 b k)
    | idle => rfl
    | last => rfl
  done

theorem push_capacity (i : Machine.Inputs) (s : State)
    (hp : Loader.push (Machine.controlInput (adapt i s) s.reference) s.control = true) :
    capacity s.control.cursor i.data = true := by
  by_cases hc : capacity s.control.cursor i.data = true
  · exact hc
  · simp [Loader.push, Machine.controlInput, adapt, hc] at hp
    split at hp <;> simp_all
  done

theorem next_fits (i : Machine.Inputs) (s : State) :
    Fits (Machine.next (adapt i s) s.reference) := by
  have hf := reference_fits s
  constructor
  · intro b k hk
    simp only [Machine.next, Store.tick]
    split
    · rename_i hw
      have hp : Loader.push (Machine.controlInput (adapt i s) s.reference) s.control = true := by
        simp [Machine.memoryInput] at hw
        exact hw.1.1
      have hc := push_capacity i s hp
      simp [Machine.memoryInput, Store.offset] at hw
      have he : s.control.cursor.toNat = k.toNat := by
        have he := congrArg BitVec.toNat hw.2
        simpa [State.reference, Nat.mod_eq_of_lt (by have := k.isLt; omega : k.toNat < 512)] using he
      simp [capacity, he, show ¬ k.toNat < 32 by omega, k.isLt] at hc
      simpa [Machine.memoryInput, adapt] using hc
    · exact hf.1 b k hk
  · intro b k
    simp only [Machine.next, Store.tick]
    split
    · rename_i hw
      have hp : Loader.push (Machine.controlInput (adapt i s) s.reference) s.control = true := by
        simp [Machine.memoryInput] at hw
        exact hw.1.1
      have hc := push_capacity i s hp
      simp [Machine.memoryInput, Store.offset] at hw
      have he : s.control.cursor.toNat = 64 + k.toNat := by
        have he := congrArg BitVec.toNat hw.2
        simpa [State.reference, Nat.mod_eq_of_lt (by have := k.isLt; omega : 64 + k.toNat < 512)] using he
      simp [capacity, he, show ¬ 64 + k.toNat < 32 by omega,
        show ¬ 64 + k.toNat < 64 by omega, show 64 + k.toNat < 320 by have := k.isLt; omega] at hc
      simp [Machine.memoryInput, adapt, BitVec.extractLsb'_toNat, Nat.mod_eq_of_lt (by omega : i.data.toNat < 64), hc]
    · exact hf.2 b k
  done

theorem reference_next (i : Machine.Inputs) (s : State) :
    (next i s).reference = Machine.next (adapt i s) s.reference := by
  exact reference_project _ (next_fits i s)
  done

def run (s : State) : List Machine.Inputs → State
  | [] => s | i :: rest => run (next i s) rest

def circuitRun (v : Values Register) : List Machine.Inputs → Values Register
  | [] => v | i :: rest => circuitRun (circuit.step i.values v) rest

theorem run_correct (s : State) (requests : List Machine.Inputs) :
    (circuitRun s.values requests : Values Register) = (fun {_} r => (run s requests).values r) := by
  induction requests generalizing s with
  | nil => rfl
  | cons i rest ih =>
    have h : (circuit.step i.values s.values : Values Register) = (fun {_} r => (next i s).values r) :=
      funext fun _ => funext fun r => next_correct i s r
    simpa only [circuitRun, h, run] using ih (next i s)
  done

end Pinwheel.Hardware.Storage.Small
