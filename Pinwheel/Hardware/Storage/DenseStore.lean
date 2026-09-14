import Pinwheel.Hardware.Storage.Dense

namespace Pinwheel.Hardware.Storage.Dense
open Loader

inductive Register : Nat → Type where
  | word : BitVec 6 → Register 55
  | index : BitVec 8 → Register 6
  | idle : Register 6 | last : Register 8

abbrev Image := Values Register

def reference (s : Image) : Loader.Store.Image
  | _, .word k => expand (s (.word k)) | _, .index k => s (.index k)
  | _, .idle => s .idle | _, .last => s .last

def offset : Register w → BitVec 9
  | .word k => Loader.Store.offset (.word k) | .index k => Loader.Store.offset (.index k)
  | .idle => 320 | .last => 321

def dataValue (r : Register w) (data : BitVec 64) : BitVec w := match r with
  | .word _ => compress data | .index _ => data.extractLsb' 0 6
  | .idle => data.extractLsb' 0 6 | .last => data.extractLsb' 0 8

def write (i : Loader.Store.Inputs) (s : Image) : Image := fun {_} r =>
  if i.write && i.cursor == offset r then dataValue r i.data else s r

def dataExpr (r : Register w) : Expr Loader.Store.Input Register w := match r with
  | .word _ => compressExpr (.input .data) | .index _ => .slice 0 6 (by decide) (.input .data)
  | .idle => .slice 0 6 (by decide) (.input .data) | .last => .slice 0 8 (by decide) (.input .data)

def next (r : Register w) : Expr Loader.Store.Input Register w :=
  .mux (.band (.input .write) (.equal (.input .cursor) (.lit (offset r)))) (dataExpr r) (.reg r)

set_option backward.isDefEq.respectTransparency false in
theorem next_correct (i : Loader.Store.Inputs) (s : Image) (r : Register w) :
    (next r).eval i.values s = write i s r := by
  cases r <;> simp [next, write, dataExpr, dataValue, compress_correct, Expr.eval,
    Loader.Store.Inputs.values, Bool.beq_eq_decide_eq]
  done

set_option backward.isDefEq.respectTransparency false in
theorem write_correct (i : Loader.Store.Inputs) (s : Image)
    (h : ∀ k, (i.write && i.cursor == Loader.Store.offset (.word k)) = true → Execution.validValue i.data = true) :
    (reference (write i s) : Loader.Store.Image) = (Loader.Store.tick i (reference s) : Loader.Store.Image) := by
  funext w r
  cases r with
  | word k =>
    by_cases hw : (i.write && i.cursor == Loader.Store.offset (.word k)) = true
    · simpa only [reference, write, offset, hw, if_true, dataValue, Loader.Store.tick,
        BitVec.extractLsb'_eq_self] using accepted_roundtrip i.data (h k hw)
    · simp [reference, write, offset, hw, Loader.Store.tick]
  | index _ | idle | last => rfl
  done

structure State where
  control : Loader.State
  core : Reactive.State
  images : Bool → Image

def State.reference (s : State) : Machine.State := ⟨s.control, s.core, fun b => Dense.reference (s.images b)⟩
def step (i : Machine.Inputs) (s : State) : State :=
  let n := Machine.next i s.reference
  ⟨n.control, n.core, fun b => write (Machine.memoryInput i s.reference b) (s.images b)⟩

theorem reference_step (i : Machine.Inputs) (s : State) :
    (step i s).reference = Machine.next i s.reference := by
  simp only [step, State.reference, Machine.next]
  congr 1
  funext b
  apply write_correct
  intro k hk
  simp [Machine.memoryInput] at hk
  have hp := hk.1.1
  simp [Loader.push, Loader.goodWord, hk.2, Loader.Store.offset,
    Nat.mod_eq_of_lt (by have := k.isLt; omega : k.toNat < 512), k.isLt] at hp
  exact hp.2
  done

def run (s : State) : List Machine.Inputs → State
  | [] => s | i :: rest => run (step i s) rest

theorem run_correct (s : State) (requests : List Machine.Inputs) :
    (run s requests).reference = Machine.run s.reference requests := by
  induction requests generalizing s with
  | nil => rfl
  | cons i rest ih => simpa only [run, Machine.run, reference_step] using ih (step i s)
  done

end Pinwheel.Hardware.Storage.Dense
