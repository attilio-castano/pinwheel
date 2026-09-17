import Pinwheel.Hardware.Storage.BackendNetlist

namespace Pinwheel.Hardware.Storage.Backend.Readback
open Loader

def selected : E 1 := lift (Cache.liftExpr Machine.selectedGate)
def target : E 8 := lift Cache.target

inductive ReadInput : Nat → Type where
  | selected : ReadInput 1
  | target : ReadInput 8

def readInputs (selection : BitVec 1) (address : BitVec 8) : Values ReadInput
  | _, .selected => selection
  | _, .target => address

def word (b : Bool) (k : BitVec 6) : Expr I Register 64 :=
  if k.toNat < 32 then Dense.expandExpr (.reg (.word b (k.extractLsb' 0 5))) else .lit 4

def index (b : Bool) (k : BitVec 8) : Expr ReadInput Register 6 :=
  .concat (.lit (0#1)) (.reg (.index b k) : Expr ReadInput Register 5)

def indexRead : Expr ReadInput Register 6 :=
  Execution.readTree 8 (fun k => .mux (.input .selected) (index true k) (index false k))
    (.input .target)

def indexAddress : E 6 := indexRead.bind
  (fun p => match p with | .selected => selected | .target => target)
  (fun r => .reg r)

inductive WordInput : Nat → Type where
  | selected : WordInput 1
  | address : WordInput 6

def wordInputs (selection : BitVec 1) (address : BitVec 6) : Values WordInput
  | _, .selected => selection
  | _, .address => address

def wordRead : Expr WordInput Register 64 :=
  Execution.readTree 6 (fun k => .mux (.input .selected) (word true k) (word false k))
    (.input .address)

theorem word_eval (i : Values I) (s : State) (b : Bool) (k : BitVec 6) :
    (word b k).eval i s.values = s.reference.machine.memory b (.word k) := by
  by_cases h : k.toNat < 32 <;>
    simp [word, h, Dense.expand_correct, Expr.eval, State.values, State.reference,
      State.small, Small.State.reference]
  simp [Nat.mod_eq_of_lt h]
  done

theorem index_eval (i : Values ReadInput) (s : State) (b : Bool) (k : BitVec 8) :
    (index b k).eval i s.values = s.reference.machine.memory b (.index k) := by
  rfl

theorem read_correct (i : Machine.Inputs) (s : State) :
    wordRead.eval (wordInputs (selected.eval i.values s.values)
      (indexRead.eval (readInputs (selected.eval i.values s.values) (target.eval i.values s.values)) s.values)) s.values =
      successor.eval i.values s.values := by
  simp only [wordRead, indexRead, Execution.readTree_correct, Expr.eval, readInputs, wordInputs,
    word_eval, index_eval, selected, target,
    lift_correct, Cache.lift_correct, Machine.selected_correct, Cache.target_correct,
    successor_correct]
  cases hs : Machine.selected (adapt i s) s.reference.machine <;>
    simp [Cache.feed, Reactive.Fetch.resolve, Loader.Store.read, hs]
  done

end Pinwheel.Hardware.Storage.Backend.Readback
