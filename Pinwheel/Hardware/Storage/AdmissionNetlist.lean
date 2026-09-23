import Pinwheel.Hardware.NetlistInputs
import Pinwheel.Hardware.Storage.Admission
import Pinwheel.Hardware.Storage.CommandSplit

/-! Realize an admission predicate without pulling data into unrelated command
decoders. The same substitution works above and below shared netlist wires. -/
namespace Pinwheel.Hardware.Storage.Admission
open Loader

def inputMap (gate : Expr Machine.Input R 1) : InputMap Machine.Input Machine.Input R where
  input := fun p => CommandSplit.expression gate (.input p)
  literalEq := fun p v => CommandSplit.expression gate (.equal (.input p) (.lit v))
  correct := by
    intro w p v i s
    simp only [CommandSplit.expression_correct, Expr.eval]
    rfl

def netlist (gate : Expr Machine.Input R 1) (n : Netlist R O Machine.Input) :=
  (inputMap gate).netlist n

theorem inputMap_values (gate : Expr Machine.Input R 1) (A : BitVec 64 → Bool)
    (i : Machine.Inputs) (s : Values R)
    (h : gate.eval i.values s = BitVec.ofBool (A i.data)) :
    ((inputMap gate).values i.values s : Values Machine.Input) =
      (fun {_} p => (admit A i).values p) := by
  funext w p
  cases p
  all_goals simp only [InputMap.values, inputMap, CommandSplit.expression_correct,
    CommandSplit.adapted, CommandSplit.checked, Expr.eval, h, Machine.Inputs.values, admit]
  cases A i.data <;> rfl

theorem netlist_step (gate : Expr Machine.Input R 1) (A : BitVec 64 → Bool)
    (n : Netlist R O Machine.Input) (i : Machine.Inputs) (s : Values R) (r : R w)
    (h : gate.eval i.values s = BitVec.ofBool (A i.data)) :
    (netlist gate n).step i.values s r = n.step (admit A i).values s r := by
  rw [netlist, InputMap.netlist_step, inputMap_values gate A i s h]

theorem netlist_observe (gate : Expr Machine.Input R 1) (A : BitVec 64 → Bool)
    (n : Netlist R O Machine.Input) (i : Machine.Inputs) (s : Values R) (o : O w)
    (h : gate.eval i.values s = BitVec.ofBool (A i.data)) :
    (netlist gate n).observe i.values s o = n.observe (admit A i).values s o := by
  rw [netlist, InputMap.netlist_observe, inputMap_values gate A i s h]

theorem commit_structure (gate : Expr Machine.Input R 1) :
    (inputMap gate).expression (.equal (.input .command) (.lit 3)) =
      .equal (.input .command) (.lit 3) := rfl

theorem start_structure (gate : Expr Machine.Input R 1) :
    (inputMap gate).expression (.equal (.input .command) (.lit 5)) =
      .equal (.input .command) (.lit 5) := rfl

theorem component_correct (gate : Expr Machine.Input R 1) (A : BitVec 64 → Bool)
    (n : Netlist R O Machine.Input)
    (h : ∀ (i : Machine.Inputs) (s : Values R), gate.eval i.values s = BitVec.ofBool (A i.data)) :
    ((netlist gate n).componentOf Machine.Inputs.values) =
      (n.componentOf Machine.Inputs.values).precompose (admit A) := by
  simp only [Netlist.componentOf, Timed.Component.precompose, Timed.Component.mk.injEq]
  constructor <;> funext i s w p
  all_goals first
    | exact netlist_step gate A n i s p (h i s)
    | exact netlist_observe gate A n i s p (h i s)

end Pinwheel.Hardware.Storage.Admission
