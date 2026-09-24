import Pinwheel.Hardware.Storage.SramAssembly
import Pinwheel.Hardware.Storage.TiledMap

/-! Experimental extraction of the hybrid index map. Controller expressions and
all input/result adapters are reused; the emitted register list excludes map
storage, which is owned exactly once by the external tiles. -/
namespace Pinwheel.Hardware.Storage.TiledController
open Pinwheel.Hardware Pinwheel.Hardware.Storage

inductive Input (I : Nat → Type) : Nat → Type where
  | base : I w → Input I w
  | index : Bool → Input I 5

inductive Output (O : Nat → Type) : Nat → Type where
  | base : SramController.Out O w → Output O w
  | map : TiledMap.Input w → Output O w

def lift (e : Expr I R w) : Expr (Input I) R w :=
  e.bind (fun p => .input (.base p)) (.reg)

def index (b : Bool) : SramController.E 5 := SramAssembly.resolve
  (.mux (Backend.fresh SramController.selected)
    (Execution.readTree 8 (fun k => .reg (.inner (.index true k)))
      (if b then SramController.sched (Dispatch.candidateExpr true) else SramController.address0))
    (Execution.readTree 8 (fun k => .reg (.inner (.index false k)))
      (if b then SramController.sched (Dispatch.candidateExpr true) else SramController.address0)))

/-- Actual accepted upload and candidate-address computations, before sampling
or any package adapter is lifted by `SramAssembly.chipExpr`. -/
def mapExpr : {w : Nat} → TiledMap.Input w → SramController.E w
  | _, .write => SramController.push
  | _, .writeBank => .inv (.reg (.inner (.control .active)))
  | _, .cursor => SramController.cursor
  | _, .data => .slice 0 5 (by decide) (.input (.base .data))
  | _, .readBank => SramController.selected
  | _, .pc p => SramAssembly.resolve
      (if p.val == 1 then SramController.sched (Dispatch.candidateExpr true) else SramController.address0)

/-- The original netlist owns every remaining transition. Only the two read
indices move across this interface; write priority and bank addressing stay. -/
def split (n : Netlist R (SramController.Out O) I)
    (embed : {w : Nat} → SramController.E w → Expr I R w) : Circuit (Input I) R (Output O) where
  next := fun r => lift (n.toCircuit.next r)
  output := fun {w} o => match w, o with
    | _, .map p => lift (embed (mapExpr p))
    | _, .base (.port (.address b)) =>
      .mux (lift (embed (SramController.write false)))
        (lift (embed (SramController.writeAddress false)))
        (.concat (.lit (0#3)) (.concat (lift (embed SramController.selected)) (.input (.index b))))
    | _, .base o => lift (n.toCircuit.output o)

def core := split (SramController.core false) (fun e => e)
def chip := split (SramAssembly.chip false) SramAssembly.chipExpr

def inputs (is : Array (Sigma I)) : Array (Sigma (Input I)) :=
  is.map (fun ⟨w, p⟩ => ⟨w, .base p⟩) ++ #[⟨5, .index false⟩, ⟨5, .index true⟩]

def inputLabel (label : {w : Nat} → I w → String) : {w : Nat} → Input I w → String
  | _, .base p => label p | _, .index b => if b then "map_index1" else "map_index0"

def outputs (os : Array (Sigma (SramController.Out O))) : Array (Sigma (Output O)) :=
  os.map (fun ⟨w, p⟩ => ⟨w, .base p⟩) ++ TiledMap.inputs.map (fun ⟨w, p⟩ => ⟨w, .map p⟩)

def outputLabel (label : {w : Nat} → SramController.Out O w → String) :
    {w : Nat} → Output O w → String
  | _, .base p => label p | _, .map p => "map_" ++ TiledMap.inputLabel p

def coreRegisters : Array (Sigma SramController.Register) :=
  (SramAssembly.registers false).filter fun ⟨_, r⟩ =>
    SramAssembly.coreOwner r != .indexMaps

def chipRegisters : Array (Sigma SramAssembly.FullRegister) :=
  (SramAssembly.fullRegisters false).filter fun ⟨_, r⟩ =>
    (SramAssembly.indexLocation r).isNone

def coreText : Except String String :=
  Emit.moduleText "pinwheel_tiled_core_logic" core
    (inputs (SramAssembly.inputs Loader.Machine.inputs)) coreRegisters
    (outputs (SramAssembly.outputs Loader.Machine.outputs))
    (inputLabel (SramAssembly.inputLabel Loader.Machine.inputLabel))
    (Backend.Policy.registerLabel SramAssembly.extraLabel)
    (outputLabel (SramAssembly.outputLabel Loader.Machine.outputLabel))

def chipText : Except String String :=
  Emit.moduleText "pinwheel_tiled_chip_logic" chip
    (inputs (SramAssembly.inputs Backend.Policy.chipInputs)) chipRegisters
    (outputs (SramAssembly.outputs Backend.Policy.chipOutputs))
    (inputLabel (SramAssembly.inputLabel Backend.Policy.chipInputLabel))
    SramAssembly.registerLabel
    (outputLabel (SramAssembly.outputLabel Backend.Policy.chipOutputLabel))

def closedInputs (embed : {w : Nat} → SramController.E w → Expr I R w)
    (i : Values I) (s : Values R) : Values (Input I)
  | _, .base p => i p | _, .index b => (embed (index b)).eval i s

def mapState (s : Values SramController.Register) : Values TiledMap.Register
  | _, .index b k => s (.inner (.index b k))

def mapValues (i : Values SramController.Input) (s : Values SramController.Register) :
    Values TiledMap.Input := fun p => (mapExpr p).eval i s

theorem lift_eval (e : Expr I R w) (i : Values (Input I)) (s : Values R) :
    (lift e).eval i s = e.eval (fun p => i (.base p)) s := by
  simp only [lift, Expr.eval_bind, Expr.eval]
  done

theorem split_step (n : Netlist R (SramController.Out O) I)
    (embed : {w : Nat} → SramController.E w → Expr I R w)
    (i : Values I) (s : Values R) (r : R w) :
    (split n embed).step (closedInputs embed i s) s r = n.step i s r := by
  simp only [split, Circuit.step, lift_eval, closedInputs]
  exact n.toCircuit_step i s r
  done

theorem resolve_eval (e : Expr SramController.W SramController.Register w)
    (i : Values SramController.Input) (s : Values SramController.Register) :
    (SramAssembly.resolve e).eval i s =
      e.eval (WithWire.values i (SramController.successor.eval i s)) s := by
  simp only [SramAssembly.resolve, Expr.eval_bind]
  congr 1
  funext w p
  cases p <;> rfl
  done

theorem core_observe (i : Values SramController.Input) (s : Values SramController.Register)
    (o : SramController.Out Loader.Machine.Output w) :
    core.observe (closedInputs (fun e => e) i s) s (.base o) =
      (SramController.core false).observe i s o := by
  cases o
  all_goals simp only [core, split, Circuit.observe, lift_eval, closedInputs]
  case base p => exact (SramController.core false).toCircuit_observe i s (.base p)
  case port p =>
    cases p
    all_goals simp [lift_eval, closedInputs, SramController.core, Netlist.observe,
      SramController.body, Circuit.observe, SramController.request, SramController.readAddress,
      index, resolve_eval, Expr.eval_bind, Expr.eval, Backend.fresh, Netlist.toCircuit, WithWire.values]
    all_goals done
  all_goals done

/-- The real candidate PCs and selected bank produce the indices assumed by
the controller split, for arbitrary stored bits and SRAM responses. -/
theorem map_reads (i : Values SramController.Input) (s : Values SramController.Register)
    (b : Bool) :
    TiledMap.flat.observe (mapValues i s) (mapState s) (.data (if b then 1 else 0)) =
      (index b).eval i s := by
  cases b <;> simp [TiledMap.flat, Circuit.observe, mapValues, mapState, mapExpr,
    index, resolve_eval, Execution.readTree_correct, Expr.eval, Backend.fresh_correct]
  all_goals done

open Loader

private theorem map_push_correct (i : Machine.Inputs) (s : Backend.State)
    (q : Bool → BitVec 64) (extra : Values SramController.Extra) :
    SramController.push.eval (SramController.inputValues i q) (SramController.registerValues s extra) =
      BitVec.ofBool (Loader.push (Machine.controlInput (Backend.adapt i s) s.reference.machine) s.control) := by
  simp only [SramController.push, SramController.base_eval, Backend.BankSelect.lift_correct,
    Cache.lift_correct, Machine.pushGate, Expr.eval_bind, Machine.control_correct,
    Machine.controlReg, Expr.eval, Machine.State.values, Loader.push_correct]
  rfl
  done
/-- Every external map update uses the actual admitted push, inactive bank,
cursor and payload. Rejected commands and arbitrary initial map words retain
the existing controller transition. -/
theorem map_next (i : Machine.Inputs) (s : Backend.State)
    (q : Bool → BitVec 64) (extra : Values SramController.Extra) (b : Bool) (k : BitVec 8) :
    TiledMap.flat.step
      (mapValues (SramController.inputValues i q) (SramController.registerValues s extra))
      (mapState (SramController.registerValues s extra)) (.index b k) =
      (SramController.core false).step (SramController.inputValues i q)
        (SramController.registerValues s extra) (.inner (.index b k)) := by
  simp only [SramController.core, Netlist.step, Circuit.step, SramController.body, SramController.liftW_eval]
  have h := Backend.Policy.core_step
    (SramController.successor.eval (SramController.inputValues i q)
      (SramController.registerValues s extra)) i s (.index b k)
  simp only [Circuit.step] at h
  rw [h]
  simp only [TiledMap.flat, mapValues, mapState, mapExpr, Expr.eval,
    Backend.Policy.fedNext, Backend.next, Backend.State.values, Cache.next, Machine.next]
  simp only [map_push_correct, SramController.cursor, Expr.eval, SramController.registerValues,
    SramController.inputValues, Backend.State.values, Loader.State.values, Machine.Inputs.values,
    Vector.getElem_ofFn, Store.tick, Machine.memoryInput]
  change _ = (if (Loader.push (Machine.controlInput (Backend.adapt i s) s.reference.machine) s.control &&
    (b != s.control.active) && (s.control.cursor == Store.offset (.index k))) then
      i.data.extractLsb' 0 6 else (0#1) ++ (s.indices b)[k.toNat]).extractLsb' 0 5
  have bank : ∀ a b : Bool, (BitVec.ofBool (!a) = BitVec.ofBool b) ↔ b ≠ a := by decide
  have tail : ((0#1) ++ (s.indices b)[k.toNat]).extractLsb' 0 5 = (s.indices b)[k.toNat] :=
    BitVec.extractLsb'_append_eq_right
  simp [apply_ite, bank, tail]
  split <;> simp_all
  all_goals done

end Pinwheel.Hardware.Storage.TiledController
