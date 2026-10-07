import Pinwheel.Hardware.Buffered.SramState
import Pinwheel.Hardware.Buffered.SharedBranchProofs
import Lean

/-! Execution correspondence at the resident binary-image boundary. The proof
compares actual typed SRAM equations with the existing full-register reactive
engine; it does not assert correctness of a source-language compiler. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
namespace Pinwheel.Hardware.Buffered.SramExecution
open Pinwheel.Hardware

def withWords (s : Values Reactive.Register) (words : Memory.Contents 6 144) :
    Values Reactive.Register
  | _, .word k => words k
  | _, r => s r

def nonword : Reactive.Register w → Prop
  | .word _ => False
  | _ => True

inductive Supported : Reactive.E w → Prop where
  | entry : Supported Reactive.entryRecord
  | input (p : Reactive.Input w) : Supported (.input p)
  | reg (r : Reactive.Register w) (h : nonword r) : Supported (.reg r)
  | lit (v : BitVec w) : Supported (.lit v)
  | concat : Supported x → Supported y → Supported (.concat x y)
  | inv : Supported x → Supported (.inv x)
  | band : Supported x → Supported y → Supported (.band x y)
  | sub : Supported x → Supported y → Supported (.sub x y)
  | slice : Supported x → Supported (.slice start len fits x)
  | equal : Supported x → Supported y → Supported (.equal x y)
  | ult : Supported x → Supported y → Supported (.ult x y)
  | zero : Supported x → Supported (.zero x)
  | mux : Supported c → Supported t → Supported f → Supported (.mux c t f)

theorem supported_congr (i : Values Reactive.Input) (s : Values Reactive.Register)
    (left right : Memory.Contents 6 144)
    (he : Reactive.entryRecord.eval i (withWords s left) =
      Reactive.entryRecord.eval i (withWords s right))
    (h : Supported e) : e.eval i (withWords s left) = e.eval i (withWords s right) := by
  induction h
  case entry => exact he
  case reg r hn => cases r <;> simp_all [nonword, withWords, Expr.eval]
  all_goals simp_all only [Expr.eval]
  done

theorem supported_pack (f : Fin n → Reactive.E 1) (hf : ∀ k, Supported (f k)) :
    Supported (Reactive.pack f) := by
  induction n
  case zero => exact Supported.lit _
  case succ n ih =>
    cases n
    case zero => exact hf 0
    case succ n => exact Supported.concat (ih _ (fun k => hf k.succ)) (hf 0)
  done

namespace SupportProof
open Lean Meta Elab Tactic

/-- Proof construction caches shared expression constants; the resulting
ordinary constructor proof is checked by Lean's kernel. -/
private partial def build (e : Lean.Expr) :
    StateT (Std.HashMap Lean.Expr Lean.Expr) MetaM Lean.Expr := do
  if let some proof := (← get)[e]? then return proof
  let proof ← if e.isConstOf ``Reactive.entryRecord then
      pure (mkConst ``Supported.entry)
    else do
      let reduced ← whnf e
      let args := reduced.getAppArgs
      let fn := reduced.getAppFn.constName!
      if fn == ``Expr.input then return ← mkAppM ``Supported.input #[args.back!]
      else if fn == ``Expr.reg then
        let r := args.back!
        let premise ← whnf (← mkAppM ``nonword #[r])
        unless premise.isConstOf ``True do throwError "unprotected word register {r}"
        return ← mkAppM ``Supported.reg #[r, mkConst ``True.intro]
      else if fn == ``Expr.lit then return ← mkAppM ``Supported.lit #[args.back!]
      else if fn == ``Expr.concat then
        return ← mkAppM ``Supported.concat #[← build args[args.size-2]!, ← build args.back!]
      else if fn == ``Expr.inv then return ← mkAppM ``Supported.inv #[← build args.back!]
      else if fn == ``Expr.band then
        return ← mkAppM ``Supported.band #[← build args[args.size-2]!, ← build args.back!]
      else if fn == ``Expr.sub then
        return ← mkAppM ``Supported.sub #[← build args[args.size-2]!, ← build args.back!]
      else if fn == ``Expr.slice then return ← mkAppOptM ``Supported.slice #[none, some args.back!, some args[args.size-4]!, some args[args.size-3]!, some args[args.size-2]!, some (← build args.back!)]
      else if fn == ``Expr.equal then
        return ← mkAppM ``Supported.equal #[← build args[args.size-2]!, ← build args.back!]
      else if fn == ``Expr.ult then
        return ← mkAppM ``Supported.ult #[← build args[args.size-2]!, ← build args.back!]
      else if fn == ``Expr.zero then return ← mkAppM ``Supported.zero #[← build args.back!]
      else if fn == ``Expr.mux then return ← mkAppM ``Supported.mux #[← build args[args.size-3]!, ← build args[args.size-2]!, ← build args.back!]
      else throwError "unsupported reactive expression {e}"
  modify fun cache => cache.insert e proof
  return proof

elab "support_expr" : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    let e := (← goal.getType).getAppArgs.back!
    let proof ← (build e).run' {}
    goal.assign proof
  replaceMainGoal []

end SupportProof

theorem supported_next (r : Reactive.Register w) (hn : nonword r) :
    Supported (Reactive.next r) := by
  cases r
  case word k => exact False.elim hn
  all_goals support_expr
  done

theorem supported_output (o : Reactive.Output w) :
    Supported (Reactive.circuit.output o) := by
  cases o
  all_goals support_expr
  done

theorem reactive_next_congr (i : Values Reactive.Input) (s : Values Reactive.Register)
    (left right : Memory.Contents 6 144)
    (he : Reactive.entryRecord.eval i (withWords s left) =
      Reactive.entryRecord.eval i (withWords s right)) (r : Reactive.Register w)
    (hn : nonword r) :
    Reactive.circuit.step i (withWords s left) r =
      Reactive.circuit.step i (withWords s right) r :=
  supported_congr i s left right he (supported_next r hn)

theorem reactive_observe_congr (i : Values Reactive.Input) (s : Values Reactive.Register)
    (left right : Memory.Contents 6 144)
    (he : Reactive.entryRecord.eval i (withWords s left) =
      Reactive.entryRecord.eval i (withWords s right)) (o : Reactive.Output w) :
    Reactive.circuit.observe i (withWords s left) o =
      Reactive.circuit.observe i (withWords s right) o :=
  supported_congr i s left right he (supported_output o)

theorem starting_withWords (i : Values Reactive.Input) (s : Values Reactive.Register)
    (words : Memory.Contents 6 144) :
    Reactive.starting.eval i (withWords s words) = Reactive.starting.eval i s := rfl

theorem entering_withWords (i : Values Reactive.Input) (s : Values Reactive.Register)
    (words : Memory.Contents 6 144) :
    Reactive.entering.eval i (withWords s words) = Reactive.entering.eval i s := rfl

theorem entryPC_withWords (i : Values Reactive.Input) (s : Values Reactive.Register)
    (words : Memory.Contents 6 144) :
    Reactive.entryPC.eval i (withWords s words) = Reactive.entryPC.eval i s := rfl

theorem branchBit_withWords (i : Values Reactive.Input) (s : Values Reactive.Register)
    (words : Memory.Contents 6 144) :
    Reactive.branchBit.eval i (withWords s words) = Reactive.branchBit.eval i s := rfl


end Pinwheel.Hardware.Buffered.SramExecution
