import Lean
import Pinwheel.Hardware.Circuit
open Lean Meta Elab Tactic
open Pinwheel.Hardware
namespace Pinwheel.Hardware.Readback.SourceBinding

private theorem bind_band {i : Values I} {s : Values R}
    {x : Hardware.Expr I R w} {a : BitVec w}
    {y : Hardware.Expr I R w} {b : BitVec w}
    (hx : x.eval i s = a) (hy : y.eval i s = b) :
    (Hardware.Expr.band x y).eval i s = (a &&& b) := by
  simp only [Hardware.Expr.eval, hx, hy]

private theorem bind_inv {i : Values I} {s : Values R}
    {x : Hardware.Expr I R w} {a : BitVec w}
    (hx : x.eval i s = a) :
    (Hardware.Expr.inv x).eval i s = (~~~a) := by
  simp only [Hardware.Expr.eval, hx]

private theorem bind_sub {i : Values I} {s : Values R}
    {x : Hardware.Expr I R w} {a : BitVec w}
    {y : Hardware.Expr I R w} {b : BitVec w}
    (hx : x.eval i s = a) (hy : y.eval i s = b) :
    (Hardware.Expr.sub x y).eval i s = (a - b) := by
  simp only [Hardware.Expr.eval, hx, hy]

private theorem bind_equal {i : Values I} {s : Values R}
    {x : Hardware.Expr I R w} {a : BitVec w}
    {y : Hardware.Expr I R w} {b : BitVec w}
    (hx : x.eval i s = a) (hy : y.eval i s = b) :
    (Hardware.Expr.equal x y).eval i s = (BitVec.ofBool (decide (a = b))) := by
  simp only [Hardware.Expr.eval, hx, hy]

private theorem bind_zero {i : Values I} {s : Values R}
    {x : Hardware.Expr I R w} {a : BitVec w}
    (hx : x.eval i s = a) :
    (Hardware.Expr.zero x).eval i s = (BitVec.ofBool (decide (a = 0))) := by
  simp only [Hardware.Expr.eval, hx]

private theorem bind_ult {i : Values I} {s : Values R}
    {x : Hardware.Expr I R w} {a : BitVec w}
    {y : Hardware.Expr I R w} {b : BitVec w}
    (hx : x.eval i s = a) (hy : y.eval i s = b) :
    (Hardware.Expr.ult x y).eval i s = (BitVec.ofBool (decide (a.toNat < b.toNat))) := by
  simp only [Hardware.Expr.eval, hx, hy]

private theorem bind_mux {i : Values I} {s : Values R}
    {g : Hardware.Expr I R 1} {c : BitVec 1}
    {x : Hardware.Expr I R w} {a : BitVec w}
    {y : Hardware.Expr I R w} {b : BitVec w}
    (hg : g.eval i s = c) (hx : x.eval i s = a) (hy : y.eval i s = b) :
    (Hardware.Expr.mux g x y).eval i s = (if c = 1 then a else b) := by
  simp only [Hardware.Expr.eval, hg, hx, hy]

private theorem bind_concat {i : Values I} {s : Values R}
    {x : Hardware.Expr I R w} {a : BitVec w}
    {y : Hardware.Expr I R v} {b : BitVec v}
    (hx : x.eval i s = a) (hy : y.eval i s = b) :
    (Hardware.Expr.concat x y).eval i s = (a ++ b) := by
  simp only [Hardware.Expr.eval, hx, hy]

private theorem bind_slice {i : Values I} {s : Values R} (first len : Nat) (fits : first + len ≤ w) {x : Hardware.Expr I R w} {a : BitVec w}
    (hx : x.eval i s = a) :
    (Hardware.Expr.slice first len fits x).eval i s = ((a.extractLsb' first len)) := by
  simp only [Hardware.Expr.eval, hx]

/-! Bind an imported source hint to the actual typed expression one constructor
at a time. A shared proof for each pair avoids expanding the whole evaluation
tree during conversion. Every intermediate equality is checked by the kernel. -/
private def comparison (body : Lean.Expr) : MetaM Lean.Expr := do
  unless body.isAppOfArity ``BitVec.ofBool 1 do throwError "expected a Boolean comparison"
  let dec := body.appArg!
  unless dec.isAppOfArity ``Decidable.decide 2 do throwError "expected decide"
  return dec.getAppArgs[0]!

private def children (op : Name) (body : Lean.Expr) : MetaM (Name × Array Lean.Expr) := do
  let args := body.getAppArgs
  match op with
  | ``Hardware.Expr.inv => return (``bind_inv, #[args.back!])
  | ``Hardware.Expr.slice => return (``bind_slice, #[args.back!])
  | ``Hardware.Expr.band => return (``bind_band, args.extract (args.size-2) args.size)
  | ``Hardware.Expr.sub => return (``bind_sub, args.extract (args.size-2) args.size)
  | ``Hardware.Expr.concat => return (``bind_concat, args.extract (args.size-2) args.size)
  | ``Hardware.Expr.equal | ``Hardware.Expr.zero =>
    let some (_, a, b) := (← comparison body).eq? | throwError "expected an equality"
    if op == ``Hardware.Expr.zero then return (``bind_zero, #[a])
    return (``bind_equal, #[a,b])
  | ``Hardware.Expr.ult =>
    let lt := (← comparison body).getAppArgs
    return (``bind_ult, #[lt[lt.size-2]!.appArg!, lt.back!.appArg!])
  | ``Hardware.Expr.mux =>
    unless body.isAppOfArity ``ite 5 do throwError "expected a mux"
    let some (_, guard, _) := args[1]!.eq? | throwError "expected a guard comparison"
    return (``bind_mux, #[guard, args[3]!, args[4]!])
  | _ => throwError "unsupported typed expression {op}"

private partial def bindNode (src ast i s : Lean.Expr)
    (memo : IO.Ref (Std.HashMap (Lean.Expr × Lean.Expr) Lean.Expr)) : MetaM Lean.Expr := do
  if let some p := (← memo.get)[(src,ast)]? then return p
  let node ← whnf ast
  let op := node.getAppFn.constName!
  let params := (← whnf (← inferType ast)).getAppArgs
  let evalFn := mkAppN (mkConst ``Hardware.Expr.eval) ((params.push i).push s)
  let goal ← mkEq (mkApp evalFn ast) src
  let proof ←
    if op == ``Hardware.Expr.lit || op == ``Hardware.Expr.input || op == ``Hardware.Expr.reg then
      mkEqRefl src
    else do
      let some body ← unfoldDefinition? src | throwError "expected an imported source node, got {src}"
      let (lemma, sources) ← children op body
      let args := node.getAppArgs
      let mut proofs := if op == ``Hardware.Expr.slice then args.extract 3 6 else #[]
      for k in [:sources.size] do
        proofs := proofs.push (← bindNode sources[k]! args[args.size-sources.size+k]! i s memo)
      let lifted ← mkAppM lemma proofs
      if node == ast then return lifted
      let expansion ← mkAuxTheorem (← mkEq ast node) (← mkEqRefl node)
      mkEqTrans (← mkCongrArg evalFn expansion) lifted
  let checked ← mkAuxTheorem goal proof
  memo.modify (·.insert (src,ast) checked)
  return checked

/-- Prove an imported word equals evaluation of a typed circuit expression
under the specified input and register assignments. -/
elab "bind_source " source:term " to " hw:term " under " inputs:ident regs:ident : tactic =>
  withMainContext do
    let i ← getFVarFromUserName inputs.getId
    let s ← getFVarFromUserName regs.getId
    let ast ← Term.elabTerm hw none
    let src ← Term.elabTerm source none
    let proof ← bindNode src ast i s (← IO.mkRef {})
    (← getMainGoal).assign (← mkEqSymm proof)
    replaceMainGoal []

private partial def bindConjunction (goal i s : Lean.Expr)
    (memo : IO.Ref (Std.HashMap (Lean.Expr × Lean.Expr) Lean.Expr)) : MetaM Lean.Expr := do
  if goal.isAppOfArity ``And 2 then
    let args := goal.getAppArgs
    let first ← bindConjunction args[0]! i s memo
    let rest ← bindConjunction args[1]! i s memo
    return mkApp4 (mkConst ``And.intro) args[0]! args[1]! first rest
  if goal.isConstOf ``True then return mkConst ``True.intro
  let some (_, src, rhs) := goal.eq? | throwError "expected an endpoint equality"
  unless rhs.isAppOfArity ``Hardware.Expr.eval 6 do throwError "expected a typed evaluation"
  mkEqSymm (← bindNode src rhs.appArg! i s memo)

/-- Share intermediate proofs across every endpoint in a group. -/
elab "bind_sources " inputs:ident regs:ident : tactic => withMainContext do
  let i ← getFVarFromUserName inputs.getId
  let s ← getFVarFromUserName regs.getId
  let g ← getMainGoal
  let p ← bindConjunction (← g.getType) i s (← IO.mkRef {})
  g.assign p
  replaceMainGoal []

end Pinwheel.Hardware.Readback.SourceBinding
