import Pinwheel.Hardware.Buffered.SharedBranches

/-! Kernel-checked expression factorization and runtime correspondence. Loader
commands have different storage effects; these statements do not assert a
whole-upload trace refinement or a post-layout timing result. -/
namespace Pinwheel.Hardware.Buffered.SharedBranches
open Pinwheel.Hardware

theorem registerExpr_correct (r : Base w) (i : Values Input) (s : Values Register) :
    (registerExpr r).eval i s = expandState s r := by
  cases r <;> simp [registerExpr, expandState, expandRow, branchAt,
    Execution.readTree_correct, Expr.eval]
  done

theorem expandRow_mux (c : E 1) (x y : E 92) (i : Values Input) (s : Values Register) :
    (expandRow (.mux c x y)).eval i s =
      (Expr.mux c (expandRow x) (expandRow y)).eval i s := by
  by_cases h : c.eval i s = 1#1 <;> simp [expandRow, branchAt, Execution.readTree_correct, Expr.eval, h]
  done

theorem merge_correct (c : E 1) (t f : Rewritten w) (i : Values Input) (s : Values Register) :
    (merge c t f).expression.eval i s =
      (Expr.mux c t.expression f.expression).eval i s := by
  cases t <;> cases f <;> simp [merge, Rewritten.expression, expandRow_mux]
  done

theorem rewrite_correct (e : Reactive.E w) (i : Values Input) (s : Values Register) :
    (rewrite e).expression.eval i s = e.eval (mappedInput i s) (expandState s) := by
  induction e with
  | input p => rfl
  | reg r =>
    cases r <;> simp [rewrite, Rewritten.expression, expandState,
      expandRow, branchAt, Execution.readTree_correct, Expr.eval]
    done
  | mux c t f hc ht hf =>
    simp only [rewrite, merge_correct, Expr.eval, hc, ht, hf]
    done
  | _ => simp_all [rewrite, Rewritten.expression, Expr.eval]
  done

end Pinwheel.Hardware.Buffered.SharedBranches

namespace Pinwheel.Hardware.Buffered.SharedBranches
open Pinwheel.Hardware

theorem adapt_correct (e : Reactive.E w) (i : Values Input) (s : Values Register) :
    (adapt e).eval i s = e.eval (mappedInput i s) (expandState s) :=
  rewrite_correct e i s

theorem adapt_bind_correct (e : Reactive.E w) (i : Values Input) (s : Values Register) :
    (adapt e).eval i s = (e.bind inputExpr registerExpr).eval i s := by
  simp only [adapt_correct, Expr.eval_bind, registerExpr_correct]
  rfl
  done

def Runtime (i : Values Input) : Prop :=
  i .command ≠ 1#3 ∧ i .command ≠ 2#3 ∧ i .command ≠ 6#3

theorem mappedInput_runtime (i : Values Input) (s : Values Register) (h : Runtime i) :
    @mappedInput i s = @i := by
  funext w p
  cases p <;> simp [mappedInput, inputExpr, cmd, both, Expr.eval, h.1, h.2.1, h.2.2]
  done

theorem writing_runtime (i : Values Input) (s : Values Register) (h : Runtime i) :
    writing.eval i s = 0 := by
  simp [writing, adapt_correct, mappedInput_runtime i s h, Reactive.writing,
    Reactive.cmd, Reactive.both, Expr.eval, h.1]
  done

theorem committing_runtime (i : Values Input) (s : Values Register) (h : Runtime i) :
    committing.eval i s = 0 := by
  simp [committing, adapt_correct, mappedInput_runtime i s h, Reactive.committing,
    Reactive.cmd, Reactive.both, Expr.eval, h.2.1]
  done

theorem row_runtime (i : Values Input) (s : Values Register) (h : Runtime i) (k : BitVec 6) :
    circuit.step i s (.row k) = s (.row k) := by
  simp [Circuit.step, circuit, next, rowWriting, both, Expr.eval,
    writing_runtime i s h, committing_runtime i s h]
  done

theorem branch_runtime (i : Values Input) (s : Values Register) (h : Runtime i) (k : BitVec 4) :
    circuit.step i s (.branch k) = s (.branch k) := by
  simp [Circuit.step, circuit, next, tableWriting, both, Expr.eval, writing_runtime i s h]
  done

theorem observe_mapped (i : Values Input) (s : Values Register) (o : Output w) :
    circuit.observe i s o = Reactive.circuit.observe (mappedInput i s) (expandState s) o :=
  by cases o <;> simp [Circuit.observe, circuit, output, adapt_correct]

theorem observe_runtime (i : Values Input) (s : Values Register) (h : Runtime i) (o : Output w) :
    circuit.observe i s o = Reactive.circuit.observe i (expandState s) o := by
  rw [observe_mapped, mappedInput_runtime i s h]
  done


theorem raw_correct (e : Reactive.E w) (i : Values Input) (s : Values Register) :
    (raw e).eval i s = e.eval i (expandState s) := by
  simp only [raw, Expr.eval_bind, registerExpr_correct]
  rfl
  done

theorem step_runtime (i : Values Input) (s : Values Register) (h : Runtime i) :
    @expandState (circuit.step i s) =
      (fun {w} (r : Base w) => Reactive.circuit.step i (expandState s) r) := by
  have hw : Reactive.writing.eval i (expandState s) = 0 := by
    simpa only [writing, adapt_correct, mappedInput_runtime i s h] using writing_runtime i s h
  have hc : Reactive.committing.eval i (expandState s) = 0 := by
    simpa only [committing, adapt_correct, mappedInput_runtime i s h] using committing_runtime i s h
  funext w r
  cases r with
  | word k =>
    simp only [expandState, row_runtime i s h, branch_runtime i s h]
    simp [Circuit.step, Reactive.circuit, Reactive.next, Reactive.both, Expr.eval, hw, hc]
    rfl
    done
  | written =>
    simp [expandState, Circuit.step, circuit, next, coreNext, rowWrittenNext, resetting, raw_correct,
      writing_runtime i s h, Reactive.circuit, Reactive.next, Expr.eval, hw]
    done
  | _ =>
    simp [expandState, Circuit.step, circuit, next, coreNext, Reactive.circuit,
      adapt_correct, mappedInput_runtime i s h]
    done
  done


theorem dense_snapshot_index :
    (registers.mapIdx fun k ⟨_,r⟩ => decide (registerIndex r = k)).all id = true := by
  decide +kernel
  done

theorem declared_register_count : registers.size = 116 := by
  decide +kernel
  done

theorem declared_state_bits : (registers.map (fun ⟨w,_⟩ => w)).foldl (· + ·) 0 = 7183 := by
  decide +kernel
  done

end Pinwheel.Hardware.Buffered.SharedBranches
