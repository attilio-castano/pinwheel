import Pinwheel.Hardware.Storage.PairedValidation

/-! Interpretation of the exact paired graph used by the emitter. Shared
combinational nodes all read one pre-edge register snapshot. This file connects
the checked graph constructor to that interpretation; it assumes no memory
behavior, initialized state or execution-image correctness. -/
namespace Pinwheel.Hardware.Storage.PairedSemantics
open PairedController
open SramController (Reads Out)

deriving instance ReflBEq, LawfulBEq for Computation

abbrev Environment := Computation → BitVec 64

def graphValues (i : Values Input) (env : Environment) : Values GraphInput
  | _, .base p => i (.base p)
  | _, .q b => i (.q b)
  | _, .node n => env n

def evaluate (i : Values Input) (s : Values Register) :
    Environment → List (Computation × E 64) → Environment
  | env, [] => env
  | env, (name, e) :: rest =>
    evaluate i s (fun n => if n == name then e.eval (graphValues i env) s else env n) rest

def inputs (nodes : List (Computation × E 64)) (i : Values Input)
    (s : Values Register) : Values GraphInput :=
  graphValues i (evaluate i s (fun _ => 0) nodes)

theorem eval_congr (e : E w) (i : Values Input) (s : Values Register)
    (a b : Environment) (h : ∀ n ∈ references e, a n = b n) :
    e.eval (graphValues i a) s = e.eval (graphValues i b) s := by
  induction e <;> simp_all [references, Expr.eval, graphValues]
  case input p => cases p <;> simp_all [references]

/-- Fresh names and only backward references make every final node satisfy its
own equation, despite evaluation proceeding in order. -/
def ordered (seen : List Computation) : List (Computation × E 64) → Bool
  | [] => true
  | (name, e) :: rest => !seen.contains name &&
      (references e).all seen.contains && ordered (name :: seen) rest

theorem evaluate_preserves_seen (nodes : List (Computation × E 64))
    (seen : List Computation) (h : ordered seen nodes = true)
    (i : Values Input) (s : Values Register) (env : Environment)
    (name : Computation) (hn : name ∈ seen) : evaluate i s env nodes name = env name := by
  induction nodes generalizing seen env with
  | nil => rfl
  | cons head rest ih =>
    simp only [ordered, Bool.and_eq_true, Bool.not_eq_true', List.contains_eq_mem,
      decide_eq_false_iff_not] at h
    rw [evaluate, ih (head.1 :: seen) h.2 _ (List.mem_cons_of_mem _ hn)]
    simp only [beq_iff_eq, if_neg (fun he : name = head.1 => h.1.1 (he ▸ hn))]

theorem evaluate_equations (nodes : List (Computation × E 64))
    (seen : List Computation) (h : ordered seen nodes = true)
    (i : Values Input) (s : Values Register) (env : Environment)
    (name : Computation) (e : E 64) (hn : (name, e) ∈ nodes) :
    evaluate i s env nodes name = e.eval (graphValues i (evaluate i s env nodes)) s := by
  induction nodes generalizing seen env with
  | nil => cases hn
  | cons head rest ih =>
    have hs := h
    simp only [ordered, Bool.and_eq_true, Bool.not_eq_true', List.contains_eq_mem,
      decide_eq_false_iff_not, List.all_eq_true, decide_eq_true_eq] at hs
    rcases List.mem_cons.mp hn with he | hn
    · cases he
      calc
        evaluate i s env ((name, e) :: rest) name = e.eval (graphValues i env) s := by
          simpa [evaluate] using evaluate_preserves_seen rest (name :: seen) hs.2 i s
            (fun n => if n == name then e.eval (graphValues i env) s else env n) name (by simp)
        _ = e.eval (graphValues i (evaluate i s env ((name, e) :: rest))) s := by
          exact eval_congr e i s _ _ (fun n hn =>
            (evaluate_preserves_seen _ seen h i s env n (hs.1.2 n hn)).symm)
    · exact ih (head.1 :: seen) hs.2 _ hn

theorem bindings_ordered : ordered [] bindings = true := by decide

theorem validation_bindings_ordered : ordered [] PairedValidation.bindings = true := by decide +kernel

def Equations (nodes : List (Computation × E 64)) (g : Values GraphInput)
    (s : Values Register) : Prop :=
  ∀ name e, (name, e) ∈ nodes → g (.node name) = e.eval g s

theorem evaluate_solution (nodes : List (Computation × E 64)) (seen : List Computation)
    (i : Values Input) (s : Values Register) (env solution : Environment)
    (ho : ordered seen nodes = true) (he : Equations nodes (graphValues i solution) s)
    (ha : ∀ n ∈ seen, env n = solution n) :
    ∀ n ∈ seen ++ nodes.map Prod.fst, evaluate i s env nodes n = solution n := by
  induction nodes generalizing seen env with
  | nil => simpa [evaluate] using ha
  | cons head rest ih =>
    simp only [ordered, Bool.and_eq_true, Bool.not_eq_true', List.contains_eq_mem,
      decide_eq_false_iff_not, List.all_eq_true, decide_eq_true_eq] at ho
    have hh : head.2.eval (graphValues i env) s = solution head.1 :=
      (eval_congr head.2 i s env solution (fun n hn => ha n (ho.1.2 n hn))).trans
        (he head.1 head.2 (List.mem_cons_self)).symm
    have ha' : ∀ n ∈ head.1 :: seen,
        (if n == head.1 then head.2.eval (graphValues i env) s else env n) = solution n := by
      intro n hn
      by_cases hn' : n = head.1 <;> simp_all
    simpa only [evaluate, List.map_cons, List.mem_append, List.mem_cons, or_assoc, or_comm, or_left_comm] using
      ih (head.1 :: seen) _ ho.2 (fun n e hn => he n e (List.mem_cons_of_mem _ hn)) ha'

theorem inputs_equations (nodes : List (Computation × E 64))
    (h : ordered [] nodes = true) (i : Values Input) (s : Values Register) :
    Equations nodes (inputs nodes i s) s := by
  exact fun name e hn => evaluate_equations nodes [] h i s (fun _ => 0) name e hn

theorem upstream_equations (g : Values GraphInput) (s : Values Register)
    (h : Equations bindings g s) : PairedValidation.UpstreamEquations g s := by
  constructor
  case validating =>
    simpa only [validating, Expr.eval, BitVec.extractLsb'_append_eq_right] using
      congrArg (fun v : BitVec 64 => v.extractLsb' 0 1)
        (h .validating (.concat (.lit (0 : BitVec 63)) validatingExpr) (by simp [bindings]))
  case bank =>
    simpa only [parameterBank, Expr.eval, BitVec.extractLsb'_append_eq_right] using
      congrArg (fun v : BitVec 64 => v.extractLsb' 0 1)
        (h .parameterBank (.concat (.lit (0 : BitVec 63)) parameterBankExpr) (by simp [bindings]))
  case index0 =>
    simpa only [parameterIndex0, Expr.eval, BitVec.extractLsb'_append_eq_right] using
      congrArg (fun v : BitVec 64 => v.extractLsb' 0 5)
        (h .parameterIndex0 (.concat (.lit (0 : BitVec 59)) parameterIndex0Expr) (by simp [bindings]))
  case index1 =>
    simpa only [parameterIndex1, Expr.eval, BitVec.extractLsb'_append_eq_right] using
      congrArg (fun v : BitVec 64 => v.extractLsb' 0 5)
        (h .parameterIndex1 (.concat (.lit (0 : BitVec 59)) parameterIndex1Expr) (by simp [bindings]))
  case parameter0 =>
    simpa only [PairedController.parameter0, Expr.eval, BitVec.extractLsb'_append_eq_right] using
      congrArg (fun v : BitVec 64 => v.extractLsb' 0 20)
        (h .parameter0 (.concat (.lit (0 : BitVec 44)) parameter0Expr) (by simp [bindings]))
  case parameter1 =>
    simpa only [PairedController.parameter1, Expr.eval, BitVec.extractLsb'_append_eq_right] using
      congrArg (fun v : BitVec 64 => v.extractLsb' 0 20)
        (h .parameter1 (.concat (.lit (0 : BitVec 44)) parameter1Expr) (by simp [bindings]))
  case good =>
    simpa only [PairedController.good, Expr.eval, BitVec.extractLsb'_append_eq_right] using
      congrArg (fun v : BitVec 64 => v.extractLsb' 0 1)
        (h .good (.concat (.lit (0 : BitVec 63)) goodExpr) (by simp [bindings]))

theorem validation_solution (g : Values GraphInput) (s : Values Register)
    (h : Equations bindings g s) : Equations PairedValidation.bindings g s := by
  intro name e hn
  obtain ⟨⟨original, rhs⟩, hm, he⟩ := List.mem_map.mp hn
  cases he
  by_cases hp : name = .push
  · subst name
    have hr : rhs = .concat (.lit (0 : BitVec 63)) pushExpr := by simpa [bindings] using hm
    subst rhs
    exact (h .push _ hm).trans (congrArg (fun b : BitVec 1 => (0 : BitVec 63) ++ b)
      (PairedValidation.isolatedPush_correct g s (upstream_equations g s h)).symm)
  · simpa only [if_neg hp] using h name rhs hm

theorem validation_complete (name : Computation) :
    name ∈ PairedValidation.bindings.map Prod.fst := by cases name <;> decide +kernel

/-- The isolated upload-validation graph computes exactly the original graph,
without upstream equations left as assumptions. -/
theorem validation_inputs_eq (i : Values Input) (s : Values Register) :
    (inputs PairedValidation.bindings i s : Values GraphInput) =
      (fun {_} p => inputs bindings i s p) := by
  funext w p
  cases p with
  | base p => simp only [inputs, graphValues]
  | q b => simp only [inputs, graphValues]
  | node name =>
    exact evaluate_solution PairedValidation.bindings [] i s (fun _ => 0)
      (evaluate i s (fun _ => 0) bindings) validation_bindings_ordered
      (validation_solution _ s (inputs_equations bindings bindings_ordered i s))
      (fun _ h => nomatch h) name (validation_complete name)

theorem lower_eval (base : {w : Nat} → Input w → Expr I Register w)
    (env : Computation → Expr I Register 64) (e : E w)
    (i : Values I) (s : Values Register) :
    (lower base env e).eval i s =
      e.eval (graphValues (fun p => (base p).eval i s) (fun k => (env k).eval i s)) s := by
  rw [lower, Expr.eval_bind]
  congr 1
  funext w p
  cases p <;> rfl

theorem construct_correct (nodes : List (Computation × E 64))
    (base : {w : Nat} → Input w → Expr I Register w)
    (env : Computation → Expr I Register 64) (seen : List Computation)
    (n : Netlist Register (Out Loader.Machine.Output) I)
    (h : construct base env seen nodes = .ok n) (i : Values I) (s : Values Register) :
    let g : Values GraphInput := graphValues (fun p => (base p).eval i s)
      (evaluate (fun p => (base p).eval i s) s (fun k => (env k).eval i s) nodes)
    (n.step i s : Values Register) = (fun {_} r => body.step g s r) ∧
      (n.observe i s : Values (Out Loader.Machine.Output)) = (fun {_} o => body.observe g s o) := by
  induction nodes generalizing I seen with
  | nil =>
    simp only [construct] at h
    split at h
    · cases h
      constructor <;> funext w p
      all_goals exact lower_eval base env _ i s
    · cases h
  | cons head rest ih =>
    simp only [construct] at h
    split at h
    · cases h
    · split at h
      · cases ht : construct (fun p => lift (base p))
          (fun k => if k == head.1 then .input .wire else lift (env k)) (head.1 :: seen) rest with
        | error error =>
          simp only [ht, bind, Except.bind] at h
          cases h
        | ok tail =>
          simp only [ht, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
          subst n
          simpa only [Netlist.step, Netlist.observe, evaluate, lower_eval, lift,
            Expr.eval_bind, Expr.eval, WithWire.values, apply_ite] using
            ih _ _ _ tail ht (WithWire.values i ((lower base env head.2).eval i s))
      · cases h

/-- Successful construction interprets the named graph, for arbitrary registers
and inputs. In particular this does not assume an initialized SRAM response. -/
theorem core_correct (n : Netlist Register (Out Loader.Machine.Output) Input)
    (h : PairedController.core = .ok n) (i : Values Input) (s : Values Register) :
    (n.step i s : Values Register) = (fun {_} r => body.step (inputs bindings i s) s r) ∧
      (n.observe i s : Values (Out Loader.Machine.Output)) =
        (fun {_} o => body.observe (inputs bindings i s) s o) := by
  exact construct_correct bindings (.input) (fun _ => .lit 0) [] n h i s

theorem validation_core_correct (n : Netlist Register (Out Loader.Machine.Output) Input)
    (h : PairedValidation.core = .ok n) (i : Values Input) (s : Values Register) :
    (n.step i s : Values Register) =
        (fun {_} r => body.step (inputs PairedValidation.bindings i s) s r) ∧
      (n.observe i s : Values (Out Loader.Machine.Output)) =
        (fun {_} o => body.observe (inputs PairedValidation.bindings i s) s o) := by
  exact construct_correct PairedValidation.bindings (.input) (fun _ => .lit 0) [] n h i s

theorem validation_core_eq (original retained : Netlist Register (Out Loader.Machine.Output) Input)
    (ho : PairedController.core = .ok original) (hv : PairedValidation.core = .ok retained)
    (i : Values Input) (s : Values Register) :
    (retained.step i s : Values Register) = (fun {_} r => original.step i s r) ∧
      (retained.observe i s : Values (Out Loader.Machine.Output)) =
        (fun {_} o => original.observe i s o) := by
  simpa only [validation_inputs_eq, ← (core_correct original ho i s).1,
    ← (core_correct original ho i s).2] using validation_core_correct retained hv i s

/-- The restricted SRAM contract never needs simultaneous read and write,
even before controller initialization or for malformed host commands. -/
theorem request_exclusive (g : Values GraphInput) (s : Values Register) :
    (request .read).eval g s = 1 → (request .write).eval g s = 0 := by
  simp only [request, both, writing, nextBusy, Expr.eval]
  have h : (g (.node .writing)).extractLsb' 0 1 = 0 ∨
      (g (.node .writing)).extractLsb' 0 1 = 1 := by bv_omega
  rcases h with h | h <;> simp [h]

theorem validation_core_exclusive (n : Netlist Register (Out Loader.Machine.Output) Input)
    (h : PairedValidation.core = .ok n) (i : Values Input) (s : Values Register) :
    n.observe i s (.port .read) = 1 → n.observe i s (.port .write) = 0 := by
  have hp (p : SramController.Port 1) : n.observe i s (.port p) =
      (request p).eval (inputs PairedValidation.bindings i s) s :=
    congrArg (fun f : Values (Out Loader.Machine.Output) => f (.port p))
      (validation_core_correct n h i s).2
  simpa only [hp] using request_exclusive (inputs PairedValidation.bindings i s) s

theorem inactive_correct (i : Values Input) (s : Values Register) :
    inactive.eval (inputs bindings i s) s = ~~~s .active := by
  simpa only [inactive, inactiveExpr, Expr.eval, BitVec.extractLsb'_append_eq_right] using
    congrArg (fun v : BitVec 64 => v.extractLsb' 0 1)
      (inputs_equations bindings bindings_ordered i s .inactive
        (.concat (.lit (0 : BitVec 63)) inactiveExpr) (by simp [bindings]))

theorem write_address_bank (i : Values Input) (s : Values Register)
    (h : (request .write).eval (inputs bindings i s) s = 1) :
    ((request (.address false)).eval (inputs bindings i s) s).extractLsb' 8 1 = ~~~s .active := by
  simp only [request, Expr.eval, show writing.eval (inputs bindings i s) s = 1 from h,
    if_true, BitVec.extractLsb'_append_eq_left, inactive_correct]

end Pinwheel.Hardware.Storage.PairedSemantics
