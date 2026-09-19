import Pinwheel.Hardware.Storage.PrefetchBackend
import Pinwheel.Hardware.Storage.OnePortBackend
import Pinwheel.Hardware.Storage.TwoPortBackend
import Pinwheel.Hardware.Structure

/-! The data port and the fetch path, structurally.

The loader's data port is a 64-bit host input with its own arrival budget. In a
policy backend it should reach the loader — the dictionaries, the index maps,
the cursor — and nothing else. It used to reach everything: the capacity check
reads the pushed word and rewrites the command, and every command decode,
including commit and start, sat behind it; the routed one-port design missed
the slow corner on exactly that path. With the command-split lift, the fact
that the data port has **no path** to the scheduler's registers, the cached
word or a policy's own registers is a theorem: once for the generic backend
(`core_data_free`), and for a two-wire realization whenever the policy's own
four pieces are data-free (`DataFree.next`), which for the three organizations
is a computation. Structural unreachability gives semantic independence
(`DataFree.step_independent`, from `Netlist.step_congr_of_arrival_none`). -/
namespace Pinwheel.Hardware.Storage.Backend.Policy
open Loader

/-- Only the loader's data port launches. -/
def dataPort : Launch Machine.Input
  | _, .data => some 0
  | _, _ => none

/-- No register launches. -/
abbrev quiet {R : Nat → Type} : Launch R := fun _ => none

/-- Below one, two and three wires none of which can see the data port. -/
abbrev leaves1 : Launch W1 := WithWire.arrivals dataPort none
abbrev leaves2 {a : Nat} : Launch (W2 a) := WithWire.arrivals leaves1 none
abbrev leaves3 {a b : Nat} : Launch (W3 a b) := WithWire.arrivals leaves2 none

section
variable (pick : Pick) (cost : Cost)

theorem fresh_arrival {I R : Nat → Type} {width : Nat} (e : Expr I R w) (input : Launch I)
    (register : Launch R) (wire : Option Nat) :
    (fresh e : Expr (WithWire I width) R w).arrival pick cost (WithWire.arrivals input wire) register =
      e.arrival pick cost input register := by
  simp only [fresh, Expr.arrival_bind, Expr.arrival, WithWire.arrivals]

theorem inner_arrival {X : Nat → Type} (e : Backend.E w) (input : Launch Machine.Input)
    (register : Launch (Register X)) :
    (inner (X := X) e).arrival pick cost input register =
      e.arrival pick cost input (fun r => register (.inner r)) := by
  simp only [inner, Expr.arrival_bind, Expr.arrival]

theorem readTree_arrival_none {J R : Nat → Type} (bits : Nat) (words : BitVec bits → Expr J R w)
    (address : Expr J R bits) (leaves : Launch J) (register : Launch R)
    (hwords : ∀ k, (words k).arrival pick cost leaves register = none)
    (haddress : address.arrival pick cost leaves register = none) :
    (Execution.readTree bits words address).arrival pick cost leaves register = none := by
  induction bits with
  | zero => exact hwords 0
  | succ n ih =>
    have hslice : (Expr.slice 1 n (by omega) address).arrival pick cost leaves register = none := by
      simp only [Expr.arrival, haddress, after, Option.map_none]
    simp only [Execution.readTree, Expr.arrival, haddress,
      ih (fun k => words (k ++ (1#1))) _ (fun k => hwords _) hslice,
      ih (fun k => words (k ++ (0#1))) _ (fun k => hwords _) hslice, merge, after, Option.map_none]

/-! ### The loader-level leaves, in the split form -/

/-- The logical registers are registers and constants: no input at all. -/
theorem logical_quiet (r : Cache.Register w) :
    (Backend.logical r).arrival pick cost dataPort quiet = none := by
  cases r with
  | current => rfl
  | machine r =>
    cases r with
    | control r => rfl
    | core r => rfl
    | memory b r =>
      cases r with
      | word k =>
        simp only [Backend.logical, Small.logical]
        split <;> rfl
      | index k => rfl
      | idle => rfl
      | last => rfl

/-- The split lift's arrival is the split expression's: substitution of the
logical registers adds no path. -/
theorem lift_arrival (e : Expr Machine.Input Cache.Register w) :
    (BankSelect.lift e).arrival pick cost dataPort quiet =
      (CommandSplit.expression (Cache.liftExpr CommandSplit.capacity) e).arrival pick cost dataPort quiet := by
  simp only [BankSelect.lift, Expr.arrival_bind, Expr.arrival, logical_quiet]

/-- Every scheduler input of the loader — reset, start, the idle pins, the last
address, the cached word — without a path from the data port. -/
theorem base_data_free (p : Reactive.Input w) :
    (BankSelect.lift (Cache.baseInputs p)).arrival pick cost dataPort quiet = none := by
  cases p <;> rfl

theorem commit_lift_data_free :
    (BankSelect.lift (Cache.liftExpr Machine.commitGate)).arrival pick cost dataPort quiet = none := rfl

theorem branch_lift_data_free :
    (BankSelect.lift FetchChoice.branch).arrival pick cost dataPort quiet = none := rfl

/-- The selected bank's registers: the bank selection decodes the raw commit. -/
theorem chosen_data_free (r : Loader.Store.Register w) :
    (BankSelect.lift (Cache.chosen r)).arrival pick cost dataPort quiet = none := by
  rw [lift_arrival]
  cases r <;> rfl

/-- The plain lift does not have this property: behind the capacity check, the
commit decode sees the data port. -/
theorem plain_commit_sees_data :
    (Backend.lift (Cache.liftExpr Machine.commitGate)).arrival max Cost.unit dataPort quiet ≠ none := by
  decide

/-! ### What policies build their wires from -/

variable {X : Nat → Type}

theorem liftC_data_free (e : Expr Machine.Input Cache.Register w)
    (h : (BankSelect.lift e).arrival pick cost dataPort quiet = none) :
    (liftC (X := X) e).arrival pick cost dataPort quiet = none := by
  rw [liftC, inner_arrival]
  exact h

theorem commit_data_free : (commit (X := X)).arrival pick cost dataPort quiet = none :=
  liftC_data_free pick cost _ (commit_lift_data_free pick cost)

theorem branch_data_free : (branch (X := X)).arrival pick cost dataPort quiet = none :=
  liftC_data_free pick cost _ (branch_lift_data_free pick cost)

theorem running_data_free : (running (X := X)).arrival pick cost dataPort quiet = none := by
  rw [running, Expr.arrival_bind]
  exact Expr.arrival_none pick cost _ _ _ (fun _ => rfl) (fun _ => rfl)

/-- Any scheduler expression that does not consult the successor. -/
theorem sched0_data_free (e : Reactive.E w) :
    (sched0 (X := X) e).arrival pick cost dataPort quiet = none := by
  rw [sched0, Expr.arrival_bind]
  refine Expr.arrival_none pick cost _ _ _ (fun p => ?_) (fun _ => rfl)
  cases p <;> first
    | rfl
    | exact liftC_data_free pick cost _ (base_data_free pick cost _)

/-- Any scheduler expression, fed a successor that cannot see the data port. -/
theorem sched_data_free (e : Reactive.E w) :
    (sched (X := X) e).arrival pick cost leaves1 quiet = none := by
  rw [sched, Expr.arrival_bind]
  refine Expr.arrival_none pick cost _ _ _ (fun p => ?_) (fun _ => rfl)
  cases p <;> first
    | rfl
    | exact (fresh_arrival pick cost _ _ _ _).trans (liftC_data_free pick cost _ (base_data_free pick cost _))

/-- The selected bank's composite read, wherever it is placed, at a data-free address. -/
theorem readAt_data_free {J : Nat → Type} (place : {w : Nat} → E X w → Expr J (Register X) w)
    (leaves : Launch J)
    (hplace : ∀ {w : Nat} (e : E X w), e.arrival pick cost dataPort quiet = none →
      (place e).arrival pick cost leaves quiet = none)
    (address : Expr J (Register X) 8) (haddress : address.arrival pick cost leaves quiet = none) :
    (readAt place address).arrival pick cost leaves quiet = none := by
  unfold readAt
  refine readTree_arrival_none pick cost 6 _ _ leaves quiet
    (fun k => hplace _ (liftC_data_free pick cost _ (chosen_data_free pick cost _))) ?_
  exact readTree_arrival_none pick cost 8 _ _ leaves quiet
    (fun k => hplace _ (liftC_data_free pick cost _ (chosen_data_free pick cost _))) haddress

theorem fresh1_data_free (e : E X w) (h : e.arrival pick cost dataPort quiet = none) :
    (fresh e : Expr W1 (Register X) w).arrival pick cost leaves1 quiet = none :=
  (fresh_arrival pick cost _ _ _ _).trans h

theorem fresh2_data_free {a : Nat} (e : Expr W1 (Register X) w)
    (h : e.arrival pick cost leaves1 quiet = none) :
    (fresh e : Expr (W2 a) (Register X) w).arrival pick cost leaves2 quiet = none :=
  (fresh_arrival pick cost _ _ _ _).trans h

theorem fresh3_data_free {a b : Nat} (e : Expr (W2 a) (Register X) w)
    (h : e.arrival pick cost leaves2 quiet = none) :
    (fresh e : Expr (W3 a b) (Register X) w).arrival pick cost leaves3 quiet = none :=
  (fresh_arrival pick cost _ _ _ _).trans h

theorem leaf_data_free {a b : Nat} (e : E X w) (h : e.arrival pick cost dataPort quiet = none) :
    (leaf (a := a) (b := b) e).arrival pick cost leaves3 quiet = none :=
  fresh3_data_free pick cost _ (fresh2_data_free pick cost _ (fresh1_data_free pick cost _ h))

/-! ### The generic backend -/

theorem schedW_data_free (e : Reactive.E w) :
    (schedW e).arrival pick cost (WithWire.arrivals dataPort none) quiet = none := by
  rw [schedW, Expr.arrival_bind]
  refine Expr.arrival_none pick cost _ _ _ (fun p => ?_) (fun _ => rfl)
  cases p <;> first
    | rfl
    | exact (fresh_arrival pick cost _ _ _ _).trans (base_data_free pick cost _)

/-- The registers of the fetch path in the general backend: the scheduler's and
the cached word. The loader's control, the dictionaries, the index maps and the
idle and last words are outside it: they take the pushed word. -/
def fetchCore : {w : Nat} → Backend.Register w → Bool
  | _, .core _ | _, .current => true
  | _, _ => false

/-- Fed a successor that cannot see the data port, no scheduler register, and
not the cached word, can see it either. -/
theorem core_data_free (r : Backend.Register w) (hr : fetchCore r = true) :
    (core.next r).arrival pick cost (WithWire.arrivals dataPort none) quiet = none := by
  cases r with
  | core r => exact schedW_data_free pick cost _
  | current =>
    simp only [core, enableW, Execution.bor, Expr.arrival, schedW_data_free, WithWire.arrivals, merge,
      after, Option.map_none]
  | control r => cases hr
  | word b k => cases hr
  | index b k => cases hr
  | idle b => cases hr
  | last b => cases hr

/-- Nor can the scheduler's outputs: pin levels and enables, the address, busy. -/
theorem core_output_data_free (o : Reactive.Output w) :
    (core.output (.core o)).arrival pick cost (WithWire.arrivals dataPort none) quiet = none :=
  schedW_data_free pick cost _

/-! ### Two-wire realizations -/

variable {p : Nat} {σ : Type} {P : FetchPolicy.Policy p σ}

/-- A policy's four structural pieces, none with a path from the data port. -/
structure DataFree {a b : Nat} (fed : E X 64) (wire2 : Expr W1 (Register X) a)
    (wire3 : Expr (W2 a) (Register X) b) (regNext : {w : Nat} → X w → Expr (W3 a b) (Register X) w) :
    Prop where
  fed : fed.arrival pick cost dataPort quiet = none
  wire2 : wire2.arrival pick cost leaves1 quiet = none
  wire3 : wire3.arrival pick cost leaves2 quiet = none
  regNext : ∀ {w : Nat} (x : X w), (regNext x).arrival pick cost leaves3 quiet = none

/-- The fetch path of a policy backend: the scheduler's registers, the cached
word and the policy's own registers. -/
def fetchPath : {w : Nat} → Register X w → Bool
  | _, .inner r => fetchCore r
  | _, .extra _ => true

variable {a b : Nat} {val : σ → Values X} {fed : E X 64} {wire2 : Expr W1 (Register X) a}
  {wire3 : Expr (W2 a) (Register X) b} {regNext : {w : Nat} → X w → Expr (W3 a b) (Register X) w}
  {fed_correct : ∀ (i : Machine.Inputs) (s : State σ), fed.eval i.values (s.values val) = fedWord P i s}
  {extra_correct : ∀ (i : Machine.Inputs) (s : State σ) {w : Nat} (x : X w),
    (regNext x).eval (values3 val fed wire2 wire3 i s) (s.values val) = val (Policy.next P i s).policy x}

/-- **No path from the data port into the fetch path**, for every two-wire
realization of every policy whose own pieces are data-free. -/
theorem DataFree.next (h : DataFree pick cost fed wire2 wire3 regNext) (r : Register X w)
    (hr : fetchPath r = true) :
    (Realization.twoWires (P := P) val fed wire2 wire3 regNext fed_correct extra_correct).netlist.arrivalNext
      pick cost dataPort quiet r = none := by
  simp only [Realization.twoWires, Netlist.arrivalNext, h.fed, h.wire2, h.wire3]
  cases r with
  | extra x => exact h.regNext x
  | inner r =>
    show ((core.next r).inner input3).arrival pick cost leaves3 quiet = none
    rw [Expr.arrival_inner]
    have hin : (fun {w} (q : WS w) => (input3 (X := X) (a := a) (b := b) q).arrival pick cost leaves3 quiet) =
        (WithWire.arrivals dataPort none : Launch WS) := by
      funext w q
      cases q <;> rfl
    rw [hin]
    exact core_data_free pick cost r hr

/-- And the scheduler's outputs. -/
theorem DataFree.output (h : DataFree pick cost fed wire2 wire3 regNext) (o : Reactive.Output w) :
    (Realization.twoWires (P := P) val fed wire2 wire3 regNext fed_correct extra_correct).netlist.arrivalOutput
      pick cost dataPort quiet (.core o) = none := by
  simp only [Realization.twoWires, Netlist.arrivalOutput, h.fed, h.wire2, h.wire3]
  show ((core.output (.core o)).inner input3).arrival pick cost leaves3 quiet = none
  rw [Expr.arrival_inner]
  have hin : (fun {w} (q : WS w) => (input3 (X := X) (a := a) (b := b) q).arrival pick cost leaves3 quiet) =
      (WithWire.arrivals dataPort none : Launch WS) := by
    funext w q
    cases q <;> rfl
  rw [hin]
  exact core_output_data_free pick cost o

end

/-- What structural unreachability buys: on the fetch path, the next value of
every register is the same whatever word the host presents. -/
theorem DataFree.step_independent {p : Nat} {σ : Type} {P : FetchPolicy.Policy p σ} {X : Nat → Type}
    {a b : Nat} {val : σ → Values X} {fed : E X 64} {wire2 : Expr W1 (Register X) a}
    {wire3 : Expr (W2 a) (Register X) b} {regNext : {w : Nat} → X w → Expr (W3 a b) (Register X) w}
    {fed_correct : ∀ (i : Machine.Inputs) (s : State σ), fed.eval i.values (s.values val) = fedWord P i s}
    {extra_correct : ∀ (i : Machine.Inputs) (s : State σ) {w : Nat} (x : X w),
      (regNext x).eval (values3 val fed wire2 wire3 i s) (s.values val) = val (Policy.next P i s).policy x}
    (h : DataFree max Cost.unit fed wire2 wire3 regNext) (i : Machine.Inputs) (data : BitVec 64)
    (s : Values (Register X)) (r : Register X w) (hr : fetchPath r = true) :
    (Realization.twoWires (P := P) val fed wire2 wire3 regNext fed_correct extra_correct).netlist.step
        i.values s r =
      (Realization.twoWires (P := P) val fed wire2 wire3 regNext fed_correct extra_correct).netlist.step
        {i with data := data}.values s r := by
  refine Netlist.step_congr_of_arrival_none max Cost.unit _ dataPort quiet _ _ s s (fun q hq => ?_)
    (fun _ _ => rfl) r (h.next max Cost.unit r hr)
  cases q <;> first | rfl | cases hq

end Pinwheel.Hardware.Storage.Backend.Policy

/-! ### The three organizations -/

namespace Pinwheel.Hardware.Storage.Backend
open Policy

section
variable (pick : Pick) (cost : Cost)

theorem Prefetch.dataFree :
    DataFree pick cost Prefetch.successor Prefetch.taken Prefetch.untaken Prefetch.regNext where
  fed := by
    simp only [Prefetch.successor, Expr.arrival, running_data_free, branch_data_free, merge, after,
      Option.map_none]
  wire2 := sched_data_free pick cost _
  wire3 := fresh2_data_free pick cost _ (sched_data_free pick cost _)
  regNext := fun x => by
    have hread (address : Expr Prefetch.W3 Prefetch.Register 8)
        (ha : address.arrival pick cost leaves3 quiet = none) :
        (Prefetch.read3 address).arrival pick cost leaves3 quiet = none :=
      readAt_data_free pick cost _ _ (fun e he => leaf_data_free pick cost e he) address ha
    cases x with
    | fetched b => cases b <;> exact hread _ rfl
    | startWord =>
      simp only [Prefetch.regNext, Expr.arrival, leaf_data_free pick cost _ (commit_data_free pick cost),
        hread (.lit 0) rfl, merge, after, Option.map_none]

theorem TwoPort.dataFree :
    DataFree pick cost TwoPort.successor TwoPort.word0 TwoPort.taken TwoPort.regNext where
  fed := by
    simp only [TwoPort.successor, Expr.arrival, running_data_free, branch_data_free, merge, after,
      Option.map_none]
  wire2 := by
    refine readAt_data_free pick cost _ _ (fun e he => fresh1_data_free pick cost e he) _ ?_
    simp only [TwoPort.address0, Expr.arrival, sched_data_free,
      fresh1_data_free pick cost _ (commit_data_free pick cost), merge, after, Option.map_none]
  wire3 := fresh2_data_free pick cost _ (sched_data_free pick cost _)
  regNext := fun x => by
    cases x with
    | fetched b =>
      cases b
      · rfl
      · exact readAt_data_free pick cost _ _ (fun e he => leaf_data_free pick cost e he) _ rfl
    | startWord =>
      simp only [TwoPort.regNext, Expr.arrival, leaf_data_free pick cost _ (commit_data_free pick cost),
        WithWire.arrivals, merge, after, Option.map_none]

theorem OnePort.dataFree :
    DataFree pick cost OnePort.successor OnePort.address OnePort.word OnePort.regNext where
  fed := by
    simp only [OnePort.successor, OnePort.choose, Expr.arrival, running_data_free, branch_data_free,
      sched0_data_free, merge, after, Option.map_none]
  wire2 := by
    simp only [OnePort.address, Expr.arrival, sched_data_free,
      fresh1_data_free pick cost _ (commit_data_free pick cost), merge, after, Option.map_none]
  wire3 := readAt_data_free pick cost _ _
    (fun e he => fresh2_data_free pick cost _ (fresh1_data_free pick cost e he)) _ rfl
  regNext := fun x => by
    have hdispatch : OnePort.dispatch3.arrival pick cost leaves3 quiet = none :=
      fresh3_data_free pick cost _ (fresh2_data_free pick cost _ (sched_data_free pick cost _))
    cases x with
    | fetched b =>
      cases b <;>
        simp only [OnePort.regNext, OnePort.taken3, Expr.arrival, hdispatch, WithWire.arrivals, merge,
          after, Option.map_none]
    | startWord =>
      simp only [OnePort.regNext, Expr.arrival, leaf_data_free pick cost _ (commit_data_free pick cost),
        WithWire.arrivals, merge, after, Option.map_none]
    | second => exact hdispatch

end

/-- In each emitted backend, no register of the fetch path has a path from the data port. -/
theorem Prefetch.fetch_path_data_free (pick : Pick) (cost : Cost) (r : Prefetch.Register w)
    (hr : fetchPath r = true) : Prefetch.netlist.arrivalNext pick cost dataPort quiet r = none :=
  (Prefetch.dataFree pick cost).next pick cost r hr

theorem TwoPort.fetch_path_data_free (pick : Pick) (cost : Cost) (r : TwoPort.Register w)
    (hr : fetchPath r = true) : TwoPort.netlist.arrivalNext pick cost dataPort quiet r = none :=
  (TwoPort.dataFree pick cost).next pick cost r hr

theorem OnePort.fetch_path_data_free (pick : Pick) (cost : Cost) (r : OnePort.Register w)
    (hr : fetchPath r = true) : OnePort.netlist.arrivalNext pick cost dataPort quiet r = none :=
  (OnePort.dataFree pick cost).next pick cost r hr

end Pinwheel.Hardware.Storage.Backend
