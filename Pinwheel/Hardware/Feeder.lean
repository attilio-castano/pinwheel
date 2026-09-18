import Pinwheel.Hardware.Structure
import Pinwheel.Hardware.TimedPairs

/-! Feeders: registers and wiring placed in front of a netlist's inputs.

A chip is a proved core behind layers that turn pins into the core's ports —
input samplers, a serial loader, a pin map. Each layer is a `Feeder`: what every
inner input is, and how the layer's own registers move, as expressions over the
outer inputs and the layer's registers only. One theorem then says what any
inner netlist does behind any feeder: it takes exactly the edges it would take
on the *fed* history, one for one, whatever the inner netlist is
(`wrap_pairTrace`). Layers compose by nesting, and a `Model` reads a feeder as
ordinary functions on records. An `OutputMap` is the same idea on the output
side, with no state. -/
namespace Pinwheel.Hardware

/-- A netlist as a timed component over raw valuations. -/
def Netlist.component (n : Netlist R O I) : Timed.Component (Values I) (Values R) (Values O) :=
  ⟨fun i r => n.step i r, fun i r => n.observe i r⟩

/-- A netlist as a timed component over input records. -/
def Netlist.componentOf {P : Type} (values : P → Values I) (n : Netlist R O I) :
    Timed.Component P (Values R) (Values O) :=
  ⟨fun i r => n.step (values i) r, fun i r => n.observe (values i) r⟩

/-- Wiring and registers in front of a netlist's inputs. -/
structure Feeder (J X I : Nat → Type) where
  /-- What each inner input is. -/
  input : {w : Nat} → I w → Expr J X w
  /-- How the feeder's own registers move. -/
  next : {w : Nat} → X w → Expr J X w

namespace Feeder
variable {J X I R O : Nat → Type}

/-- What the inner netlist sees. -/
def feed (F : Feeder J X I) (j : Values J) (x : Values X) : Values I :=
  fun p => (F.input p).eval j x

/-- The feeder's registers after an edge. -/
def step (F : Feeder J X I) (j : Values J) (x : Values X) : Values X :=
  fun r => (F.next r).eval j x

/-- A feeder expression among the registers of the wrapped design. -/
def outer (e : Expr J X w) : Expr J (Extended R X) w :=
  e.bind (fun p => .input p) (fun r => .reg (.extra r))

theorem outer_correct (e : Expr J X w) (j : Values J) (s : Values (Extended R X)) :
    (outer (R := R) e).eval j s = e.eval j (Extended.extraValues s) := by
  simp only [outer, Expr.eval_bind, Expr.eval]
  rfl

/-- The inner netlist behind the feeder: its expressions are reused unchanged. -/
def wrap (F : Feeder J X I) (n : Netlist R O I) : Netlist (Extended R X) O J :=
  n.extend (fun p => outer (F.input p)) (fun r => outer (F.next r))

theorem wrap_step (F : Feeder J X I) (n : Netlist R O I) (j : Values J) (s : Values R)
    (x : Values X) :
    ((F.wrap n).step j (Extended.values s x) : Values (Extended R X)) =
      (fun {_} r => Extended.values (n.step (F.feed j x) s) (F.step j x) r) := by
  funext w r
  cases r with
  | inner r =>
    simp only [wrap, Netlist.extend_inner, outer_correct]
    rfl
  | extra r =>
    simp only [wrap, Netlist.extend_extra, outer_correct]
    rfl

theorem wrap_observe (F : Feeder J X I) (n : Netlist R O I) (j : Values J) (s : Values R)
    (x : Values X) :
    ((F.wrap n).observe j (Extended.values s x) : Values O) =
      (fun {_} o => n.observe (F.feed j x) s o) := by
  funext w o
  simp only [wrap, Netlist.extend_observe, outer_correct]
  rfl

/-- What the inner netlist consumes on each edge and sees after it, from what the
wrapped one does. After an edge the feeder's registers already hold their next
values, so an inner output that depends combinationally on an input sees those. -/
def history (F : Feeder J X I) : Values X → List (Values J × Values J) → List (Values I × Values I)
  | _, [] => []
  | x, (j, after) :: rest =>
    (F.feed j x, F.feed after (F.step j x)) :: F.history (F.step j x) rest

/-- **Behind any feeder, any netlist takes exactly the edges it would take on the
fed history**: none added, removed or reordered, and the feeder's state is the
only thing that stands between the two. -/
theorem wrap_pairTrace (F : Feeder J X I) (n : Netlist R O I) (s : Values R) (x : Values X)
    (inputs : List (Values J × Values J)) :
    (F.wrap n).component.pairTrace (Extended.values s x) inputs =
      n.component.pairTrace s (F.history x inputs) := by
  induction inputs generalizing s x with
  | nil => rfl
  | cons pair rest ih =>
    obtain ⟨j, after⟩ := pair
    have hs := wrap_step F n j s x
    have ho := wrap_observe F n j s x
    have hn := wrap_observe F n after (n.step (F.feed j x) s) (F.step j x)
    simp only [Timed.Component.pairTrace, Netlist.component, history] at ih ⊢
    rw [hs, ho, hn]
    exact congrArg _ (ih _ _)

/-- The ordinary trace: each outer input held across its edge. -/
theorem wrap_trace (F : Feeder J X I) (n : Netlist R O I) (s : Values R) (x : Values X)
    (inputs : List (Values J)) :
    (F.wrap n).component.trace (Extended.values s x) inputs =
      n.component.pairTrace s (F.history x (inputs.map fun j => (j, j))) := by
  rw [← Timed.Component.pairTrace_same, wrap_pairTrace]

/-! ### Structural timing through a feeder -/

section Timing
variable (pick : Pick) (cost : Cost)

theorem outer_arrival (e : Expr J X w) (input : Launch J) (register : Launch (Extended R X)) :
    (outer (R := R) e).arrival pick cost input register =
      e.arrival pick cost input (fun r => register (.extra r)) := by
  simp only [outer, Expr.arrival_bind, Expr.arrival]

/-- An inner register's arrival is the inner netlist's own, with each inner input
arriving when the feeder's expression for it does. -/
theorem wrap_arrivalNext (F : Feeder J X I) (n : Netlist R O I) (input : Launch J)
    (register : Launch (Extended R X)) (r : R w) :
    (F.wrap n).arrivalNext pick cost input register (.inner r) =
      n.arrivalNext pick cost
        (fun p => (F.input p).arrival pick cost input (fun x => register (.extra x)))
        (fun r => register (.inner r)) r := by
  simp only [wrap, Netlist.arrivalNext_extend, outer_arrival]

theorem wrap_arrivalNext_extra (F : Feeder J X I) (n : Netlist R O I) (input : Launch J)
    (register : Launch (Extended R X)) (x : X w) :
    (F.wrap n).arrivalNext pick cost input register (.extra x) =
      (F.next x).arrival pick cost input (fun x => register (.extra x)) := by
  simp only [wrap, Netlist.arrivalNext_extend_extra, outer_arrival]

theorem wrap_arrivalOutput (F : Feeder J X I) (n : Netlist R O I) (input : Launch J)
    (register : Launch (Extended R X)) (o : O w) :
    (F.wrap n).arrivalOutput pick cost input register o =
      n.arrivalOutput pick cost
        (fun p => (F.input p).arrival pick cost input (fun x => register (.extra x)))
        (fun r => register (.inner r)) o := by
  simp only [wrap, Netlist.arrivalOutput_extend, outer_arrival]

/-- A feeder none of whose inner inputs can see the outer inputs — every one comes
from its registers — shields the inner netlist: no outer input has a path to any
inner register or output, whatever the inner netlist is. -/
theorem wrap_shields (F : Feeder J X I) (n : Netlist R O I) (input : Launch J)
    (registered : ∀ {w : Nat} (p : I w),
      (F.input p).arrival pick cost input (fun _ => none) = none) (r : R w) :
    (F.wrap n).arrivalNext pick cost input (fun _ => none) (.inner r) = none := by
  rw [wrap_arrivalNext]
  exact Netlist.arrivalNext_none pick cost n _ _ (fun p => registered p) (fun _ => rfl) r

theorem wrap_shields_output (F : Feeder J X I) (n : Netlist R O I) (input : Launch J)
    (registered : ∀ {w : Nat} (p : I w),
      (F.input p).arrival pick cost input (fun _ => none) = none) (o : O w) :
    (F.wrap n).arrivalOutput pick cost input (fun _ => none) o = none := by
  rw [wrap_arrivalOutput]
  exact Netlist.arrivalOutput_none pick cost n _ _ (fun p => registered p) (fun _ => rfl) o

end Timing

/-! ### A feeder read as functions on records -/

/-- Records for the outer inputs, the feeder's state and the inner inputs, with
the feeder's two expressions read as functions on them. -/
structure Model (F : Feeder J X I) (PJ PX PI : Type) where
  outer : PJ → Values J
  state : PX → Values X
  inner : PI → Values I
  feed : PJ → PX → PI
  step : PJ → PX → PX
  feed_correct : ∀ (j : PJ) (x : PX) {w : Nat} (p : I w),
    (F.input p).eval (outer j) (state x) = inner (feed j x) p
  step_correct : ∀ (j : PJ) (x : PX) {w : Nat} (r : X w),
    (F.next r).eval (outer j) (state x) = state (step j x) r

namespace Model
variable {F : Feeder J X I} {PJ PX PI : Type}

/-- The fed history, on records. -/
def history (M : Model F PJ PX PI) : PX → List (PJ × PJ) → List (PI × PI)
  | _, [] => []
  | x, (j, after) :: rest => (M.feed j x, M.feed after (M.step j x)) :: M.history (M.step j x) rest

theorem feed_eq (M : Model F PJ PX PI) (j : PJ) (x : PX) :
    (F.feed (M.outer j) (M.state x) : Values I) = (fun {_} p => M.inner (M.feed j x) p) :=
  funext fun _ => funext fun p => M.feed_correct j x p

theorem step_eq (M : Model F PJ PX PI) (j : PJ) (x : PX) :
    (F.step (M.outer j) (M.state x) : Values X) = (fun {_} r => M.state (M.step j x) r) :=
  funext fun _ => funext fun r => M.step_correct j x r

/-- The wrapped netlist on outer records takes the inner netlist's edges on the
fed records. -/
theorem pairTrace_eq (M : Model F PJ PX PI) (n : Netlist R O I) (s : Values R) (x : PX)
    (inputs : List (PJ × PJ)) :
    ((F.wrap n).componentOf M.outer).pairTrace (Extended.values s (M.state x)) inputs =
      (n.componentOf M.inner).pairTrace s (M.history x inputs) := by
  induction inputs generalizing s x with
  | nil => rfl
  | cons pair rest ih =>
    obtain ⟨j, after⟩ := pair
    have hs := wrap_step F n (M.outer j) s (M.state x)
    have ho := wrap_observe F n (M.outer j) s (M.state x)
    have hn := wrap_observe F n (M.outer after) (n.step (F.feed (M.outer j) (M.state x)) s)
      (F.step (M.outer j) (M.state x))
    simp only [Timed.Component.pairTrace, Netlist.componentOf, history] at ih ⊢
    rw [hs, ho, hn, M.step_eq j x, M.feed_eq j x, M.feed_eq after (M.step j x)]
    exact congrArg _ (ih _ _)

theorem trace_eq (M : Model F PJ PX PI) (n : Netlist R O I) (s : Values R) (x : PX)
    (inputs : List PJ) :
    ((F.wrap n).componentOf M.outer).trace (Extended.values s (M.state x)) inputs =
      (n.componentOf M.inner).pairTrace s (M.history x (inputs.map fun j => (j, j))) := by
  rw [← Timed.Component.pairTrace_same, pairTrace_eq]

end Model

/-! ### The two-register sampler of every input -/

/-- Two registers for each sampled input. -/
inductive Sampled (J : Nat → Type) : Nat → Type where
  | first : J w → Sampled J w
  | second : J w → Sampled J w

/-- Every input sampled twice before anything reads it; the stages never reset. -/
def sampler : Feeder J (Sampled J) J where
  input := fun p => .reg (.second p)
  next := fun r => match r with
    | .first p => .input p
    | .second p => .reg (.first p)

/-- The sampler's registers as two valuations of the inputs. -/
def sampledValues (first second : Values J) : Values (Sampled J)
  | _, .first p => first p
  | _, .second p => second p

theorem sampler_feed (j first second : Values J) :
    ((sampler (J := J)).feed j (sampledValues first second) : Values J) = (fun {_} p => second p) := rfl

theorem sampler_step (j first second : Values J) :
    ((sampler (J := J)).step j (sampledValues first second) : Values (Sampled J)) =
      (fun {_} r => sampledValues j first r) := by
  funext w r
  cases r <;> rfl

/-- No pin has a path past the first stage: behind the sampler, no input reaches
any inner register or output, whatever is behind it. -/
theorem sampler_registered (pick : Pick) (cost : Cost) (input : Launch J) {w : Nat} (p : J w) :
    ((sampler (J := J)).input p).arrival pick cost input (fun _ => none) = none := rfl

end Feeder

/-! ### Record-level sampler -/

namespace Feeder

/-- The sampler on input records: the two stages are two earlier records. -/
def samplerModel {J : Nat → Type} {P : Type} (values : P → Values J) :
    Model (sampler (J := J)) P (P × P) P where
  outer := values
  state := fun x => sampledValues (values x.1) (values x.2)
  inner := values
  feed := fun _ x => x.2
  step := fun j x => (j, x.1)
  feed_correct := fun _ _ _ _ => rfl
  step_correct := fun _ _ _ r => by cases r <;> rfl

end Feeder

/-! ### Output maps -/

/-- No registers. -/
inductive NoRegister : Nat → Type

/-- The only valuation of no registers. -/
def NoRegister.values : Values NoRegister := fun r => nomatch r

/-- New outputs as expressions over a netlist's outputs. -/
def Netlist.mapOutputs {O' : Nat → Type} : {I : Nat → Type} → Netlist R O I →
    ({w : Nat} → O' w → Expr O NoRegister w) → Netlist R O' I
  | _, .finish c, out => .finish
      { next := c.next
        output := fun o => (out o).bind (fun q => c.output q) (fun r => nomatch r) }
  | _, .letWire e body, out => .letWire e (body.mapOutputs out)

theorem Netlist.mapOutputs_step {O' : Nat → Type} (n : Netlist R O I)
    (out : {w : Nat} → O' w → Expr O NoRegister w)
    (i : Values I) (s : Values R) (r : R w) : (n.mapOutputs out).step i s r = n.step i s r := by
  induction n with
  | finish c => rfl
  | letWire e body ih => exact ih _

/-- A mapped output is its expression evaluated on the netlist's observations. -/
theorem Netlist.mapOutputs_observe {O' : Nat → Type} (n : Netlist R O I)
    (out : {w : Nat} → O' w → Expr O NoRegister w) (i : Values I) (s : Values R) (o : O' w) :
    (n.mapOutputs out).observe i s o = (out o).eval (n.observe i s) (fun r => nomatch r) := by
  induction n with
  | finish c =>
    simp only [Netlist.mapOutputs, Netlist.observe, Circuit.observe, Expr.eval_bind]
    congr 1
    funext w r
    exact nomatch r
  | letWire e body ih => exact ih _

/-- Observations through a function: the same edges, each observation mapped. -/
theorem Timed.Component.pairTrace_map {I S O O' : Type} (c : Timed.Component I S O)
    (c' : Timed.Component I S O') (g : O → O') (hstep : ∀ i s, c'.step i s = c.step i s)
    (hobserve : ∀ i s, c'.observe i s = g (c.observe i s)) (s : S) (inputs : List (I × I)) :
    c'.pairTrace s inputs = (c.pairTrace s inputs).map (fun e => (g e.1, g e.2)) := by
  induction inputs generalizing s with
  | nil => rfl
  | cons pair rest ih =>
    obtain ⟨i, after⟩ := pair
    simp only [Timed.Component.pairTrace, List.map, hstep, hobserve, ih]

end Pinwheel.Hardware
