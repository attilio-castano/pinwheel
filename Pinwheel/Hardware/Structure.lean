import Pinwheel.Hardware.NetlistExtend

/-! Structural timing: which leaves an expression can see, and how many levels lie
between a chosen set of launch points and an endpoint. Levels are an abstract
cost per operation, not nanoseconds; wire load, buffering and placement are
outside this model. -/
namespace Pinwheel.Hardware

/-- Levels charged per operation. Comparisons and arithmetic may depend on width. -/
structure Cost where
  concat : Nat
  slice : Nat
  inv : Nat
  band : Nat
  mux : Nat
  sub : Nat → Nat
  equal : Nat → Nat
  ult : Nat → Nat
  zero : Nat → Nat

/-- One level per emitted operation: the depth of the emitted dataflow graph. -/
def Cost.unit : Cost := ⟨1, 1, 1, 1, 1, fun _ => 1, fun _ => 1, fun _ => 1, fun _ => 1⟩

/-- A rough two-input-gate estimate: wiring is free, reductions and carries are
logarithmic trees. -/
def Cost.gates : Cost :=
  ⟨0, 0, 1, 1, 2, fun w => 2 + 2 * Nat.log2 w, fun w => 1 + Nat.log2 w,
    fun w => 2 + 2 * Nat.log2 w, fun w => Nat.log2 w⟩

/-- How two arriving transitions combine: `max` for the latest arrival (setup),
`min` for the earliest (hold). -/
abbrev Pick := Nat → Nat → Nat

/-- `none` means no launch point is visible. -/
def merge (pick : Pick) : Option Nat → Option Nat → Option Nat
  | none, b => b
  | a, none => a
  | some a, some b => some (pick a b)

def after (levels : Nat) (arrival : Option Nat) : Option Nat := arrival.map (· + levels)

theorem merge_eq_none {pick : Pick} {a b : Option Nat} :
    merge pick a b = none ↔ a = none ∧ b = none := by
  cases a <;> cases b <;> simp [merge]

theorem after_eq_none {levels : Nat} {a : Option Nat} : after levels a = none ↔ a = none := by
  cases a <;> simp [after]

abbrev Launch (Signal : Nat → Type) := {w : Nat} → Signal w → Option Nat

section
variable (pick : Pick) (cost : Cost)

/-- Arrival at the output of an expression, given the arrival of every launch
point among its leaves. Literals never launch a transition. -/
def Expr.arrival (input : Launch I) (register : Launch R) : Expr I R w → Option Nat
  | .input i => input i
  | .reg r => register r
  | .lit _ => none
  | .concat x y => after cost.concat (merge pick (x.arrival input register) (y.arrival input register))
  | .inv x => after cost.inv (x.arrival input register)
  | .band x y => after cost.band (merge pick (x.arrival input register) (y.arrival input register))
  | .sub (w := w) x y => after (cost.sub w) (merge pick (x.arrival input register) (y.arrival input register))
  | .slice _ _ _ x => after cost.slice (x.arrival input register)
  | .equal (w := v) x y => after (cost.equal v) (merge pick (x.arrival input register) (y.arrival input register))
  | .ult (w := v) x y => after (cost.ult v) (merge pick (x.arrival input register) (y.arrival input register))
  | .zero (w := v) x => after (cost.zero v) (x.arrival input register)
  | .mux c t f => after cost.mux (merge pick (c.arrival input register)
      (merge pick (t.arrival input register) (f.arrival input register)))

/-- Composition law: wiring an expression into the leaves of another adds the
arrival of what is wired in. No path is created or lost by substitution. -/
theorem Expr.arrival_bind (f : {w : Nat} → I w → Expr J S w) (g : {w : Nat} → R w → Expr J S w)
    (e : Expr I R w) (input : Launch J) (register : Launch S) :
    (e.bind f g).arrival pick cost input register =
      e.arrival pick cost (fun p => (f p).arrival pick cost input register)
        (fun r => (g r).arrival pick cost input register) := by
  induction e <;> simp_all [Expr.bind, Expr.arrival]

/-- An endpoint with no visible launch point is independent of every launch
point: structural unreachability implies semantic non-interference. -/
theorem Expr.eval_congr_of_arrival_none (e : Expr I R w) (input : Launch I) (register : Launch R)
    (i i' : Values I) (s s' : Values R)
    (hi : ∀ {w : Nat} (p : I w), input p = none → i p = i' p)
    (hs : ∀ {w : Nat} (r : R w), register r = none → s r = s' r)
    (unreached : e.arrival pick cost input register = none) : e.eval i s = e.eval i' s' := by
  induction e with
  | input p => exact hi p unreached
  | reg r => exact hs r unreached
  | lit v => rfl
  | concat x y hx hy =>
    have h := merge_eq_none.mp (after_eq_none.mp unreached)
    simp only [Expr.eval, hx h.1, hy h.2]
  | inv x hx => simp only [Expr.eval, hx (after_eq_none.mp unreached)]
  | band x y hx hy =>
    have h := merge_eq_none.mp (after_eq_none.mp unreached)
    simp only [Expr.eval, hx h.1, hy h.2]
  | sub x y hx hy =>
    have h := merge_eq_none.mp (after_eq_none.mp unreached)
    simp only [Expr.eval, hx h.1, hy h.2]
  | slice start len fits x hx => simp only [Expr.eval, hx (after_eq_none.mp unreached)]
  | equal x y hx hy =>
    have h := merge_eq_none.mp (after_eq_none.mp unreached)
    simp only [Expr.eval, hx h.1, hy h.2]
  | ult x y hx hy =>
    have h := merge_eq_none.mp (after_eq_none.mp unreached)
    simp only [Expr.eval, hx h.1, hy h.2]
  | zero x hx => simp only [Expr.eval, hx (after_eq_none.mp unreached)]
  | mux c t f hc ht hf =>
    have h := merge_eq_none.mp (after_eq_none.mp unreached)
    have h' := merge_eq_none.mp h.2
    simp only [Expr.eval, hc h.1, ht h'.1, hf h'.2]

/-- If no leaf launches, nothing arrives. -/
theorem Expr.arrival_none (e : Expr I R w) (input : Launch I) (register : Launch R)
    (hi : ∀ {w : Nat} (p : I w), input p = none) (hs : ∀ {w : Nat} (r : R w), register r = none) :
    e.arrival pick cost input register = none := by
  induction e <;> simp_all [Expr.arrival, merge, after]

/-- A shared wire launches whenever its defining expression can. -/
def WithWire.arrivals (input : Launch I) (wire : Option Nat) : Launch (WithWire I width)
  | _, .input p => input p
  | _, .wire => wire

/-- Arrival at a register's data input, through every shared wire. -/
def Netlist.arrivalNext : {I : Nat → Type} → Netlist R O I → Launch I → Launch R → Launch R
  | _, .finish c, input, register, _, r => (c.next r).arrival pick cost input register
  | _, .letWire e body, input, register, _, r =>
    body.arrivalNext (WithWire.arrivals input (e.arrival pick cost input register)) register r

def Netlist.arrivalOutput : {I : Nat → Type} → Netlist R O I → Launch I → Launch R → Launch O
  | _, .finish c, input, register, _, o => (c.output o).arrival pick cost input register
  | _, .letWire e body, input, register, _, o =>
    body.arrivalOutput (WithWire.arrivals input (e.arrival pick cost input register)) register o

/-- Evaluate every shared wire once, then hand the final circuit and the arrivals
of its leaves to one consumer. An executable report uses this to avoid
re-deriving wire arrivals for each of several hundred registers. -/
def Netlist.withArrivals : {I : Nat → Type} → Netlist R O I → Launch I → Launch R →
    ({J : Nat → Type} → Circuit J R O → Launch J → α) → α
  | _, .finish c, input, _, consume => consume c input
  | _, .letWire e body, input, register, consume =>
    let wire := e.arrival pick cost input register
    body.withArrivals (WithWire.arrivals input wire) register consume

theorem Netlist.withArrivals_next (n : Netlist R O I) (input : Launch I) (register : Launch R)
    (r : R w) :
    n.withArrivals pick cost input register
        (fun c leaves => (c.next r).arrival pick cost leaves register) =
      n.arrivalNext pick cost input register r := by
  induction n with
  | finish c => rfl
  | letWire e body ih => exact ih _

theorem Netlist.withArrivals_output (n : Netlist R O I) (input : Launch I) (register : Launch R)
    (o : O w) :
    n.withArrivals pick cost input register
        (fun c leaves => (c.output o).arrival pick cost leaves register) =
      n.arrivalOutput pick cost input register o := by
  induction n with
  | finish c => rfl
  | letWire e body ih => exact ih _

/-- A register whose data input sees no launch point takes the same next value
whatever the launch points carry. -/
theorem Netlist.step_congr_of_arrival_none (n : Netlist R O I) (input : Launch I)
    (register : Launch R) (i i' : Values I) (s s' : Values R)
    (hi : ∀ {w : Nat} (p : I w), input p = none → i p = i' p)
    (hs : ∀ {w : Nat} (r : R w), register r = none → s r = s' r)
    (r : R w) (unreached : n.arrivalNext pick cost input register r = none) :
    n.step i s r = n.step i' s' r := by
  induction n with
  | finish c =>
    exact Expr.eval_congr_of_arrival_none pick cost (c.next r) input register i i' s s' hi hs unreached
  | letWire e body ih =>
    refine ih (WithWire.arrivals input (e.arrival pick cost input register))
      (WithWire.values i (e.eval i s)) (WithWire.values i' (e.eval i' s')) ?_ unreached
    intro v p hp
    cases p with
    | input p => exact hi p hp
    | wire => exact Expr.eval_congr_of_arrival_none pick cost e input register i i' s s' hi hs hp

theorem Netlist.observe_congr_of_arrival_none (n : Netlist R O I) (input : Launch I)
    (register : Launch R) (i i' : Values I) (s s' : Values R)
    (hi : ∀ {w : Nat} (p : I w), input p = none → i p = i' p)
    (hs : ∀ {w : Nat} (r : R w), register r = none → s r = s' r)
    (o : O w) (unreached : n.arrivalOutput pick cost input register o = none) :
    n.observe i s o = n.observe i' s' o := by
  induction n with
  | finish c =>
    exact Expr.eval_congr_of_arrival_none pick cost (c.output o) input register i i' s s' hi hs unreached
  | letWire e body ih =>
    refine ih (WithWire.arrivals input (e.arrival pick cost input register))
      (WithWire.values i (e.eval i s)) (WithWire.values i' (e.eval i' s')) ?_ unreached
    intro v p hp
    cases p with
    | input p => exact hi p hp
    | wire => exact Expr.eval_congr_of_arrival_none pick cost e input register i i' s s' hi hs hp

theorem Expr.arrival_weaken (e : Expr I R w) (input : Launch I) (register : Launch R)
    (wire : Option Nat) :
    (e.weaken (width := width)).arrival pick cost (WithWire.arrivals input wire) register =
      e.arrival pick cost input register := by
  simp only [Expr.weaken, Expr.arrival_bind, Expr.arrival, WithWire.arrivals]

theorem Expr.arrival_inner (f : {w : Nat} → I w → Expr J (Extended R X) w) (e : Expr I R w)
    (input : Launch J) (register : Launch (Extended R X)) :
    (e.inner f).arrival pick cost input register =
      e.arrival pick cost (fun p => (f p).arrival pick cost input register)
        (fun r => register (.inner r)) := by
  simp only [Expr.inner, Expr.arrival_bind, Expr.arrival]

theorem belowWire_arrival (f : {w : Nat} → I w → Expr J S w) (input : Launch J)
    (register : Launch S) (wire : Option Nat) :
    (fun {w} (p : WithWire I width w) =>
        (belowWire f p).arrival pick cost (WithWire.arrivals input wire) register) =
      (WithWire.arrivals (fun {w} (p : I w) => (f p).arrival pick cost input register) wire :
        Launch (WithWire I width)) := by
  funext w p
  cases p <;> simp only [belowWire, Expr.arrival_weaken, Expr.arrival, WithWire.arrivals]

/-- Timing law of a wrapper: an inner register's arrival is the inner netlist's,
with each inner input arriving when the expression wired into it does. -/
theorem Netlist.arrivalNext_extend (n : Netlist R O I)
    (f : {w : Nat} → I w → Expr J (Extended R X) w)
    (extra : {w : Nat} → X w → Expr J (Extended R X) w)
    (input : Launch J) (register : Launch (Extended R X)) (r : R w) :
    (n.extend f extra).arrivalNext pick cost input register (.inner r) =
      n.arrivalNext pick cost (fun p => (f p).arrival pick cost input register)
        (fun r => register (.inner r)) r := by
  induction n generalizing J with
  | finish c => simp only [Netlist.extend, Netlist.arrivalNext, Expr.arrival_inner]
  | letWire e body ih =>
    simp only [Netlist.extend, Netlist.arrivalNext, ih, belowWire_arrival, Expr.arrival_inner]

theorem Netlist.arrivalNext_extend_extra (n : Netlist R O I)
    (f : {w : Nat} → I w → Expr J (Extended R X) w)
    (extra : {w : Nat} → X w → Expr J (Extended R X) w)
    (input : Launch J) (register : Launch (Extended R X)) (x : X w) :
    (n.extend f extra).arrivalNext pick cost input register (.extra x) =
      (extra x).arrival pick cost input register := by
  induction n generalizing J with
  | finish c => simp only [Netlist.extend, Netlist.arrivalNext]
  | letWire e body ih =>
    simp only [Netlist.extend, Netlist.arrivalNext, ih, Expr.arrival_weaken]

theorem Netlist.arrivalOutput_extend (n : Netlist R O I)
    (f : {w : Nat} → I w → Expr J (Extended R X) w)
    (extra : {w : Nat} → X w → Expr J (Extended R X) w)
    (input : Launch J) (register : Launch (Extended R X)) (o : O w) :
    (n.extend f extra).arrivalOutput pick cost input register o =
      n.arrivalOutput pick cost (fun p => (f p).arrival pick cost input register)
        (fun r => register (.inner r)) o := by
  induction n generalizing J with
  | finish c => simp only [Netlist.extend, Netlist.arrivalOutput, Expr.arrival_inner]
  | letWire e body ih =>
    simp only [Netlist.extend, Netlist.arrivalOutput, ih, belowWire_arrival, Expr.arrival_inner]

/-- With nothing launching, no register's data input sees an arrival. -/
theorem Netlist.arrivalNext_none (n : Netlist R O I) (input : Launch I) (register : Launch R)
    (hi : ∀ {w : Nat} (p : I w), input p = none) (hs : ∀ {w : Nat} (r : R w), register r = none)
    (r : R w) : n.arrivalNext pick cost input register r = none := by
  induction n with
  | finish c => exact Expr.arrival_none pick cost (c.next r) input register hi hs
  | letWire e body ih =>
    refine ih (WithWire.arrivals input (e.arrival pick cost input register)) ?_
    intro v p
    cases p with
    | input p => exact hi p
    | wire => exact Expr.arrival_none pick cost e input register hi hs

theorem Netlist.arrivalOutput_none (n : Netlist R O I) (input : Launch I) (register : Launch R)
    (hi : ∀ {w : Nat} (p : I w), input p = none) (hs : ∀ {w : Nat} (r : R w), register r = none)
    (o : O w) : n.arrivalOutput pick cost input register o = none := by
  induction n with
  | finish c => exact Expr.arrival_none pick cost (c.output o) input register hi hs
  | letWire e body ih =>
    refine ih (WithWire.arrivals input (e.arrival pick cost input register)) ?_
    intro v p
    cases p with
    | input p => exact hi p
    | wire => exact Expr.arrival_none pick cost e input register hi hs

end

end Pinwheel.Hardware
