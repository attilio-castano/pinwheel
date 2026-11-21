import Pinwheel.Hardware.TimedPairs

/-! Event traces permit several implementation edges between observable
transitions. The event extractor and environment admission predicate are fixed
parameters, not witnesses chosen by a refinement proof. Finite-prefix safety
does not imply eventual events or termination. Environment effects such as
timer ticks must remain events when the contract observes them.
-/
namespace Pinwheel.Hardware.Timed

structure EventSpec (State Event : Type) where
  step : State → Event → State → Prop

/-- An empty event path cannot change the abstract state. -/
inductive EventSpec.Path (spec : EventSpec A E) : A → List E → A → Prop
  | nil (a : A) : spec.Path a [] a
  | cons {a b c : A} {event : E} {rest : List E} :
      spec.step a event b → spec.Path b rest c → spec.Path a (event :: rest) c

theorem EventSpec.Path.nil_iff {spec : EventSpec A E} {a b : A} :
    spec.Path a [] b ↔ a = b := by
  constructor
  · intro h; cases h; rfl
  · intro h; cases h; exact .nil _

theorem EventSpec.Path.append {spec : EventSpec A E} {a b c : A} {xs ys : List E}
    (first : spec.Path a xs b) (second : spec.Path b ys c) :
    spec.Path a (xs ++ ys) c := by
  induction first with
  | nil => exact second
  | cons h _ ih => exact .cons h (ih second)

def Component.eventTrace (impl : Component I S O) (emit : I → S → List E)
    (s : S) : List I → List E
  | [] => []
  | i :: rest => emit i s ++ impl.eventTrace emit (impl.step i s) rest

/-- Admission is checked at every actual implementation state. Protocol
history, if needed, belongs in a separately specified environment monitor. -/
def Component.Legal (impl : Component I S O) (allowed : I → S → Prop)
    (s : S) : List I → Prop
  | [] => True
  | i :: rest => allowed i s ∧ impl.Legal allowed (impl.step i s) rest

structure EventRefinement (impl : Component I S O) (spec : EventSpec A E)
    (emit : I → S → List E) (allowed : I → S → Prop) where
  Rel : S → A → Prop
  edge : ∀ i s a, Rel s a → allowed i s →
    ∃ b, spec.Path a (emit i s) b ∧ Rel (impl.step i s) b

variable {impl : Component I S O} {spec : EventSpec A E}
  {emit : I → S → List E} {allowed : I → S → Prop}

/-- Every finite legal input prefix has exactly the emitted abstract path.
There is no fairness or eventual-retirement conclusion. -/
theorem EventRefinement.trace (r : EventRefinement impl spec emit allowed)
    (s : S) (a : A) (inputs : List I) (h : r.Rel s a)
    (legal : impl.Legal allowed s inputs) :
    ∃ b, spec.Path a (impl.eventTrace emit s inputs) b ∧
      r.Rel (impl.run s inputs) b := by
  induction inputs generalizing s a with
  | nil => exact ⟨a, .nil _, h⟩
  | cons i rest ih =>
    obtain ⟨middle, first, related⟩ := r.edge i s a h legal.1
    obtain ⟨last, remaining, final⟩ := ih _ _ related legal.2
    exact ⟨last, first.append remaining, final⟩

/-- Initial coverage is separate from simulation. Inhabited admission rules
out an empty initial domain, and every admitted start must be related. This
does not replace a hardware reset-recovery or loader/image theorem. -/
structure EventRefinement.InitialCoverage (r : EventRefinement impl spec emit allowed)
    (initial : S → Prop) (abstractInitial : A → Prop) where
  nonempty : ∃ s, initial s
  covered : ∀ s, initial s → ∃ a, abstractInitial a ∧ r.Rel s a

theorem EventRefinement.initialized_trace (r : EventRefinement impl spec emit allowed)
    (coverage : r.InitialCoverage initial abstractInitial)
    (s : S) (hs : initial s) (inputs : List I) (legal : impl.Legal allowed s inputs) :
    ∃ a b, abstractInitial a ∧ spec.Path a (impl.eventTrace emit s inputs) b ∧
      r.Rel (impl.run s inputs) b := by
  obtain ⟨a, ha, hr⟩ := coverage.covered s hs
  obtain ⟨b, path, last⟩ := r.trace s a inputs hr legal
  exact ⟨a, b, ha, path, last⟩

/-- Lift event safety through a cycle-for-cycle refinement. Events must agree
on related states; port equality alone does not justify hidden-state events. -/
def EventRefinement.ofLockstep {physical : Component I P O}
    (cycle : Refinement physical impl) (events : EventRefinement impl spec emit allowed)
    (physicalEmit : I → P → List E) (physicalAllowed : I → P → Prop)
    (faithful : ∀ i p s, cycle.Rel p s → physicalEmit i p = emit i s)
    (admitted : ∀ i p s, cycle.Rel p s → physicalAllowed i p → allowed i s) :
    EventRefinement physical spec physicalEmit physicalAllowed where
  Rel p a := ∃ s, cycle.Rel p s ∧ events.Rel s a
  edge := by
    intro i p a ⟨s, hp, hs⟩ hi
    obtain ⟨b, path, related⟩ := events.edge i s a hs (admitted i p s hp hi)
    exact ⟨b, faithful i p s hp ▸ path, impl.step i s, cycle.step i p s hp, related⟩

/-- Event extraction from ports inherits faithfulness directly. The observer
must describe edge events (for example accepted handshakes), not arbitrary
samples that may be counted twice before and after the same edge. -/
theorem Refinement.port_events {physical : Component I P O}
    (cycle : Refinement physical impl) (extract : I → O → List E)
    (i : I) (p : P) (s : S) (h : cycle.Rel p s) :
    extract i (physical.observe i p) = extract i (impl.observe i s) :=
  congrArg (extract i) (cycle.observe i p s h)

def Component.serviceCount (impl : Component I S O) (service : I → S → Bool)
    (s : S) : List I → Nat
  | [] => 0
  | i :: rest => (if service i s then 1 else 0) +
      impl.serviceCount service (impl.step i s) rest

def Component.Occurs (impl : Component I S O) (finished : I → S → Prop)
    (s : S) : List I → Prop
  | [] => False
  | i :: rest => finished i s ∨ impl.Occurs finished (impl.step i s) rest

/-- A separate finite progress certificate. An unresolved edge cannot
increase rank and consumes one rank unit when `service` is true. No eventual
service is assumed or concluded. For retirement progress, `finished` must mean
retirement/trap, not merely a timer tick or another observable event. Reset
exclusion or abort treatment must be stated in these fixed predicates. -/
structure ProgressBound (impl : Component I S O) (allowed finished : I → S → Prop)
    (service : I → S → Bool) where
  rank : S → Nat
  step : ∀ i s, allowed i s → ¬ finished i s →
    rank (impl.step i s) + (if service i s then 1 else 0) ≤ rank s

/-- Without an outcome, the observed service count is bounded by the initial
rank. This is a finite-prefix theorem, not an environment fairness theorem. -/
theorem ProgressBound.unfinished_bound
    (p : ProgressBound impl allowed finished service)
    (s : S) (inputs : List I) (legal : impl.Legal allowed s inputs)
    (unfinished : ¬ impl.Occurs finished s inputs) :
    impl.serviceCount service s inputs + p.rank (impl.run s inputs) ≤ p.rank s := by
  induction inputs generalizing s with
  | nil => simp only [Component.serviceCount, Component.run, Nat.zero_add, Nat.le_refl]
  | cons i rest ih =>
    have hn : ¬ finished i s ∧ ¬ impl.Occurs finished (impl.step i s) rest :=
      not_or.mp unfinished
    have edge := p.step i s legal.1 hn.1
    have remaining := ih _ legal.2 hn.2
    change (if service i s then 1 else 0) + impl.serviceCount service (impl.step i s) rest +
      p.rank (impl.run (impl.step i s) rest) ≤ p.rank s
    omega

/-- More service opportunities than the initial rank force an actual outcome.
A wall-clock bound additionally needs an independently proved service bound. -/
theorem ProgressBound.occurs_of_service_count
    (p : ProgressBound impl allowed finished service)
    (s : S) (inputs : List I) (legal : impl.Legal allowed s inputs)
    (enough : p.rank s < impl.serviceCount service s inputs) :
    impl.Occurs finished s inputs := by
  apply Classical.byContradiction
  intro h
  have bound := p.unfinished_bound s inputs legal h
  omega

end Pinwheel.Hardware.Timed
