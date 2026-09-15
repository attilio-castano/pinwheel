import Pinwheel.Hardware.Circuit
import Pinwheel.Hardware.Timed

namespace Pinwheel.Hardware

/-- A finite, complete interface. Names identify distinct slots; the inverse
lookup guarantees that no typed signal is omitted. Widths remain in `Port`. -/
structure Interface (Port : Nat → Type) where
  size : Nat
  signal : Fin size → Sigma Port
  position : {w : Nat} → Port w → Fin size
  signal_position : ∀ {w} (p : Port w), signal (position p) = ⟨w, p⟩
  label : {w : Nat} → Port w → String
  unique : ∀ a b, label (signal a).2 = label (signal b).2 → a = b

namespace Interface

def ports (d : Interface P) : Array (Sigma P) := Array.ofFn d.signal

/-- Evaluate in declared order, then access results by typed signal identity.
In particular, emission names never participate in lookup. -/
def mapM [Monad m] (d : Interface P) (f : {w : Nat} → P w → m α) :
    m ({w : Nat} → P w → α) := do
  let values ← Vector.ofFnM (fun k => f (d.signal k).2)
  return fun p => values[(d.position p).val]

def rename (d : Interface P) (label : {w : Nat} → P w → String)
    (unique : ∀ a b, label (d.signal a).2 = label (d.signal b).2 → a = b) : Interface P :=
  {d with label := label, unique := unique}

/-- Presentation changes cannot alter traversal order or typed lookup. -/
theorem rename_mapM [Monad m] (d : Interface P) (label : {w : Nat} → P w → String)
    (unique : ∀ a b, label (d.signal a).2 = label (d.signal b).2 → a = b)
    (f : {w : Nat} → P w → m α) : (d.rename label unique).mapM f = d.mapM f := rfl

theorem position_signal (d : Interface P) (k : Fin d.size) :
    d.position (d.signal k).2 = k := by
  exact d.unique _ _ (congrArg (fun p : Sigma P => d.label p.2) (d.signal_position (d.signal k).2))

theorem mapM_pure [Monad m] [LawfulMonad m] (d : Interface P) (f : {w : Nat} → P w → α) :
    d.mapM (m := m) (fun p => pure (f p)) = pure (@f) := by
  simp only [mapM, Vector.ofFnM_pure, pure_bind, Vector.getElem_ofFn]
  exact congrArg pure (funext fun w => funext fun p =>
    congrArg (fun q : Sigma P => f q.2) (d.signal_position p))
  done

structure Observation where
  signal : String
  width : Nat
  value : Nat
  deriving DecidableEq, Repr

def observe (d : Interface P) (values : Values P) : Array Observation :=
  d.ports.map fun ⟨w, p⟩ => ⟨d.label p, w, (values p).toNat⟩

def namedComponent (d : Interface P) (c : Timed.Component I S (Values P)) :
    Timed.Component I S (Array Observation) :=
  ⟨c.step, fun i s => d.observe (c.observe i s)⟩

/-- Naming observations preserves the existing same-edge refinement. -/
def namedRefinement (d : Interface P)
    {impl : Timed.Component I S (Values P)} {spec : Timed.Component I T (Values P)}
    (r : Timed.Refinement impl spec) :
    Timed.Refinement (d.namedComponent impl) (d.namedComponent spec) where
  Rel := r.Rel
  step := r.step
  observe := fun i s t h => congrArg d.observe (r.observe i s t h)

inductive Phase where
  | before | after
  deriving DecidableEq, Repr

def Phase.label : Phase → String | .before => "before" | .after => "after"

structure Mismatch where
  cycle : Nat
  phase : Phase
  component : String
  signal : String
  width : Nat
  expected : Nat
  actual : Nat
  deriving DecidableEq, Repr

def Mismatch.describe (m : Mismatch) : String :=
  s!"cycle {m.cycle} {m.phase.label} {m.component}.{m.signal} ({m.width} bits): expected {m.expected}, got {m.actual}"

def differences (d : Interface P) (cycle : Nat) (component : String) (phase : Phase)
    (expected actual : Values P) : Array Mismatch :=
  d.ports.filterMap fun ⟨w, p⟩ =>
    if expected p == actual p then none
    else some ⟨cycle, phase, component, d.label p, w, (expected p).toNat, (actual p).toNat⟩

/-- Compare both settled observations using the interface's complete enumeration. -/
def edgeDifferences (d : Interface P) (cycle : Nat) (component : String)
    (expected actual : Values P × Values P) : Array Mismatch :=
  d.differences cycle component .before expected.1 actual.1 ++
    d.differences cycle component .after expected.2 actual.2

/-- A clean comparison cannot hide a signal omitted from the interface. -/
theorem differences_empty_iff (d : Interface P) (cycle : Nat) (component : String) (phase : Phase)
    (expected actual : Values P) :
    d.differences cycle component phase expected actual = #[] ↔
      ∀ {w} (p : P w), expected p = actual p := by
  simp only [differences, Array.filterMap_eq_empty_iff]
  constructor
  · intro h w p
    have hm : (⟨w, p⟩ : Sigma P) ∈ d.ports := Array.mem_ofFn.mpr ⟨d.position p, d.signal_position p⟩
    simpa using h ⟨w, p⟩ hm
  · intro h p _
    simp [h]
  done

end Interface
end Pinwheel.Hardware
