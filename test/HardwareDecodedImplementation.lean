import Lean
import Pinwheel.Hardware.DecodedImplementation

open Lean Elab Command
open Pinwheel.Hardware

namespace HardwareDecodedImplementationTests

inductive Input : Nat → Type where
  | reset : Input 1
  | load : Input 1
  | clear : Input 1
  | data : Input 8

inductive Register : Nat → Type where
  | word : Register 8
  | active : Register 1
  | metadata : Register 8

inductive Output : Nat → Type where
  | word : Output 8
  | valid : Output 1
  | data : Output 8

/-- The logical image retains a storage word but forgets inactive metadata. -/
abbrev State := BitVec 8 × Option (BitVec 8)

def view (r : Values Register) : State :=
  (r .word, if r .active = 1 then some (r .metadata) else none)

def circuit : Circuit Input Register Output where
  next p := match p with
    | .word => .reg .word
    | .active => .mux (.input .reset) (.lit 0)
        (.mux (.input .load) (.lit 1) (.mux (.input .clear) (.lit 0) (.reg .active)))
    | .metadata => .mux (.input .reset) (.reg .metadata)
        (.mux (.input .load) (.input .data) (.reg .metadata))
  output p := match p with
    | .word => .reg .word
    | .valid => .mux (.input .reset) (.lit 0) (.mux (.reg .active) (.lit 1) (.lit 0))
    | .data => .mux (.input .reset) (.lit 0) (.mux (.reg .active) (.reg .metadata) (.lit 0))

def spec : Timed.Component (Values Input) State (Values Output) where
  step i s := (s.1, if i .reset = 1 then none else if i .load = 1 then some (i .data)
    else if i .clear = 1 then none else s.2)
  observe i s := fun p => match p with
    | .word => s.1
    | .valid => if i .reset = 1 then 0 else if s.2.isSome then 1 else 0
    | .data => if i .reset = 1 then 0 else s.2.getD 0

theorem step_view (i : Values Input) (r : Values Register) :
    view (circuit.step i r) = spec.step i (view r) := by
  by_cases hr : i .reset = 1#1 <;> by_cases hl : i .load = 1#1 <;>
    by_cases hc : i .clear = 1#1 <;> simp [view, circuit, Circuit.step, Expr.eval, spec, hr, hl, hc]

theorem output_view (i : Values Input) (r : Values Register) (o : Output b) :
    circuit.observe i r o = spec.observe i (view r) o := by
  cases o <;> by_cases hr : i .reset = 1#1 <;> by_cases hp : r .active = 1#1 <;>
    simp [view, circuit, Circuit.observe, Expr.eval, spec, hr, hp]

def implementation : DecodedImplementation circuit spec where
  Valid _ := True
  view := view
  preserved _ _ _ := trivial
  step_eq i r _ := step_view i r
  output_eq i r _ _ o := output_view i r o

def resetProjection : implementation.Reset .reset where
  initial r := (r .word, none)
  reset_valid _ _ _ := trivial
  reset_view i r hr := by simp [implementation, view, circuit, Circuit.step, Expr.eval, hr]

theorem reset_retains (i : Values Input) (r : Values Register) (hr : i .reset = 1) :
    circuit.step i r .word = r .word ∧ circuit.step i r .metadata = r .metadata ∧
      circuit.step i r .active = 0 := by
  simp [Circuit.step, circuit, Expr.eval, hr]

def raw (word : BitVec 8) (active : BitVec 1) (metadata : BitVec 8) : Values Register :=
  fun p => match p with
    | .word => word
    | .active => active
    | .metadata => metadata

def pins (reset load clear : BitVec 1) (data : BitVec 8) : Values Input :=
  fun p => match p with
    | .reset => reset
    | .load => load
    | .clear => clear
    | .data => data

theorem inactive_views (word first second : BitVec 8) :
    view (raw word 0 first) = view (raw word 0 second) := rfl

theorem inactive_states_differ (word first second : BitVec 8) (h : first ≠ second) :
    @raw word 0 first ≠ @raw word 0 second := by
  intro heq
  exact h (congrArg (fun r : Values Register => r .metadata) heq)

/-- These equal traces do not imply equal physical states: inactive metadata is
unobservable but persists through quiet edges, including reset edges. -/
theorem inactive_traces (word first second : BitVec 8) (traffic : List (Values Input)) :
    circuit.component.trace (raw word 0 first) traffic =
      circuit.component.trace (raw word 0 second) traffic := by
  rw [implementation.trace_eq _ trivial, implementation.trace_eq _ trivial]
  rfl

theorem projected_run (r : Values Register) (traffic : List (Values Input)) :
    view (circuit.component.run r traffic) = spec.run (view r) traffic :=
  implementation.run_eq r trivial traffic

/-- No external RTL certificate is invented: every imported-component claim
below keeps the exact raw-state correspondence as an explicit premise. -/
theorem artifact_projection
    {rtl : Timed.Component (Values Input) (Values Register) (Values Output)}
    (artifact : Artifact.Correspondence circuit rtl) (r : Values Register)
    (traffic : List (Values Input)) :
    rtl.trace r traffic = spec.trace (view r) traffic ∧
      view (rtl.run r traffic) = spec.run (view r) traffic :=
  ⟨implementation.artifact_trace_eq artifact r trivial traffic,
    implementation.artifact_run_eq artifact r trivial traffic⟩

theorem artifact_reset_projection
    {rtl : Timed.Component (Values Input) (Values Register) (Values Output)}
    (artifact : Artifact.Correspondence circuit rtl) (i : Values Input) (r : Values Register)
    (hr : i .reset = 1) (traffic : List (Values Input)) :
    rtl.trace (rtl.step i r) traffic = spec.trace (r .word, none) traffic ∧
      view (rtl.run (rtl.step i r) traffic) = spec.run (r .word, none) traffic :=
  ⟨resetProjection.artifact_trace_after_reset implementation .reset artifact i r hr traffic,
    resetProjection.artifact_run_after_reset implementation .reset artifact i r hr traffic⟩

example (artifact : Artifact.Correspondence circuit rtl) (r : Values Register) :
    (implementation.toArtifact artifact).Rel r (view r) := ⟨r, rfl, trivial, rfl⟩

/-- Reset masks an asserted load, clears validity, and preserves both bytes.
The two raw results remain distinct although their projected states agree. -/
example :
    let first : Values Register := circuit.step (pins 1 1 1 99) (raw 77 0 165)
    let second : Values Register := circuit.step (pins 1 1 1 99) (raw 77 0 60)
    view first = (77, none) ∧ view second = (77, none) ∧
      first .metadata = 165 ∧ second .metadata = 60 ∧ first .metadata ≠ second .metadata := by
  decide +kernel

/-- Clearing a loaded entry erases it only from the projection. Its metadata
and the original logical storage word survive the final inactive edge. -/
example :
    let final : Values Register := circuit.component.run (raw 77 1 165) [pins 1 1 1 99, pins 0 1 0 60, pins 0 0 1 9]
    view final = (77, none) ∧ final .metadata = 60 ∧ final .word = 77 := by
  decide +kernel

theorem imported_retained_metadata
    {rtl : Timed.Component (Values Input) (Values Register) (Values Output)}
    (artifact : Artifact.Correspondence circuit rtl) (word metadata : BitVec 8) :
    let result : Values Register := rtl.run (rtl.step (pins 1 1 1 99) (raw word 0 metadata)) [pins 0 0 0 255]
    view result = (word, none) ∧ result .metadata = metadata := by
  rw [artifact.run_eq, artifact.step_eq]
  exact ⟨rfl, rfl⟩

end HardwareDecodedImplementationTests

elab "#audit_decoded_implementation" : command => do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let selected := name == ``DecodedImplementation ||
      name.toString.startsWith "Pinwheel.Hardware.DecodedImplementation." ||
      name.toString.startsWith "_private.Pinwheel.Hardware.DecodedImplementation." ||
      name.toString.startsWith "HardwareDecodedImplementationTests." ||
      name.toString.startsWith "_private.test.HardwareDecodedImplementation."
    if selected then
      count := count+1
      let axioms ← collectAxioms name
      let bad := axioms.filter fun a => a != ``propext && a != ``Classical.choice && a != ``Quot.sound
      unless bad.isEmpty do throwError "Unapproved decoded implementation axioms in {name}: {bad}"
  if count < 20 then throwError "Incomplete decoded implementation audit"
  logInfo m!"Decoded implementation audit: {count} declarations, standard axioms only."

#audit_decoded_implementation

def main : IO Unit :=
  IO.println "Decoded implementation: arbitrary retained bytes, noninjective inactive metadata, reset, traces, and final projected state kernel-checked; external artifact correspondence remains an explicit premise."
