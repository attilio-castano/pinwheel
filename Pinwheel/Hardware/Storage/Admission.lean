import Pinwheel.Hardware.Storage.ImageRule
import Pinwheel.Hardware.TimedRule

/-! A rule on program words, enforced instead of assumed.

The small backend already turns a push it cannot hold into a rejection (the
capacity check). The same filter discharges any rule on pushed words: behind it
a rule-conditional refinement holds for every input history, against the
reference behind the same filter. For programs that satisfy the rule the filter
changes nothing. `AdmissionNetlist` implements this gate while preserving
independent commit/start decoding; `OnePortAdmission` supplies the readiness
predicate used by the admitted one-port result chip. -/
namespace Pinwheel.Hardware.Storage.Admission
open Loader

/-- Turn a push of a word outside `A` into a rejection (command 6). -/
def admit (A : BitVec 64 → Bool) (i : Machine.Inputs) : Machine.Inputs :=
  {i with command := if i.command == 2 && !A i.data then 6 else i.command}

/-- What survives the filter as a push is admissible. -/
theorem admit_rule (A : BitVec 64 → Bool) (i : Machine.Inputs) :
    (admit A i).command = 2 → A (admit A i).data = true := by
  intro hc
  show A i.data = true
  cases hA : A i.data
  · exfalso
    cases hcmd : (i.command == 2)
    · have hcond : (i.command == 2 && !A i.data) = false := by rw [hcmd]; rfl
      have hsame : (admit A i).command = i.command := by
        unfold admit
        rw [hcond]
        rfl
      rw [hsame] at hc
      rw [hc] at hcmd
      exact absurd hcmd (by decide)
    · have hcond : (i.command == 2 && !A i.data) = true := by rw [hcmd, hA]; rfl
      have hreject : (admit A i).command = 6 := by
        unfold admit
        rw [hcond]
        rfl
      rw [hreject] at hc
      exact absurd hc (by decide)
  · rfl

/-- The filter never creates a push. -/
theorem admit_command (A : BitVec 64 → Bool) (i : Machine.Inputs) (hc : (admit A i).command = 2) :
    i.command = 2 := by
  cases hcmd : (i.command == 2)
  · have hcond : (i.command == 2 && !A i.data) = false := by rw [hcmd]; rfl
    have hsame : (admit A i).command = i.command := by
      unfold admit
      rw [hcond]
      rfl
    rw [hsame] at hc
    exact hc
  · simpa using hcmd

/-- On inputs that satisfy the rule the filter is the identity. -/
theorem admit_of_rule (A : BitVec 64 → Bool) (i : Machine.Inputs) (h : i.command = 2 → A i.data = true) :
    admit A i = i := by
  have hcond : (i.command == 2 && !A i.data) = false := by
    cases hcmd : (i.command == 2)
    · rfl
    · have hA := h (by simpa using hcmd)
      simp [hA]
  unfold admit
  rw [hcond]
  rfl

/-- A refinement conditional on "every push carries an admissible word" is
unconditional behind the filter. -/
def discharge {S T O : Type} {impl : Timed.Component Machine.Inputs S O}
    {spec : Timed.Component Machine.Inputs T O} (A : BitVec 64 → Bool)
    (r : Timed.RuleRefinement impl spec (fun i => i.command = 2 → A i.data = true)) :
    Timed.Refinement (impl.precompose (admit A)) (spec.precompose (admit A)) :=
  r.precompose (admit A) (admit_rule A)

end Pinwheel.Hardware.Storage.Admission
