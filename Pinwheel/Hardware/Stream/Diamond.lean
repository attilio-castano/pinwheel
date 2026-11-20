import Pinwheel.Hardware.Stream.Bundle
import Pinwheel.Hardware.Stream.Properties

namespace Pinwheel.Hardware.Stream

set_option backward.isDefEq.respectTransparency false

def increment (w : Nat) : Map w w where
  expression := (Expr.input .data).plus (.lit 1)
  function := fun x => x + 1
  correct := by intro v; simp [Expr.eval, dataValues]

def complement (w : Nat) : Map w w where
  expression := .inv (.input .data)
  function := fun x => ~~~x
  correct := fun _ => rfl

/-- A positive stage count is checked at the CLI. As in Design.pipeline, the
library parameter counts additional stages beyond the mandatory first one. -/
def diamondDesign (w leftExtra rightExtra : Nat) : Design w (w + w) :=
  .parallel (.pipeline (increment w) leftExtra) (.pipeline (complement w) rightExtra)

def diamondPayload (w : Nat) : Bundle := .pair (.bits "incremented" w) (.bits "complemented" w)

def diamondPayloadInterface (w : Nat) : Interface (diamondPayload w).Port :=
  (diamondPayload w).interface (by
    intro a b
    match a, b with
    | ⟨0, _⟩, ⟨0, _⟩ | ⟨1, _⟩, ⟨1, _⟩ => intro _; rfl
    | ⟨0, _⟩, ⟨1, _⟩ | ⟨1, _⟩, ⟨0, _⟩ => intro h; simp [diamondPayload, Bundle.label, Bundle.shape, Joint.interface, Joint.signal] at h
    | ⟨k + 2, h⟩, _ | _, ⟨k + 2, h⟩ => exact False.elim (by change k + 2 < 2 at h; omega))

theorem diamond_capacity (w l r : Nat) : Bounded (diamondDesign w l r).flatten (min (l + 1) (r + 1)) :=
  bounded_parallel _ _ (bounded_pipeline (increment w) l) (bounded_pipeline (complement w) r)

theorem diamond_stable (w l r : Nat) : Stable (diamondDesign w l r).flatten.machine :=
  stable_parallel _ _ _ (stable_pipeline (increment w) l) (stable_pipeline (complement w) r)

theorem diamond_function (w l r : Nat) (x : BitVec w) :
    (diamondDesign w l r).flatten.function x = (x + 1) ++ (~~~x) := by
  change (Design.pipeline (increment w) l).flatten.function x ++
    (Design.pipeline (complement w) r).flatten.function x = (x + 1) ++ (~~~x)
  rw [Design.pipeline_function, Design.pipeline_function]
  rfl

/-- The explicit arithmetic statement, universally quantified over width,
branch depth, traffic, backpressure and reset epochs. -/
theorem diamond_transactions (w l r : Nat) (inputs : List (Input (BitVec w))) :
    let c := (diamondDesign w l r).flatten
    let actual := runHistory c.simulator (c.encode c.initial) {} inputs
    let model := runHistory c.machine.component c.initial {} inputs
    actual.2.inputs.map (fun x => (x + 1) ++ (~~~x)) = actual.2.outputs ++ c.contract.pending model.1 := by
  have h := (diamondDesign w l r).flatten.simulator_transactions inputs
  simpa only [show (diamondDesign w l r).flatten.function = (fun x => (x + 1) ++ (~~~x)) from
    funext (diamond_function w l r)] using h

end Pinwheel.Hardware.Stream
