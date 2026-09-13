import Std

namespace Pinwheel.I2C

/-- Open-drain commands cannot actively drive high. -/
inductive Drive where
  | low
  | release
  deriving DecidableEq, Repr

structure Pins where
  scl : Drive := .release
  sda : Drive := .release
  deriving DecidableEq, Repr

structure Bus where
  scl : Bool := true
  sda : Bool := true
  deriving DecidableEq, Repr

/-- Ideal pull-ups: high exactly when both participants release the line. -/
def resolveLine (controller target : Drive) : Bool :=
  controller == .release && target == .release

def resolve (controller target : Pins) : Bus :=
  ⟨resolveLine controller.scl target.scl, resolveLine controller.sda target.sda⟩

theorem low_dominates (other : Drive) : resolveLine .low other = false := by
  rfl

theorem release_observes_target (target : Drive) :
    resolveLine .release target = (target == .release) := by
  cases target <;> rfl

theorem resolve_comm (a b : Drive) : resolveLine a b = resolveLine b a := by
  cases a <;> cases b <;> rfl

end Pinwheel.I2C
