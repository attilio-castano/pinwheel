import Pinwheel.Hardware.StreamingPhysical.Packing
import Pinwheel.Hardware.StreamingReady.Package

/-! The physical storage basis contains every original frontend and core bit.
No constant, unreachable-state, or ghost-counter constraint is imposed. -/
namespace Pinwheel.Hardware.StreamingPhysical
open Pinwheel.Hardware

deriving instance DecidableEq for Streaming.Frontend.Register
deriving instance DecidableEq for Streaming.Core.Register

inductive Register : Nat → Type where
  | frontend : Streaming.Frontend.Register width → Register width
  | core : Streaming.Core.Register 1 width → Register width
  deriving DecidableEq

def stateValues (state : StreamingReady.Package.State 1) : Values Register
  | _, .frontend field => state.frontend field
  | _, .core field => state.core field

def packageState (values : Values Register) : StreamingReady.Package.State 1 :=
  ⟨fun field => values (.frontend field),fun field => values (.core field)⟩

theorem packageState_stateValues (state : StreamingReady.Package.State 1) :
    packageState (stateValues state) = state := by cases state; rfl

theorem stateValues_packageState (values : Values Register) :
    (@stateValues (packageState values)) = @values := by
  funext width field
  cases field <;> rfl

end Pinwheel.Hardware.StreamingPhysical
