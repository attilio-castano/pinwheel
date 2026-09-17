import Pinwheel.Hardware.Countdown
import Pinwheel.Hardware.Timed

namespace Pinwheel.Hardware.Countdown

/-- Named observations, including the combinational boundary on either side of an edge. -/
def observations (i : Inputs) (s : State) : State × Bool := (s, boundary i s)

def component : Timed.Component Inputs State (State × Bool) :=
  ⟨tick, observations⟩

/-- A checked one-edge artifact interpretation suffices for every finite input history.
The initial states are related by equality; no arbitrary power-up values are assumed equal. -/
theorem artifact_trace (step : Inputs → State → State) (observe : Inputs → State → State × Bool)
    (hs : ∀ i s, step i s = tick i s) (ho : ∀ i s, observe i s = observations i s)
    (s : State) (inputs : List Inputs) :
    (Timed.Component.mk step observe).trace s inputs = component.trace s inputs := by
  have h : Timed.Component.mk step observe = component := by
    exact congr (congrArg Timed.Component.mk (funext fun i => funext (hs i)))
      (funext fun i => funext (ho i))
  rw [h]
  done

end Pinwheel.Hardware.Countdown
