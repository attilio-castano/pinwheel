import Pinwheel.Hardware.Switch.CircuitProofs
import Pinwheel.Hardware.Implementation
import Pinwheel.Hardware.Artifact

namespace Pinwheel.Hardware.Switch.Structural

open Physical

/-- The switch's protocol proof stays in its model; this certificate adds a
physical implementation without imposing a single-channel stream interface. -/
def implementation (e : DestinationEncoding (m+1)) (n w depth : Nat) (hd : 0 < depth) :
    Implementation (circuit e n w depth) (Physical.component e depth) where
  Valid := Switch.Valid depth
  encode := encode e
  preserved := fun i s h => Switch.valid_preserved depth (decode (readPins i)) s h
  step_eq := fun i s h _ r => step_eq e s h i r
  output_eq := fun i s h _ o => output_eq e s h hd i o

def resetCertificate (e : DestinationEncoding (m+1)) (n w depth : Nat) (hd : 0 < depth) :
    (implementation e n w depth hd).Reset Physical.reset where
  initial := Switch.initial
  initial_valid := Switch.initial_valid depth
  reset_eq := fun i s h _ r => reset_eq e i s h r

theorem initialized_trace (e : DestinationEncoding (m+1)) (n w depth : Nat) (hd : 0 < depth)
    (i : Values (In n m e.width w)) (s : Values (Register n m e.width w depth))
    (h : i Physical.reset = 1) (inputs : List (Values (In n m e.width w))) :
    (circuit e n w depth).component.trace ((circuit e n w depth).step i s) inputs =
      (Physical.component e depth).trace Switch.initial inputs :=
  (resetCertificate e n w depth hd).trace_after_reset
    (implementation e n w depth hd) Physical.reset i s h inputs

/-- Artifact correspondence and structural refinement compose without exposing
the FIFO representation or reproving the protocol's transaction contract. -/
theorem artifact_initialized_trace (e : DestinationEncoding (m+1)) (n w depth : Nat) (hd : 0 < depth)
    (rtl : Timed.Component (Values (In n m e.width w))
      (Values (Register n m e.width w depth)) (Values (Out n m w)))
    (a : Artifact.Correspondence (circuit e n w depth) rtl)
    (i : Values (In n m e.width w)) (s : Values (Register n m e.width w depth))
    (h : i Physical.reset = 1) (inputs : List (Values (In n m e.width w))) :
    rtl.trace (rtl.step i s) inputs = (Physical.component e depth).trace Switch.initial inputs :=
  a.initialized_trace (implementation e n w depth hd) Physical.reset
    (resetCertificate e n w depth hd) i s h inputs

end Pinwheel.Hardware.Switch.Structural
