import Pinwheel.I2C.Bus

/-! Digital contracts for a proposed external interface. These models are not
inserted into the core and make no metastability or electrical timing claim. -/
namespace Pinwheel.Hardware.PinBoundary

structure Samples (width : Nat) where
  first : BitVec width
  second : BitVec width
  deriving DecidableEq, Repr

/-- Both registers update from the old state. The engine consumes `second`
before this update on the same clock edge. Reset samples are an explicit profile. -/
def sampleStep (resetValue : BitVec w) (reset : Bool) (pins : BitVec w) (s : Samples w) : Samples w :=
  if reset then ⟨resetValue, resetValue⟩ else ⟨pins, s.first⟩

def engineInput (s : Samples w) : BitVec w := s.second

theorem reset_priority (resetValue pins : BitVec w) (s : Samples w) :
    sampleStep resetValue true pins s = ⟨resetValue, resetValue⟩ := rfl

/-- A pin sampled on edge n is consumed by the engine on edge n+2, provided
neither intervening pipeline update resets. This is a two-edge digital delay,
not a bound on the analog resolution of an asynchronous transition. -/
theorem two_edge_latency (resetValue first second : BitVec w) (s : Samples w) :
    engineInput (sampleStep resetValue false second (sampleStep resetValue false first s)) = first := rfl

theorem first_edge_retains_old_sample (resetValue pins : BitVec w) (s : Samples w) :
    engineInput (sampleStep resetValue false pins s) = s.first := rfl

structure PadOutput where
  data : Bool
  enabled : Bool
  deriving DecidableEq, Repr

/-- A physical open-drain pad drives zero or disables its output driver. -/
def openDrain (command : I2C.Drive) : PadOutput :=
  ⟨false, command == .low⟩

theorem openDrain_never_high (command : I2C.Drive) : (openDrain command).data = false := rfl

theorem release_disables : (openDrain .release).enabled = false := rfl

/-- Ideal pull-up interpretation connects the pad command to the existing bus
model. Rise time, input thresholds, pull-up sizing, and pads remain external. -/
def resolved (pad : PadOutput) (peer : I2C.Drive) : Bool :=
  if pad.enabled then pad.data else peer == .release

theorem openDrain_resolves (command peer : I2C.Drive) :
    resolved (openDrain command) peer = I2C.resolveLine command peer := by
  cases command <;> cases peer <;> rfl
  done

end Pinwheel.Hardware.PinBoundary
