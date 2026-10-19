import Pinwheel.Hardware.Buffered.SerialSourceSession

/-! Every partial sampled request/read frame supplies quiet actual controller
inputs. This derives the abort-prefix admission from physical wire witnesses,
including a cut between low/high samples, rather than assuming a decoded trace. -/
namespace Pinwheel.Hardware.Buffered.SerialPackage
open Pinwheel.Hardware

theorem State.commands_take (before : State) (pins : List Pins) (count : Nat) :
    before.commands (pins.take count) = (before.commands pins).take count := by
  induction pins generalizing before count with
  | nil => simp [State.commands]
  | cons pin rest ih =>
    cases count with
    | zero => rfl
    | succ count =>
      change _ :: (before.step pin).commands (rest.take count) =
        _ :: ((before.step pin).commands rest).take count
      rw [ih]

theorem State.quiet_take (before : State) (pins : List Pins) (count : Nat)
    (quiet : ∀ input ∈ before.commands pins, SpiCircuit.Quiet input) :
    ∀ input ∈ before.commands (pins.take count), SpiCircuit.Quiet input := by
  rw [before.commands_take]
  intro input member
  exact quiet input (List.mem_of_mem_take member)

end Pinwheel.Hardware.Buffered.SerialPackage

namespace Pinwheel.Hardware.Buffered.SerialWire
open Pinwheel.Hardware Serial.Frames

theorem Request.quiet_prefix (request : Request before) (count : Nat) :
    ∀ input ∈ before.commands (request.pins.take count), SpiCircuit.Quiet input :=
  before.quiet_take request.pins count request.quiet

theorem Read.quiet_prefix (read : Read before) (ready : ReceiptReady before.record) (count : Nat) :
    ∀ input ∈ before.commands (read.pins.take count), SpiCircuit.Quiet input :=
  before.quiet_take read.pins count (read.quiet ready)

end Pinwheel.Hardware.Buffered.SerialWire

namespace Pinwheel.Hardware.Buffered.SerialSourceSession

theorem Attempt.quiet_prefix (attempt : Attempt before) (count : Nat) :
    ∀ input ∈ before.commands (attempt.pins.take count), SpiCircuit.Quiet input :=
  before.quiet_take attempt.pins count attempt.quiet

end Pinwheel.Hardware.Buffered.SerialSourceSession
