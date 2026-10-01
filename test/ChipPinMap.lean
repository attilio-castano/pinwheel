import Pinwheel.Hardware.HostResult
import Pinwheel.Hardware.Storage.ChipBackend
import Pinwheel.Hardware.Storage.PairedHost

/-! Kernel-checked boundary controls for the static five-pad digital candidate.
The arithmetic oracle is independent of `packProtocolOutput`: each logical
three-bit value must occupy physical pads 2–4, with no other physical bit set. -/
open Pinwheel.Hardware

private def coreOutputs (levels enabled : BitVec 3) : Values Loader.Machine.Output
  | _, .core (.state .levels) => levels
  | _, .core (.state .enabled) => enabled
  | _, _ => 0

theorem all_level_enable_assignments : ∀ levels enabled : BitVec 3,
    (Chip.shown (coreOutputs levels enabled) .uioOut).toNat = levels.toNat * 4 ∧
    (Chip.shown (coreOutputs levels enabled) .uioOe).toNat = enabled.toNat * 4 := by
  decide +kernel

example : (Chip.packProtocolOutput 1, Chip.packProtocolOutput 2, Chip.packProtocolOutput 4) =
    (4#8, 8#8, 16#8) := by
  decide +kernel

-- Any combination on pads 2–7 leaves the two engine input lanes unchanged.
example : ∀ incoming : BitVec 2, ∀ upper : BitVec 6,
    (Chip.wired {uioIn := upper ++ incoming}).incoming = incoming := by
  decide +kernel

-- Serial transport, reset and host-result controls retain their original inputs.
example (p : Chip.Pins) :
    (Chip.wired p).sck = p.uiIn.getLsbD 0 ∧
    (Chip.wired p).mosi = p.uiIn.getLsbD 1 ∧
    (Chip.wired p).csn = p.uiIn.getLsbD 2 ∧
    (Chip.wired p).init = !p.rstN := ⟨rfl, rfl, rfl, rfl⟩

example (p : Chip.Pins) (o : Values Loader.Machine.Output) (s : HostResult.State) :
    (HostResult.next p o s).pageFirst = p.uiIn.extractLsb' 3 2 ∧
    (HostResult.next p o s).controlFirst = p.uiIn.extractLsb' 5 2 := ⟨rfl, rfl⟩

-- The result observer preserves both physical pad buses for every mailbox state,
-- even while uo_out displays result pages instead of live status.
example (o : Values Loader.Machine.Output) (s : HostResult.State) :
    Chip.unpackProtocolOutput (HostResult.shown o s .uioOut) = o (.core (.state .levels)) ∧
    Chip.unpackProtocolOutput (HostResult.shown o s .uioOe) = o (.core (.state .enabled)) :=
  Chip.shown_protocol_outputs o

example (o : Values Loader.Machine.Output) (s : HostResult.State) :
    HostResult.shown o s .uioOe &&& ~~~Chip.protocolOutputMask = 0 :=
  (Chip.shown_protocol_mask o).2.2

example (o : Values Loader.Machine.Output) (s : HostResult.State) (k : Nat)
    (h : k < 2 ∨ 5 ≤ k) :
    (HostResult.shown o s .uioOe).getLsbD k = false :=
  Chip.shown_released o k h
