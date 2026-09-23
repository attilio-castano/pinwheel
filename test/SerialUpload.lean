import Pinwheel.Hardware.Storage.ChipUpload
import Pinwheel.Compile.I2C
import Pinwheel.Compile.UARTRx

/-! An executable host: serialize a program's upload into pin samples, run them
through the chip's samplers and serial receiver (their functional models), and
check that the core consumes exactly the intended commands. The theorems
(`Serial.session_delivers`, `Chip.session_delivers`) cover every session; this
suite pins the frame format a host driver has to follow, shows the hypotheses of
`chip_runs_upload` hold for real programs, and rejects the usual mistakes. -/

open Pinwheel Pinwheel.Hardware Pinwheel.Hardware.Loader

private def ensure (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw (IO.userError message)

/-- Tiny Tapeout pins for one sample: `ui_in[0]` clock, `[1]` data, `[2]` select. -/
private def pin (sck mosi csn : Bool) (noise : Nat) : Chip.Pins :=
  { uiIn := BitVec.ofNat 8 ((if sck then 1 else 0) + (if mosi then 2 else 0) + (if csn then 4 else 0))
    uioIn := BitVec.ofNat 8 noise }

/-- One frame, most significant bit first: `low` samples with the clock low, then
`high` with it high. `spoil` puts garbage on the data pin everywhere except at
the first high sample of each bit. -/
private def frame (first : Bool → Bool) (command : BitVec 8) (word : BitVec 64) (low high : Nat)
    (spoil : Bool) : List Chip.Pins := Id.run do
  let bits : BitVec 72 := command ++ word
  let mut samples := #[]
  for k in [0:72] do
    let b := first (bits.getLsbD (71 - k))
    for j in [0:low] do samples := samples.push (pin false (if spoil then j % 2 == 0 else b) false (k + j))
    for j in [0:high] do samples := samples.push (pin true (if spoil && j > 0 then !b else b) false (k + 2 * j))
  return samples.toList

private def idle (n : Nat) : List Chip.Pins := List.replicate n (pin false false true 3)

private def session (commands : List (BitVec 8 × BitVec 64)) (low high : Nat) (spoil : Bool := false)
    (first : Bool → Bool := id) : List Chip.Pins :=
  idle 3 ++ (commands.flatMap fun (c, w) => frame first c w low high spoil ++ idle 2) ++ idle 2

/-- The commands the core consumed: every edge that is not quiet. -/
private def delivered (pins : List Chip.Pins) : List (BitVec 3 × BitVec 64 × Bool) :=
  (Chip.consumed {} pins).filterMap fun m =>
    if m.command == 0 && !m.reset && !m.init then none else some (m.command, m.data, m.reset)

private def uploadBytes (ws : List (BitVec 64)) : List (BitVec 8 × BitVec 64) :=
  (1, 0) :: (ws.map fun w => ((2 : BitVec 8), w)) ++ [(3, 0)]

def main : IO Unit := do
  let write := Execution.widenProgram (Compile.I2C.program ⟨3, 7⟩ ⟨0x53, 0xa6⟩)
  let some ws := Loader.ProgramImage.upload write | throw (IO.userError "I2C write has no indexed image")
  -- The hypotheses of `chip_runs_upload` for a real program.
  ensure (ws.length == 322) "upload length"
  ensure (((Execution.imageWords write).toList.eraseDups).length ≤ 32) "I2C write must fit the small store"
  ensure (ws.all Storage.SinglePort.Ready) "I2C write must be ready for one port"
  ensure ((List.range 322).all fun k => Storage.Small.capacity (BitVec.ofNat 9 k) (ws.getD k 0))
    "every word must pass the capacity check at its position"
  let receiver := Compile.UARTRx.program ⟨16, by decide, by decide, 0⟩
  let some rx := Loader.ProgramImage.upload receiver | throw (IO.userError "UART RX has no indexed image")
  ensure (!rx.all Storage.SinglePort.Ready) "the UART receiver is outside the one-port rule"
  -- A whole upload, then start, at the slowest legal phase lengths.
  let commands := uploadBytes ws ++ [(5, 0)]
  let expected := commands.map fun (c, w) => (c.extractLsb' 0 3, w, false)
  let pins := session commands 1 2
  ensure (delivered pins == expected) "upload session must deliver exactly its commands"
  IO.println s!"Serial upload: {commands.length} frames, {pins.length} samples, delivered in order."
  -- Uneven phases, and garbage on the data pin except where the theorem asks for the bit.
  ensure (delivered (session (commands.take 40) 3 5) == expected.take 40) "longer phases"
  ensure (delivered (session (commands.take 40) 2 3 (spoil := true)) == expected.take 40)
    "only the first high sample of a bit may matter"
  -- Command 7 is the core's reset input, not a loader command.
  ensure (delivered (session [(7, 0xabc)] 1 2) == [(0, 0xabc, true)]) "command 7 is reset"
  -- The upper five bits of the command byte are ignored.
  ensure (delivered (session [(0xfa, 5)] 1 2) == [(2, 5, false)]) "command byte low bits"
  -- Mistakes a driver can make.
  ensure (delivered (session (commands.take 5) 1 2 (first := not)) != expected.take 5) "inverted data escaped"
  let reversed := (commands.take 5).map fun (c, w) => (c.reverse, w.reverse)
  ensure (delivered (session reversed 1 2) != expected.take 5) "least-significant-bit-first escaped"
  -- A frame cut short by the select line delivers nothing; the next frame is intact.
  let cut := idle 3 ++ (frame id 2 77 1 2 false).take 200 ++ idle 2 ++ frame id 2 99 1 2 false ++ idle 4
  ensure (delivered cut == [(2, 99, false)]) "abandoned frame"
  -- Without the two trailing samples the last command is still inside the samplers.
  let tight := idle 3 ++ frame id 5 0 1 2 false
  ensure (delivered tight == []) "two samples of latency"
  ensure (delivered (tight ++ idle 3) == [(5, 0, false)]) "delivered after the samplers"
  IO.println "Serial upload: phases, spoiled data pin, reset command, driver mistakes and abandoned frames passed."
