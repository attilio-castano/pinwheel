import Pinwheel.Hardware.Storage.PairedResidentEffects

open Pinwheel.Hardware Pinwheel.Hardware.Storage PairedController

private def ensure (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw (IO.userError message)

private def token (kind levels duration : Nat) : BitVec 32 :=
  BitVec.ofNat 32 (kind + levels * 8 + 7 * 64 + (duration - 1) * 512)

private def snapshot (word : BitVec 32) (parameter : BitVec 20)
    (payload : BitVec 8) (levels : BitVec 3) (mode : BitVec 3 := 0)
    (remaining : BitVec 8 := 0) : Values Register
  | _, .parameter _ _ => parameter
  | _, .boot _ => word
  | _, .idle _ => 0x3f
  | _, .valid => 1
  | _, .current => word
  | _, .cached => parameter
  | _, .mode => mode
  | _, .remaining => remaining
  | _, .payload => payload
  | _, .levels => levels
  | _, .samples => 0x5a5a
  | _, _ => 0

private def inputs (i : Loader.Machine.Inputs) (word : BitVec 32) : Values Input
  | _, .base p => i.values p
  | _, .q _ => word ++ word

-- These expectations use arithmetic bit positions and the protocol operand,
-- never graph wires or the proof's shiftOperand/outputBit definitions.
private def shiftValue (value : Nat) (msb : Bool) : BitVec 8 :=
  BitVec.ofNat 8 (if msb then value * 2 else value / 2)

private def shiftedLevels (literal pin value : Nat) (msb : Bool) : BitVec 3 :=
  let bit := if msb then value / 128 else value % 2
  BitVec.ofNat 3 ((literal &&& (7 - 2 ^ pin)) ||| (bit * 2 ^ pin))

private def shiftCases (n : Netlist Register (SramController.Out Loader.Machine.Output) Input) : IO Nat := do
  let mut cases := 0
  for duration in [1, 4, 256] do
    for pin in [:3] do
      for msb in [false, true] do
        for value in [:256] do
          let literal := value % 8
          let word := token 5 literal duration
          let parameter := BitVec.ofNat 20 (pin + if msb then 4 else 0)
          let s : Values Register := snapshot word parameter 0xa6 5
          let i : Loader.Machine.Inputs := {command := 5, data := BitVec.ofNat 64 (0x1234567800 + value)}
          let after : Values Register := n.step (inputs i word) s
          ensure (after .payload == shiftValue value msb) "SHIFT did not snapshot low START byte and shift once"
          ensure (after .levels == shiftedLevels literal pin value msb) "SHIFT drove wrong pre-shift bit or changed another pin"
          ensure (after .remaining == BitVec.ofNat 8 (duration - 1)) "SHIFT duration did not enter at full count"
          ensure (after .mode == 1) "SHIFT did not enter timed mode"
          -- Use a concrete independently expected snapshot for the next local
          -- edge. Chaining lazy register closures repeatedly evaluates the
          -- entire preceding graph for every parameter and control read.
          let enteredState : Values Register := snapshot word parameter (shiftValue value msb)
            (shiftedLevels literal pin value msb) 1 (BitVec.ofNat 8 (duration - 1))
          if duration > 1 then
            let busy : Loader.Machine.Inputs := {command := 5, data := BitVec.ofNat 64 (value ^^^ 255)}
            let held : Values Register := n.step (inputs busy word) enteredState
            ensure (held .payload == shiftValue value msb && held .levels == shiftedLevels literal pin value msb)
              "Held edge shifted again or accepted a busy payload"
          else
            let next : Values Register := n.step (inputs {command := 5, data := 0xffffffffffffffff} word) enteredState
            ensure (next .payload == shiftValue (shiftValue value msb).toNat msb)
              "Second instruction entry did not shift the existing owned payload exactly once"
          let reset : Values Register := n.step (inputs {init := true, command := 5, data := 255} word) enteredState
          ensure (reset .payload == 0) "Reset lost priority over SHIFT or START"
          cases := cases + 1
  return cases

private def keepCases (n : Netlist Register (SramController.Out Loader.Machine.Output) Input) : IO Nat := do
  let mut cases := 0
  for mask in [:8] do
    for old in [:8] do
      for literal in [:8] do
        let word := token 6 literal 4
        let parameter := BitVec.ofNat 20 (mask * 64)
        let s : Values Register := snapshot word parameter 0xa6 (BitVec.ofNat 3 old)
        let after : Values Register := n.step (inputs {command := 5, data := 0x1234567853} word) s
        let expected := BitVec.ofNat 3 ((old &&& mask) ||| (literal &&& (7 - mask)))
        ensure (after .levels == expected) "KEEP did not preserve exactly its selected old output bits"
        ensure (after .payload == 0x53) "KEEP shifted or failed to snapshot an accepted START payload"
        cases := cases + 1
  for pin in [:2] do
    for slot in [:16] do
      for incoming in [:4] do
        let word := token 6 2 4
        let descriptor := 1 + pin * 2 + slot * 4
        let parameter := BitVec.ofNat 20 (descriptor + 64)
        -- A real running dispatch enters KEEP from Q and retains all old samples
        -- except the designated ordinary capture. It is not an accepted START.
        let s : Values Register := snapshot (token 5 1 4) parameter 0xa6 1 1 0
        let after : Values Register := n.step (inputs {incoming := BitVec.ofNat 2 incoming} word) s
        let sample := (incoming / 2 ^ pin) % 2
        let expected := BitVec.ofNat 16 ((0x5a5a &&& (65535 - 2 ^ slot)) ||| (sample * 2 ^ slot))
        ensure (after .samples == expected) "KEEP lost an old sample or captured the wrong input/destination"
        ensure (after .payload == 0xa6 && after .levels == 3) "KEEP changed resident data or preserved MOSI incorrectly"
        cases := cases + 1
  return cases

def main : IO Unit := do
  let .ok n := PairedController.core | throw (IO.userError "Retained resident core construction failed")
  let shifts ← shiftCases n
  let keeps ← keepCases n
  IO.println s!"Resident effects: {shifts} SHIFT cases; periods 1/4/256, both bit orders, three outputs, all 256 operands; accepted snapshot, busy holds, one shift per entry and reset; {keeps} KEEP mask/capture cases passed on the actual typed core."

#print axioms PairedResidentEffects.accepted_start_snapshot
#print axioms PairedResidentEffects.payload_enter_shift
#print axioms PairedResidentEffects.payload_held
#print axioms PairedResidentEffects.payload_busy_hold
#print axioms PairedResidentEffects.payload_reset
#print axioms PairedResidentEffects.payload_accepted_start_not_shift
#print axioms PairedResidentEffects.shift_pin_after_edge
#print axioms PairedResidentEffects.keep_pin_after_edge
#print axioms PairedResidentEffects.keep_capture_after_edge
#print axioms PairedResidentEffects.retained_shift_payload
