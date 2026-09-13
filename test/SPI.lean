import Pinwheel

/-! Executable digital-model checks. No RTL or physical peripheral is involved. -/

open Pinwheel.SPI

/-- A response defined by absolute edge times, with optional noise elsewhere. -/
private def incoming (cfg : Config) (reply : BitVec 8) (noisy : Bool) (cycle : Nat) : Bool := Id.run do
  for bit in [:8] do
    if cycle == (2 * bit + 1) * cfg.halfCycles then
      return reply.getLsbD (7 - bit)
  return noisy && cycle % 2 == 0

private def isSample (cfg : Config) (cycle : Nat) : Bool :=
  (List.range 8).any fun bit => cycle == (2 * bit + 1) * cfg.halfCycles

private def checkFrame (cfg : Config) (byte reply : BitVec 8) (noisy : Bool) : IO Unit := do
  let mut state := step (resetState cfg) ⟨false, some byte, true⟩
  let mut rising := 0
  let mut falling := 0
  let mut captures := 0
  for cycle in [:cfg.transferCycles + 3] do
    let fail := fun detail => IO.userError
      s!"{detail}: tx={byte}, rx={reply}, H={cfg.halfCycles}, cycle={cycle}, noisy={noisy}"
    if pins state != expectedPins cfg byte cycle then
      throw <| fail "waveform mismatch"
    if controlBusy state.control != decide (cycle < cfg.transferCycles) then
      throw <| fail "busy duration mismatch"
    let expectedResult := if cycle < cfg.transferCycles then none else some reply
    if result state != expectedResult then
      throw <| fail "received result or valid timing mismatch"
    for bit in [:8] do
      let expectedBit := cycle >= (2 * bit + 1) * cfg.halfCycles && reply.getLsbD (7 - bit)
      if state.samples.toArray[bit]! != expectedBit then
        throw <| fail "receive slot changed outside its sampling edge"
    let aborted := step state ⟨true, some (~~~byte), true⟩
    if aborted != resetState cfg || result aborted != none || pins aborted != ⟨true, false, false⟩ then
      throw <| fail "reset priority or idle outputs mismatch"
    if step aborted ⟨false, some (~~~byte), true⟩ != initial cfg (~~~byte) then
      throw <| fail "restart after abort failed"
    let miso := incoming cfg reply noisy (cycle + 1)
    let next := step state ⟨false, none, miso⟩
    if controlBusy state.control && step state ⟨false, some (~~~byte), miso⟩ != next then
      throw <| fail "busy request changed execution"
    for bit in List.finRange 8 do
      if captureAt state.control bit then
        captures := captures + 1
        if cycle + 1 != (2 * bit.val + 1) * cfg.halfCycles then
          throw <| fail "unexpected capture event"
    if !(pins state).sclk && (pins next).sclk then
      rising := rising + 1
      if !isSample cfg (cycle + 1) || (pins state).mosi != (pins next).mosi then
        throw <| fail "rising edge or MOSI stability mismatch"
    if (pins state).sclk && !(pins next).sclk then
      falling := falling + 1
    if cycle >= cfg.transferCycles && next != state then
      throw <| fail "idle did not retain the completed result"
    if cycle == cfg.transferCycles then
      let restarted := step state ⟨false, some (~~~byte), true⟩
      if restarted != initial cfg (~~~byte) || result restarted != none then
        throw <| fail "earliest restart did not capture data and clear valid"
    state := next
  if rising != 8 || falling != 8 || captures != 8 then
    throw <| IO.userError s!"expected eight rising, falling, and capture events; got {rising}/{falling}/{captures}"

private def writeTrace : IO Unit := do
  let cfg : Config := ⟨3⟩
  let byte : BitVec 8 := 0x53
  let reply : BitVec 8 := 0xa6
  let mut state := step (resetState cfg) ⟨false, some byte, false⟩
  let mut csv := "cycle,cs_n,sclk,mosi,miso,sample,busy,valid,rx\n"
  let bit := fun value => if value then 1 else 0
  for cycle in [:cfg.transferCycles + 2] do
    let p := pins state
    csv := csv ++ s!"{cycle},{bit p.csN},{bit p.sclk},{bit p.mosi},{bit (incoming cfg reply true cycle)},{bit (isSample cfg cycle)},{bit (controlBusy state.control)},{bit state.valid},{(received state).toNat}\n"
    state := step state ⟨false, none, incoming cfg reply true (cycle + 1)⟩
  IO.FS.createDirAll "build/spi"
  IO.FS.writeFile "build/spi/0x53-rx0xa6-4cycles.csv" csv

def main : IO Unit := do
  let configs : List Config := [⟨0⟩, ⟨3⟩, ⟨255⟩]
  for cfg in configs do
    for value in [:256] do
      let byte := BitVec.ofNat 8 value
      for noisy in [false, true] do
        checkFrame cfg byte (~~~byte) noisy
    IO.println s!"Passed all 256 TX and RX values at H={cfg.halfCycles}, with quiet and noisy off-edge inputs."
  for reply in [:256] do
    checkFrame ⟨0⟩ 0x53 (BitVec.ofNat 8 reply) true
  writeTrace
  IO.println "Passed waveform, eight clock/sample events, receive storage, reset at every phase, busy requests, result retention, and earliest restart checks."
  IO.println "Wrote build/spi/0x53-rx0xa6-4cycles.csv (68 transfer cycles plus 2 idle cycles)."
