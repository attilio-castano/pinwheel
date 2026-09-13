import Pinwheel

/-! Runnable model checks and a CSV trace; these exercise Lean, not RTL. -/

open Pinwheel.UART

private def checkFrame (cfg : Config) (byte : BitVec 8) : IO Unit := do
  let mut state : State cfg := step .idle ⟨false, some byte⟩
  for cycle in [:cfg.frameCycles + 2] do
    if pin state != expected cfg byte cycle then
      throw <| IO.userError s!"waveform mismatch: byte={byte}, duration={cfg.cycles}, cycle={cycle}"
    if busy state != decide (cycle < cfg.frameCycles) then
      throw <| IO.userError s!"busy timing mismatch at cycle {cycle}"
    if step state ⟨true, some byte⟩ != .idle then
      throw <| IO.userError s!"reset priority mismatch at cycle {cycle}"
    if busy state && step state ⟨false, some (~~~byte)⟩ != advance state then
      throw <| IO.userError s!"busy request changed execution at cycle {cycle}"
    state := step state ⟨false, none⟩
  let next := ~~~byte
  if step state ⟨false, some next⟩ != initial cfg next then
    throw <| IO.userError "restart did not capture the next byte"

private def writeTrace : IO Unit := do
  let cfg : Config := ⟨3⟩
  let byte : BitVec 8 := 0x53
  let mut state : State cfg := step .idle ⟨false, some byte⟩
  let mut csv := "cycle,tx,busy\n"
  for cycle in [:cfg.frameCycles + 2] do
    csv := csv ++ s!"{cycle},{if pin state then 1 else 0},{if busy state then 1 else 0}\n"
    state := step state ⟨false, none⟩
  IO.FS.createDirAll "build/uart"
  IO.FS.writeFile "build/uart/0x53-4cycles.csv" csv

def main : IO Unit := do
  let configs : List Config := [⟨0⟩, ⟨3⟩, ⟨255⟩]
  for cfg in configs do
    for value in [:256] do
      checkFrame cfg (BitVec.ofNat 8 value)
    IO.println s!"Passed all 256 bytes at {cfg.cycles} cycles/bit."
  writeTrace
  IO.println "Passed waveform, busy, reset priority, ignored requests, and restart checks."
  IO.println "Wrote build/uart/0x53-4cycles.csv (40 frame cycles plus 2 idle cycles)."
