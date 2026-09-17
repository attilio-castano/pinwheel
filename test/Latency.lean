import Pinwheel.Latency
import Pinwheel.SPI.Latency
import Pinwheel.I2C.Latency

open Pinwheel

private def ensure (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw (IO.userError message)

/-- A mode-0 peripheral at the pins: bit `k` from `tco` cycles after its falling
edge until `tco` after the next one. Outside every window it shows the opposite of
the first bit, the least helpful value. -/
private def misoPins (cfg : SPI.Config) (reply : BitVec 8) (tco : Nat) (t : Nat) : Bool :=
  let h := cfg.halfCycles
  if t < tco then !SPI.replyBit reply 0
  else
    let k := (t - tco) / (2 * h)
    if k < 8 then SPI.replyBit reply k else SPI.replyBit reply 7

private def spi : IO Nat := do
  let mut transfers := 0
  for half in [1, 2, 3, 4, 6] do
    let cfg : SPI.Config := ⟨Fin.ofNat 256 (half - 1)⟩
    for tco in [0, 1, 2, 3] do
      for d in [0, 1, 2, 3, 4] do
        for reply in [0x00, 0xff, 0xaa, 0x55, 0xa6, 0x53] do
          let reply := BitVec.ofNat 8 reply
          let seen := Latency.delayed d true (misoPins cfg reply tco)
          let result := SPI.result (SPI.run cfg 0x3c seen cfg.transferCycles)
          if d + tco ≤ half then
            ensure (result == some reply) s!"SPI half={half} tco={tco} d={d}: reply lost inside the proved bound"
          transfers := transfers + 1
        -- One cycle beyond the bound every slot reads its predecessor's bit.
        if d + tco == half + 1 then
          let reply : BitVec 8 := 0xaa
          let seen := Latency.delayed d true (misoPins cfg reply tco)
          ensure (SPI.result (SPI.run cfg 0x3c seen cfg.transferCycles) != some reply)
            s!"SPI half={half} tco={tco} d={d}: bound is not tight"
  pure transfers

/-- Closed loop around the I2C write controller. The target acknowledges as told,
may stretch each clock, and changes SDA only while the true SCL is low. The
controller consumes the bus as it was `d` edges earlier. -/
private def i2c (cfg : I2C.Config) (d stretch : Nat) (reply : I2C.Reply)
    (transition : I2C.Config → I2C.State → I2C.Bus → I2C.State) :
    IO (Option I2C.Outcome × Array Bool × Bool) := do
  let request : I2C.Request := ⟨0x53, 0xa6⟩
  let mut state := I2C.initial cfg request
  let mut target : I2C.Pins := {}
  let mut pipe : List I2C.Bus := List.replicate d {}
  let mut previous : I2C.Bus := {}
  let mut previousCommand : I2C.Pins := {}
  let mut stretchLeft := 0
  let mut clocks : Array Bool := #[]
  let mut pending : Option Bool := none
  let mut stopped := false
  for _ in [:40 * 256] do
    if !I2C.busy state then break
    let command := I2C.pins state
    if previousCommand.scl == .low && command.scl == .release then stretchLeft := stretch
    target := {target with scl := if stretchLeft > 0 then .low else .release}
    let bus := I2C.resolve command target
    -- A clock pulse counts once it falls again; the rise before STOP never does.
    if !previous.scl && bus.scl then pending := some bus.sda
    if previous.scl && !bus.scl then
      if let some bit := pending then clocks := clocks.push bit
      pending := none
    if previous.scl && bus.scl && !previous.sda && bus.sda then stopped := true
    if !bus.scl then
      let ack := if clocks.size == 8 then reply.addressAck
        else if clocks.size == 17 then reply.dataAck else false
      target := {target with sda := if ack then .low else .release}
    let observed := I2C.resolve command target
    let queue := pipe ++ [observed]
    state := transition cfg state (queue.headD observed)
    pipe := queue.tail
    previous := observed
    previousCommand := command
    stretchLeft := stretchLeft - 1
  pure (I2C.result state, clocks, stopped)

private def wireBitsOk (clocks : Array Bool) : Bool :=
  let request : I2C.Request := ⟨0x53, 0xa6⟩
  clocks.size == 18 && (List.range 8).all (fun k => clocks[k]! == (I2C.wireBits request)[k]!) &&
    (List.range 8).all (fun k => clocks[k + 9]! == (I2C.wireBits request)[k + 8]!)

private def i2cCases : IO Nat := do
  let original := fun cfg s bus => I2C.step cfg s bus
  let tolerant := fun cfg s bus => I2C.tolerantStep cfg s bus
  let acks : I2C.Reply := ⟨true, true⟩
  let mut runs := 0
  for phase in [2, 3, 5] do
    let cfg : I2C.Config := ⟨Fin.ofNat 256 (phase - 1), 15⟩
    -- Without latency both controllers succeed.
    for transition in [original, tolerant] do
      let (outcome, clocks, stopped) ← i2c cfg 0 0 acks transition
      ensure (outcome == some .success && wireBitsOk clocks && stopped) "ideal I2C transaction"
      runs := runs + 1
    -- Latency beyond the clock-low time: a stale high starts the high timer early and
    -- the controller's own low phase then reads as a fault, before any clock pulse.
    for transition in [original, tolerant] do
      let (outcome, clocks, _) ← i2c cfg (phase + 1) 0 acks transition
      ensure (outcome == some .busFault && clocks.size == 0) s!"premature high at d={phase + 1}: {repr outcome}"
      runs := runs + 1
    for d in [1, 2, 3].filter (· ≤ phase) do
      -- The specified controller completes the wire transaction and then faults on its own echo.
      let (outcome, clocks, stopped) ← i2c cfg d 0 acks original
      ensure (outcome == some .busFault) s!"expected the STOP echo fault at d={d}, got {repr outcome}"
      ensure (wireBitsOk clocks && stopped) "the wire transaction itself must still be complete"
      -- The revised controller succeeds, also with a stretching target.
      for stretch in [0, 2] do
        let (outcome, clocks, stopped) ← i2c cfg d stretch acks tolerant
        ensure (outcome == some .success && wireBitsOk clocks && stopped)
          s!"tolerant controller at d={d}, stretch={stretch}: {repr outcome}"
        runs := runs + 1
      let (nack, _, _) ← i2c cfg d 0 ⟨false, true⟩ tolerant
      ensure (nack == some .addressNack) "address NACK behind the pipeline"
      let (dataNack, _, _) ← i2c cfg d 0 ⟨true, false⟩ tolerant
      ensure (dataNack == some .dataNack) "data NACK behind the pipeline"
      runs := runs + 3
  -- A wait budget no larger than the latency times out on the controller's own clock echo.
  for d in [1, 2, 3] do
    let tight : I2C.Config := ⟨2, Fin.ofNat 256 (d - 1)⟩
    let (outcome, _, _) ← i2c tight d 0 acks tolerant
    ensure (outcome == some .timeout) s!"wait budget {d} at latency {d} must time out, got {repr outcome}"
    let enough : I2C.Config := ⟨2, Fin.ofNat 256 d⟩
    let (outcome, _, _) ← i2c enough d 0 acks tolerant
    ensure (outcome == some .success) s!"wait budget {d + 1} at latency {d}: {repr outcome}"
    runs := runs + 2
  pure runs

def main : IO Unit := do
  ensure ((List.range 6).map (Latency.delayed 2 9 (fun n => n + 10)) == [9, 9, 10, 11, 12, 13])
    "two-stage delay with idle contents"
  ensure ((List.range 8).all fun n =>
    Latency.delayed 1 0 (Latency.delayed 2 0 (· + 1)) n == Latency.delayed 3 0 (· + 1) n) "pipelines compose"
  let transfers ← spi
  let runs ← i2cCases
  IO.println s!"Latency: {transfers} SPI transfers inside and at the edge of d + tco ≤ half; {runs} closed-loop I2C runs (echo fault, revised controller, wait budget)."
