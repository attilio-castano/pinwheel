import Pinwheel.Latency
import Pinwheel.SPI.Latency
import Pinwheel.I2C.Latency
import Pinwheel.Compile.I2CProofs
import Pinwheel.Compile.I2CReadProofs

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

/-- Closed loop around any I2C controller. The target may stretch each clock,
pulls SDA low as `targetLow` says for the current pulse count, and changes SDA only
while the true SCL is low. The controller consumes the bus as it was `d` edges
earlier. Returns the final state, the bit seen on each completed clock pulse, and
whether a STOP appeared on the wire. -/
private def closedLoop {σ : Type} (start : σ) (busy : σ → Bool) (pinsOf : σ → I2C.Pins)
    (advance : σ → I2C.Bus → σ) (targetLow : Nat → Bool) (d stretch : Nat) :
    IO (σ × Array Bool × Bool) := do
  let mut state := start
  let mut target : I2C.Pins := {}
  let mut pipe : List I2C.Bus := List.replicate d {}
  let mut previous : I2C.Bus := {}
  let mut previousCommand : I2C.Pins := {}
  let mut stretchLeft := 0
  let mut clocks : Array Bool := #[]
  let mut pending : Option Bool := none
  let mut stopped := false
  for _ in [:60 * 256] do
    if !busy state then break
    let command := pinsOf state
    if previousCommand.scl == .low && command.scl == .release then stretchLeft := stretch
    target := {target with scl := if stretchLeft > 0 then .low else .release}
    let bus := I2C.resolve command target
    -- A clock pulse counts once it falls again; the rise before STOP never does.
    if !previous.scl && bus.scl then pending := some bus.sda
    if previous.scl && !bus.scl then
      if let some bit := pending then clocks := clocks.push bit
      pending := none
    if previous.scl && bus.scl && previous.sda != bus.sda then
      pending := none
      if !previous.sda then stopped := true
    if !bus.scl then
      target := {target with sda := if targetLow clocks.size then .low else .release}
    let observed := I2C.resolve command target
    let queue := pipe ++ [observed]
    state := advance state (queue.headD observed)
    pipe := queue.tail
    previous := observed
    previousCommand := command
    stretchLeft := stretchLeft - 1
  pure (state, clocks, stopped)

private def request : I2C.Request := ⟨0x53, 0xa6⟩

private def writeTarget (reply : I2C.Reply) (pulses : Nat) : Bool :=
  if pulses == 8 then reply.addressAck else if pulses == 17 then reply.dataAck else false

private def wireBitsOk (clocks : Array Bool) : Bool :=
  clocks.size == 18 && (List.range 8).all (fun k => clocks[k]! == (I2C.wireBits request)[k]!) &&
    (List.range 8).all (fun k => clocks[k + 9]! == (I2C.wireBits request)[k + 8]!)

private def enginePins (pins : Engine.Reactive.Pins) : I2C.Pins :=
  ⟨if pins.enabled[0] then .low else .release, if pins.enabled[1] then .low else .release⟩

/-- The write controller: the guarded transition recorded in `I2C.guardedStopFree`,
the revised reference `I2C.step`, and the compiled engine program. -/
private def writeCases : IO Nat := do
  let acks : I2C.Reply := ⟨true, true⟩
  let mut runs := 0
  let reference (cfg : I2C.Config) (guarded : Bool) (d stretch : Nat) (reply : I2C.Reply) :=
    closedLoop (I2C.initial cfg request) I2C.busy I2C.pins
      (fun s bus => if guarded && s.phase == .stopFree then I2C.guardedStopFree s bus else I2C.step cfg s bus)
      (writeTarget reply) d stretch
  let compiled (cfg : I2C.Config) (d stretch : Nat) (reply : I2C.Reply) :=
    let p := Compile.I2C.program cfg request
    closedLoop (Engine.Reactive.start p (Compile.I2C.encodeInputs {})) Engine.Reactive.busy
      (fun s => enginePins s.pins)
      (fun s bus => Engine.Reactive.advance p s (Compile.I2C.encodeInputs bus)) (writeTarget reply) d stretch
  for phase in [2, 3, 5] do
    let cfg : I2C.Config := ⟨Fin.ofNat 256 (phase - 1), 15⟩
    for guarded in [true, false] do
      let (final, clocks, stopped) ← reference cfg guarded 0 0 acks
      ensure (I2C.result final == some .success && wireBitsOk clocks && stopped) "ideal I2C transaction"
      runs := runs + 1
    -- Latency beyond the clock-low time: a stale high starts the high timer early and the
    -- controller's own low phase then reads as a fault, before any clock pulse.
    let (final, clocks, _) ← reference cfg false (phase + 1) 0 acks
    ensure (I2C.result final == some .busFault && clocks.size == 0) s!"premature high at d={phase + 1}"
    runs := runs + 1
    for d in [1, 2, 3].filter (· ≤ phase) do
      -- The guarded transition completes the wire transaction and then faults on its own echo.
      let (final, clocks, stopped) ← reference cfg true d 0 acks
      ensure (I2C.result final == some .busFault) s!"expected the STOP echo fault at d={d}"
      ensure (wireBitsOk clocks && stopped) "the wire transaction itself must still be complete"
      for stretch in [0, 2] do
        for reply in [acks, ⟨false, true⟩, ⟨true, false⟩] do
          let (final, clocks, stopped) ← reference cfg false d stretch reply
          ensure (I2C.result final == some reply.outcome && stopped) s!"revised controller at d={d}, stretch={stretch}"
          ensure (clocks.size == reply.clockCount) "pulse count behind the pipeline"
          if reply == acks then ensure (wireBitsOk clocks) "wire bits behind the pipeline"
          -- The compiled program behaves identically, cycle for cycle on the wire.
          let (engine, engineClocks, engineStopped) ← compiled cfg d stretch reply
          ensure (Compile.I2C.outcome engine == some reply.outcome && engineClocks == clocks &&
            engineStopped == stopped) s!"compiled program at d={d}, stretch={stretch}"
          runs := runs + 2
  -- A wait budget no larger than the latency times out on the controller's own clock echo.
  for d in [1, 2, 3] do
    let (tight, _, _) ← reference ⟨2, Fin.ofNat 256 (d - 1)⟩ false d 0 acks
    ensure (I2C.result tight == some .timeout) s!"wait budget {d} at latency {d} must time out"
    let (enough, _, _) ← reference ⟨2, Fin.ofNat 256 d⟩ false d 0 acks
    ensure (I2C.result enough == some .success) s!"wait budget {d + 1} at latency {d}"
    runs := runs + 2
  pure runs

/-- The register-read controller and its compiled program behind the pipeline. -/
private def readCases : IO Nat := do
  let read : I2C.RegisterRead.Request := ⟨0x53, 0xa6⟩
  let mut runs := 0
  for phase in [3, 5] do
    let cfg : I2C.Config := ⟨Fin.ofNat 256 (phase - 1), 15⟩
    for d in [0, 1, 2, 3].filter (· ≤ phase) do
      for byte in [0x00, 0xff, 0x5a, 0xc3] do
        let byte := BitVec.ofNat 8 byte
        let target (pulses : Nat) : Bool :=
          if pulses == 8 || pulses == 17 || pulses == 26 then true
          else if 27 ≤ pulses && pulses < 35 then !byte.toNat.testBit (34 - pulses) else false
        let (final, clocks, stopped) ← closedLoop (I2C.RegisterRead.initial cfg)
          (fun s => (I2C.RegisterRead.result s).isNone) (fun s => I2C.RegisterRead.pins read s.phase)
          (fun s bus => I2C.RegisterRead.step cfg s bus) target d (if d == 2 then 1 else 0)
        ensure (I2C.RegisterRead.result final == some (.success byte) && clocks.size == 36 && stopped)
          s!"register read at d={d}: {repr (I2C.RegisterRead.result final)}"
        let p := Compile.I2CRead.program cfg read
        let (engine, engineClocks, _) ← closedLoop (Engine.Reactive.start p (Compile.I2C.encodeInputs {}))
          Engine.Reactive.busy (fun s => enginePins s.pins)
          (fun s bus => Engine.Reactive.advance p s (Compile.I2C.encodeInputs bus)) target d
          (if d == 2 then 1 else 0)
        ensure (Compile.I2CRead.result engine == some (.success byte) && engineClocks == clocks)
          s!"compiled register read at d={d}"
        runs := runs + 2
  pure runs

def main : IO Unit := do
  ensure ((List.range 6).map (Latency.delayed 2 9 (fun n => n + 10)) == [9, 9, 10, 11, 12, 13])
    "two-stage delay with idle contents"
  ensure ((List.range 8).all fun n =>
    Latency.delayed 1 0 (Latency.delayed 2 0 (· + 1)) n == Latency.delayed 3 0 (· + 1) n) "pipelines compose"
  let transfers ← spi
  let writes ← writeCases
  let reads ← readCases
  IO.println s!"Latency: {transfers} SPI transfers inside and at the edge of d + tco ≤ half; {writes} closed-loop I2C write runs and {reads} register-read runs, reference and compiled."
