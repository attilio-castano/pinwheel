import Pinwheel.Compile.I2CRecoveryProofs
import Pinwheel.Hardware.Storage.PairedImage
import Lean

open Pinwheel Pinwheel.Hardware
open Lean (toJson)
open Pinwheel.Compile.I2CRecovery

private def ensure (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw (IO.userError message)

private structure Fixture where
  name : String
  phase : Nat := 4
  timeout : Nat := 32
  releaseAfter : Option Nat := some 9
  stretch : Nat := 0
  sclStuck : Bool := false
  deriving Repr

private def cfg (f : Fixture) : Config :=
  ⟨⟨min (f.phase - 1) 255, Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩,
    ⟨min (f.timeout - 1) 255, Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩⟩

private def expected (f : Fixture) : I2C.Recovery.Outcome :=
  if f.sclStuck then .timeout
  else if f.releaseAfter.isSome then .recovered else .stillStuck

private def metadata (f : Fixture) : Lean.Json := Lean.Json.mkObj [
  ("name", toJson f.name), ("phase_cycles", toJson f.phase),
  ("timeout_cycles", toJson f.timeout), ("recovery_policy", toJson "nine_rises_release_only"),
  ("capture_slot", toJson (0 : Nat)), ("release_after_pulses", toJson f.releaseAfter),
  ("stretch_cycles", toJson f.stretch), ("scl_stuck", toJson f.sclStuck),
  ("expected_pulses", toJson (if f.sclStuck then (0 : Nat) else 9)),
  ("expected_sda_sample", toJson (!f.sclStuck && f.releaseAfter.isSome)),
  ("expected_outcome", toJson (if f.sclStuck then (6 : Nat) else 5))]

/-- The untrusted producer deduplicates canonical parameter projections. The
separate PairedImage checker compares both successor choices and every used slot. -/
private def lowered (p : Execution.Image) : Storage.PairedImage.Image := Id.run do
  let parameters := ((List.range (p.last.val + 1)).map fun k =>
    Storage.PairedImage.parameter (Execution.fields (p.fetch (BitVec.ofNat 8 k).toFin))).eraseDups
  let token (node : Storage.PairedImage.Node) : BitVec 32 := match node with
    | none => 7
    | some pc =>
      let f := Execution.fields (p.fetch pc.toFin)
      if f.kind == 4 then 4 else
        let index := BitVec.ofNat 5 (parameters.idxOf (Storage.PairedImage.parameter f))
        (0#2) ++ pc ++ index ++ f.duration ++ f.enabled ++ f.levels ++ f.kind
  return {
    parameters := Vector.ofFn fun k => parameters[k.val]?.getD 0
    rows := Vector.ofFn fun k => if k.val ≤ p.last.val then
      token (Storage.PairedImage.successor p (BitVec.ofFin k) true) ++
        token (Storage.PairedImage.successor p (BitVec.ofFin k) false)
      else (4#32) ++ (4#32)
    boot := token (some 0)
    idle := p.idle.enabled ++ p.idle.levels }

/-- Ideal digital target observes resolved clock transitions, independently of
reference phases/PCs. The emitted-RTL gate adds callback/sampler latency checks. -/
private def checkRun (f : Fixture) (transform : RecoveryProgram → RecoveryProgram := id)
    (guardLoss : Bool := false) : IO Unit := do
  let c := cfg f
  let p := transform (program c)
  let store := Execution.directStore (Execution.imageWords p) p.idle p.last
  let mut reference := I2C.Recovery.initial c
  let mut core := Engine.Reactive.Fetch.start store 3
  let mut previous : I2C.Bus := {}
  let mut previousCommand : I2C.Pins := {}
  let mut stretchLeft := 0
  let mut rises := 0
  let mut sdaLow := true
  let mut guardBlocked := false
  let limit := 12 * (5 * c.phaseCycles + c.waitCycles + f.stretch + 8)
  for t in [:limit] do
    ensure (core == lift reference) s!"reference mismatch {f.name}/{t}"
    ensure (result core == I2C.Recovery.result reference) s!"result mismatch {f.name}/{t}"
    let command : I2C.Pins := ⟨if core.pins.enabled[0] then .low else .release, .release⟩
    ensure (core.pins.levels == 0 && !core.pins.enabled[1] && !core.pins.enabled[2])
      s!"SDA or unused output driven {f.name}/{t}"
    if previousCommand.scl == .low && command.scl == .release then
      stretchLeft := f.stretch
    let target : I2C.Pins :=
      ⟨if f.sclStuck || guardBlocked || stretchLeft > 0 then .low else .release,
        if sdaLow then .low else .release⟩
    let observed := I2C.resolve command target
    if !previous.scl && observed.scl then
      rises := rises + 1
      if f.releaseAfter.any (rises ≥ ·) then sdaLow := false
    ensure (rises ≤ 9) s!"more than nine observed rises {f.name}/{t}"
    let bus : I2C.Bus := {observed with sda := !sdaLow}
    if guardLoss && rises == 1 then
      -- The target drops SCL after the wait has accepted its first high. The next
      -- guarded observation must abort rather than continue issuing clocks.
      guardBlocked := true
    let inputs := Compile.I2C.encodeInputs bus
    ensure ((Engine.Reactive.Fetch.step store core true true inputs).pins == {})
      s!"reset did not release lines {f.name}/{t}"
    core := Engine.Reactive.Fetch.advance store core inputs
    reference := I2C.Recovery.step c reference bus
    previous := bus
    previousCommand := command
    stretchLeft := stretchLeft - 1
    if !Engine.Reactive.busy core then break
  ensure (core == lift reference) s!"terminal reference mismatch {f.name}"
  ensure (result core == some (if guardLoss then .busFault else expected f))
    s!"unexpected result {f.name}: {repr (result core)}"
  ensure (core.pins == {}) s!"terminal drivers not released {f.name}"
  ensure (rises == if f.sclStuck then 0 else if guardLoss then 1 else 9)
    s!"unexpected pulse count {f.name}: {rises}"
  ensure (core.samples[0] == (!guardLoss && !f.sclStuck && f.releaseAfter.isSome))
    s!"terminal SDA sample {f.name}"
  for slot in [1:16] do
    ensure (!core.samples[slot]!) s!"unreserved capture slot changed {f.name}/{slot}"
  ensure (Engine.Reactive.Fetch.advance store core 0 == core)
    s!"terminal state not retained {f.name}"

private def validate (f : Fixture) : IO String := do
  ensure (1 ≤ f.phase && f.phase ≤ 256 && 1 ≤ f.timeout && f.timeout ≤ 256 &&
    f.releaseAfter.all (fun n => 1 ≤ n && n ≤ 9) && f.stretch < f.timeout)
    s!"invalid recovery fixture {f.name}"
  let p := program (cfg f)
  let words := Execution.imageWords p
  ensure (p.last.val + 1 == 30 && words.toList.eraseDups.length ≤ 32)
    s!"E64 capacity {f.name}"
  let some indexed := Execution.lowerIndexed words
    | throw (IO.userError s!"indexed lowering {f.name}")
  ensure (indexed.val.expand == words) s!"indexed certificate {f.name}"
  let paired := lowered p
  ensure (Storage.PairedImage.check p paired (Storage.PairedImage.upload paired))
    s!"paired certificate {f.name}"
  let index := (Storage.PairedImage.index paired.boot).toNat
  let wrong := {paired with parameters := paired.parameters.set index (paired.parameters[index]! ^^^ 1)}
  ensure (!Storage.PairedImage.check p wrong (Storage.PairedImage.upload wrong))
    s!"wrong qualifier/capture parameter certified {f.name}"
  for pc in [:256] do
    ensure (Execution.decode words[pc]! == some (p.fetch (BitVec.ofNat 8 pc).toFin))
      s!"canonical E64 decode {f.name}/{pc}"
  checkRun f
  return f.name ++ " " ++ String.intercalate " " (([p.last.val, p.idle.levels.toNat,
    p.idle.enabled.toNat] ++ words.toList.map BitVec.toNat).map toString)

private def baseline : List Fixture :=
  (List.range 9).map (fun n => {name := s!"i2c-clear-release{n + 1}", releaseAfter := some (n + 1)}) ++
  [{name := "i2c-clear-still-stuck", releaseAfter := none},
   {name := "i2c-clear-stretch3", releaseAfter := some 5, stretch := 3},
   {name := "i2c-clear-scl-stuck", sclStuck := true}]

private def negatives : IO Unit := do
  let f : Fixture := {name := "capture-control"}
  let variants : List (String × (RecoveryProgram → RecoveryProgram)) := [
    ("ninth capture removed", fun p => {p with memory := p.memory.map fun i => match i with
      | .checked a => .checked {a with terminalCapture := none} | _ => i}),
    ("capture wrong slot", fun p => {p with memory := p.memory.map fun i => match i with
      | .checked a => .checked {a with terminalCapture := a.terminalCapture.map (fun c => {c with destination := 1})}
      | _ => i}),
    ("stop after eight pulses", fun p => {p with memory := p.memory.set 25 .halt}),
    ("skip recovered bus qualification", fun p => {p with memory := p.memory.set 28 .halt})]
  for (name, transform) in variants do
    let error ← try
      checkRun f transform
      pure none
    catch e => pure (some e.toString)
    ensure (error.any (fun s => (s.splitOn "mismatch").length > 1))
      s!"mutation not rejected {name}: {error}"
  checkRun {name := "guard-loss"} id true

def main (args : List String) : IO Unit := do
  let out : System.FilePath ← match args with
    | [] => pure "build/i2c-recovery"
    | [path] => pure path
    | _ => throw (IO.userError "usage: I2CRecovery.lean [output-directory]")
  IO.FS.createDirAll out
  let lines ← baseline.mapM validate
  for (phase, timeout) in [(1, 1), (256, 256)] do
    for releaseAfter in [some 9, none] do
      let _ ← validate {name := s!"boundary-{phase}-{releaseAfter}", phase, timeout, releaseAfter}
    let _ ← validate {name := s!"scl-boundary-{phase}", phase, timeout, sclStuck := true}
  negatives
  IO.FS.writeFile (out / "images.txt") (String.intercalate "\n" lines ++ "\n")
  IO.FS.writeFile (out / "metadata.json") ((Lean.Json.arr (baseline.map metadata).toArray).pretty ++ "\n")
  IO.println "I2C recovery: 12 wire fixtures, releases 1..9, persistent SDA/SCL, stretch; six min/max checks, guarded fault and four compiler mutations; canonical E64/indexed/paired certificates passed."
