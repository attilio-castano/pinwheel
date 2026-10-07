import Pinwheel.Program.Buffered
import Pinwheel.Program.BufferedI2C
import Lean.Data.Json

/-! Actual Lean reactive-buffer snapshots for finite cross-language comparison.
Stdout contains one JSON object. The admitted owner has one local identity;
wrapper device identities and protocol correctness are outside these vectors. -/
open Lean (Json toJson)
open Pinwheel.Program.Buffered
open Pinwheel.Engine.Reactive (Pins Inputs Action Check Capture)
open Pinwheel.Engine.Reactive.Counted (Schedule)

private def captureJson (capture : Option (Capture 15)) : Json :=
  match capture with
  | none => Json.null
  | some c => toJson [c.input.val, c.destination.val]

private def targetJson : Target → Json
  | .next => Json.null
  | .absolute pc => toJson pc.val

private def finishJson : Finish → Json
  | .sequential => Json.null
  | .jump target => toJson target.val
  | .branch sample yes no => Json.arr #[toJson sample.val, targetJson yes, targetJson no]

private def actionFields (action : Action 15) : List (String × Json) :=
  [("duration", toJson action.duration), ("levels", toJson action.pins.levels.toNat),
   ("enabled", toJson action.pins.enabled.toNat), ("entry_capture", captureJson action.capture)]

private def instructionJson (instruction : Instruction) : Json :=
  let fields := [("append_input", instruction.append.map (toJson ∘ Fin.val) |>.getD Json.null)]
  let preserved := [("preserve", toJson instruction.preserveLevels.toNat),
    ("preserve_enabled", toJson instruction.preserveEnabled.toNat)]
  let operation := match instruction.operation with
    | .drive action => [("kind", toJson "drive")] ++ actionFields action
    | .shift output enable invert action => [("kind", toJson "shift"),
        ("shift_pin", toJson output.val), ("shift_enabled", toJson enable),
        ("shift_invert", toJson invert)] ++ actionFields action
    | .keep levels enabled action => [("kind", toJson "keep"),
        ("preserve", toJson levels.toNat), ("preserve_enabled", toJson enabled.toNat)] ++ actionFields action
    | .wait wait => [("kind", toJson "wait"), ("levels", toJson wait.pins.levels.toNat),
        ("enabled", toJson wait.pins.enabled.toNat), ("wait_input", toJson wait.condition.input.val),
        ("wait_level", toJson wait.condition.level), ("budget", toJson (wait.budgetMinusOne.val + 1))] ++ preserved
    | .checked action guard terminal finish => [("kind", toJson "checked"),
        ("check_mask", toJson guard.mask.toNat), ("check_value", toJson guard.value.toNat),
        ("terminal_capture", captureJson terminal), ("finish", finishJson finish)] ++ actionFields action ++ preserved
    | .qualify qualify => [("kind", toJson "qualify"),
        ("levels", toJson qualify.pins.levels.toNat), ("enabled", toJson qualify.pins.enabled.toNat),
        ("duration", toJson (qualify.durationMinusOne.val + 1)),
        ("budget", toJson (qualify.budgetMinusOne.val + 1)),
        ("check_mask", toJson qualify.condition.mask.toNat),
        ("check_value", toJson qualify.condition.value.toNat)] ++ preserved
    | .halt => [("kind", toJson "halt")]
    | .fault outcome => [("kind", toJson "fault"), ("outcome", toJson (match outcome with
        | .timeout => "timeout" | _ => "fault"))]
  Json.mkObj (operation ++ fields)

private def scheduleJson : Schedule Instruction → Json
  | .emit instruction => Json.mkObj [("kind", toJson "emit"), ("instruction", instructionJson instruction)]
  | .seq first rest => Json.mkObj [("kind", toJson "seq"),
      ("first", scheduleJson first), ("rest", scheduleJson rest)]
  | .repeat n body => Json.mkObj [("kind", toJson "repeat"),
      ("count", toJson (n.val + 1)), ("body", scheduleJson body)]

private def stateJson (s : State) : Json :=
  let (control, stop, pc, remaining, waitLeft) := match s.core.control with
    | .stopped reason => ("stopped", toJson (match reason with
        | .ready => "ready" | .completed => "complete" | .fault => "fault" | .timeout => "timeout"),
        Json.null, Json.null, Json.null)
    | .active pc remaining => ("active", Json.null, toJson pc.val, toJson remaining.val, Json.null)
    | .waiting pc remaining => ("waiting", Json.null, toJson pc.val, toJson remaining.val, Json.null)
    | .checked pc remaining => ("checked", Json.null, toJson pc.val, toJson remaining.val, Json.null)
    | .qualifying pc remaining waitLeft => ("qualifying", Json.null, toJson pc.val,
        toJson remaining.val, toJson waitLeft.val)
  let (phase, consumed, rx, outcome) := match s.buffers.slot with
    | .running execution => ("running", execution.txConsumed, execution.rx, Json.null)
    | .completed completion => ("completed", completion.execution.txConsumed, completion.execution.rx,
        toJson (match completion.outcome with | .complete => "complete" | .fault => "fault" | .timeout => "timeout"))
    | .free => ("free", 0, [], Json.null)
    | .preparing _ => ("preparing", 0, [], Json.null)
  Json.mkObj [("control", toJson control), ("stop_reason", stop), ("pc", pc),
    ("remaining", remaining), ("wait_left", waitLeft), ("samples", toJson s.core.samples.toList),
    ("levels", toJson s.core.pins.levels.toNat), ("enabled", toJson s.core.pins.enabled.toNat),
    ("sampler_first", toJson s.samplerFirst.toNat), ("sampler_second", toJson s.samplerSecond.toNat),
    ("phase", toJson phase), ("tx_consumed_bits", toJson consumed), ("rx_bits", toJson rx), ("outcome", outcome)]

private def makeProgram (code : Schedule Instruction) (idle : Pins) : IO Program :=
  if fits : code.span ≤ 1024 then
    if nodesFit : code.nodes ≤ 256 then
      if nestingFit : code.nesting ≤ 2 then return ⟨code, idle, fits, nodesFit, nestingFit⟩
      else throw (IO.userError "fixture nesting exceeded")
    else throw (IO.userError "fixture nodes exceeded")
  else throw (IO.userError "fixture span exceeded")

private def caseJson (name : String) (code : Schedule Instruction) (tx : List Bool)
    (rxLimit rxDemand : Nat) (incoming : List Nat) (idle : Pins := ⟨0, 0⟩) : IO Json := do
  let p ← makeProgram code idle
  let capacity : Pinwheel.Program.Transfer.Capacity := ⟨tx.length, rxLimit⟩
  let owner : Pinwheel.Program.Transfer.Identity := ⟨0, 1⟩
  let prepared := Pinwheel.Program.Transfer.step capacity {} (.prepare 0 tx rxLimit)
  let buffers := (Pinwheel.Program.Transfer.step capacity prepared.state (.start owner 0)).state
  let before := start p capacity (initial p buffers owner)
  let mut s := before
  let mut states : Array Json := #[]
  for pads in incoming do
    s := advance p capacity s (BitVec.ofNat 2 pads)
    states := states.push (stateJson s)
  return Json.mkObj [("name", toJson name), ("program", Json.mkObj [
      ("schedule", scheduleJson code), ("idle_levels", toJson idle.levels.toNat),
      ("idle_enabled", toJson idle.enabled.toNat), ("virtual_span", toJson code.span),
      ("stored_words", toJson code.words), ("stored_nodes", toJson code.nodes),
      ("loop_count", toJson code.loops), ("nesting", toJson code.nesting)]),
    ("tx_capacity_bits", toJson capacity.txBits), ("rx_capacity_bits", toJson capacity.rxBits),
    ("tx_bits", toJson tx), ("rx_limit", toJson rxLimit), ("tx_demand", toJson tx.length),
    ("rx_demand", toJson rxDemand), ("rx_max", toJson rxLimit),
    ("initial_state", stateJson before), ("incoming", toJson incoming), ("states", Json.arr states)]

private def emit (operation : Operation) (append : Option (Fin 2) := none)
    (preserve preserveEnabled : BitVec 3 := 0) : Schedule Instruction :=
  .emit ⟨operation, append, preserve, preserveEnabled⟩

private def action (duration : Fin 256 := 0) (levels enabled : BitVec 3 := 0)
    (capture : Option (Capture 15) := none) : Action 15 := ⟨⟨levels, enabled⟩, duration, capture⟩

private def chain : List (Schedule Instruction) → Schedule Instruction
  | [] => emit .halt
  | [last] => last
  | first :: rest => .seq first (chain rest)

private def i2cInputs (nack : Option Nat) (blockFrom : Option Nat) : List Nat := Id.run do
  let p := Pinwheel.Program.BufferedI2C.program 3 31
  let tx := (List.range 24).map fun n => n % 3 == 1
  let capacity : Pinwheel.Program.Transfer.Capacity := ⟨24, 32⟩
  let owner : Pinwheel.Program.Transfer.Identity := ⟨0, 1⟩
  let prepared := Pinwheel.Program.Transfer.step capacity {} (.prepare 0 tx 32)
  let buffers := (Pinwheel.Program.Transfer.step capacity prepared.state (.start owner 0)).state
  let mut s := start p capacity (initial p buffers owner)
  let mut incoming : Array Nat := #[]
  for cycle in [:1100] do
    let pc := match s.core.control with
      | .active pc _ | .waiting pc _ | .checked pc _ | .qualifying pc _ _ => pc.val
      | .stopped _ => 0
    let stage := if 35 ≤ pc && pc ≤ 38 then some 0
      else if 71 ≤ pc && pc ≤ 74 then some 1
      else if 112 ≤ pc && pc ≤ 115 then some 2 else none
    let pads := if blockFrom.any (fun target => target ≤ pc) then 2
      else if stage.isSome then if stage == nack then 3 else 1
      else if 116 ≤ pc && pc < 260 then 1 + 2 * (cycle % 3)
      else 3
    incoming := incoming.push (pads % 4)
    s := advance p capacity s (BitVec.ofNat 2 pads)
  return incoming.toList

def main : IO Unit := do
  let mut cases : Array Json := #[]
  let halted := emit .halt
  for pattern in [:16] do
    let pads := (List.range 48).map fun n => (pattern / (2 ^ (n % 4))) % 2 + 2 * (n % 2)
    for duration in [0, 1, 3] do
      let d : Fin 256 := Fin.ofNat 256 duration
      let body := .seq (emit (.shift 1 true true (action d 0 1)) (some 0))
        (emit (.keep 0 2 (action d 0 0 (some ⟨1, 5⟩))) (some 1))
      let code := .seq (.repeat 1 (.repeat 1 body)) halted
      cases := cases.push (← caseJson s!"nested-shift-keep-{pattern}-{duration}" code
        [false, true, true, false] 8 8 pads ⟨0, 0⟩)
  for budget in [0, 1, 3] do
    let b : Fin 256 := Fin.ofNat 256 budget
    for pattern in [:16] do
      let pads := (List.range 24).map fun n => (pattern / (2 ^ (n % 4))) % 2
      let code := .seq (emit (.drive (action 0 2 7)) (some 1))
        (.seq (emit (.wait ⟨⟨0, 0⟩, ⟨0, true⟩, b⟩) (some 0) 2 2)
          (.seq (emit (.qualify ⟨⟨0, 0⟩, ⟨1, 1⟩, 1, b⟩) (some 1) 2 2) halted))
      cases := cases.push (← caseJson s!"wait-qualify-{budget}-{pattern}" code [] 3 3 pads)
  for pattern in [:16] do
    let pads := (List.range 32).map fun n => (pattern / (2 ^ (n % 4))) % 2 + 2 * (n % 2)
    let code := .seq (emit (.checked (action 1 2 7 (some ⟨1, 3⟩)) ⟨1, 1⟩ (some ⟨0, 0⟩)
        (.branch 0 (.absolute 0) .next)) (some 1) 2 2) halted
    cases := cases.push (← caseJson s!"checked-self-entry-{pattern}" code [] 6 0 pads)
    let code := .seq (emit (.checked (action 0 0 0) ⟨0, 0⟩ (some ⟨0, 0⟩)
        (.branch 0 (.absolute 2) .next)))
      (.seq (emit (.shift 2 false false (action 0 0 7)) (some 1)) halted)
    cases := cases.push (← caseJson s!"terminal-branch-{pattern}" code [true] 1 1 pads)
  let underflow := .seq (emit (.shift 0 false false (action 0 0 7 (some ⟨0, 2⟩))) (some 1)) halted
  cases := cases.push (← caseJson "underflow-entry" underflow [] 1 1 [0, 1, 2, 3])
  let overflow := .seq (emit (.shift 0 false false (action 0 0 7 (some ⟨0, 2⟩))) (some 1)) halted
  cases := cases.push (← caseJson "overflow-after-consume" overflow [true] 0 0 [0, 1, 2, 3])
  for outcome in [Failure.fault, .timeout] do
    let code := .seq (emit (.drive (action 0 7 7)) (some 0)) (emit (.fault outcome))
    cases := cases.push (← caseJson s!"explicit-{repr outcome}" code [] 1 0 [0, 1, 2, 3])
  let runaway := emit (.checked (action 0 0 7) ⟨0, 0⟩ none (.jump 1023))
  cases := cases.push (← caseJson "out-of-span-jump" runaway [] 0 0 [0, 1, 2, 3])
  let malformed := emit (.checked (action 0 0 7 (some ⟨0, 1⟩)) ⟨0, 0⟩ none
      (.branch 0 .next (.absolute 1023))) (some 0)
  let full := .repeat 7 (.repeat 7 (chain (List.replicate 15 (emit (.drive (action 0))) ++ [malformed])))
  cases := cases.push (← caseJson "full-span-eager-branch-admission" full [] 8 0 (List.replicate 32 3))
  let boundary (finish : Finish) := .repeat 7 (.repeat 7 (chain (
    [emit (.checked (action 0 0 7 (some ⟨0, 0⟩)) ⟨0, 0⟩ none (.jump 1023))] ++
    List.replicate 14 (emit (.drive (action 0))) ++
    [emit (.checked (action 0 0 7 (some ⟨0, 1⟩)) ⟨0, 0⟩ none finish) (some 0)])))
  cases := cases.push (← caseJson "unused-next-at-1023" (boundary (.branch 0 (.absolute 0) .next))
    [] 8 0 [3, 3, 3, 3])
  cases := cases.push (← caseJson "sequential-at-1023" (boundary .sequential)
    [] 8 0 [3, 3, 3, 3])
  let tx := (List.range 24).map fun n => n % 3 == 1
  let code := (Pinwheel.Program.BufferedI2C.program 3 31).code
  cases := cases.push (← caseJson "i2c-four-byte-complete" code tx 32 32 (i2cInputs none none))
  for stage in [:3] do
    cases := cases.push (← caseJson s!"i2c-nack-{stage}" code tx 32 32 (i2cInputs (some stage) none))
  for pc in [0, 136, 263] do
    cases := cases.push (← caseJson s!"i2c-timeout-at-{pc}" code tx 32 32 (i2cInputs none (some pc)))
  IO.println (Json.mkObj [("schema", toJson "pinwheel-buffered-reactive-vectors-v1"),
    ("cases", Json.arr cases)]).compress
