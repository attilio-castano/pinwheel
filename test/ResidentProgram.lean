import Pinwheel.Program.ResidentProofs
import Pinwheel.Hardware.Storage.PairedValidation

/-! Local differential checks for the typed resident model. Each edge starts
from a concrete matching execution snapshot with an admitted source and its
successor row already available. This suite does not initialize the loader,
SRAM, UART or result mailbox and does not assert their lifecycle refinement. -/
open Pinwheel.Hardware Pinwheel.Hardware.Storage
open PairedController

private def ensure (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw (IO.userError message)

private def program (memory : Fin 256 → Pinwheel.Program.Resident.Instruction) (last : Fin 256 := 2)
    (idle : Pinwheel.Engine.Reactive.Pins := ⟨0, 0⟩) : Pinwheel.Program.Resident.Program := ⟨Vector.ofFn memory, idle, last⟩

private def slots (value : Nat) : Vector Bool 16 :=
  Vector.ofFn fun k => value / 2 ^ k.val % 2 == 1

private def packed (samples : Vector Bool 16) : BitVec 16 :=
  BitVec.ofNat 16 ((List.range 16).foldl
    (fun total k => total + if samples[k]! then 2 ^ k else 0) 0)

private def state (control : Pinwheel.Engine.Reactive.Control 255 := .stopped .ready)
    (levels : BitVec 3 := 5) (operand : BitVec 8 := 0xa6)
    (samples : Nat := 0x5a5a) : Pinwheel.Program.Resident.State := ⟨⟨control, ⟨levels, 7⟩, slots samples⟩, operand⟩

private def pc : Pinwheel.Engine.Reactive.Control 255 → Fin 256
  | .active p _ | .waiting p _ | .checked p _ | .qualifying p _ _ => p
  | .stopped _ => 0

private def mode : Pinwheel.Engine.Reactive.Control 255 → BitVec 3
  | .stopped .ready => 0
  | .stopped .completed => 5
  | .stopped .timeout => 6
  | .stopped .fault => 7
  | .active _ _ => 1
  | .waiting _ _ => 2
  | .checked _ _ => 3
  | .qualifying _ _ _ => 4

private def remaining : Pinwheel.Engine.Reactive.Control 255 → BitVec 8
  | .active _ r | .waiting _ r | .checked _ r | .qualifying _ r _ => BitVec.ofFin r
  | .stopped _ => 0

private def waitLeft : Pinwheel.Engine.Reactive.Control 255 → BitVec 8
  | .qualifying _ _ r => BitVec.ofFin r
  | _ => 0

-- Independent paired-token bit positions, with three distinct parameter slots
-- for the current token and each possible successor. The actual execution
-- graph must select the right row half and the right slot on dispatch.
private def parameter (instruction : Pinwheel.Program.Resident.Instruction) : BitVec 20 :=
  let f := Execution.unpack (Pinwheel.Program.Resident.encode instruction)
  BitVec.ofNat 20 (if f.kind == 3 then f.budget.toNat + f.check.toNat * 4096
    else f.entry.toNat + f.terminal.toNat * 64 + f.check.toNat * 4096 + f.sample.toNat * 65536)

private def word (p : Pinwheel.Program.Resident.Program) (target : Option (Fin 256)) (index : Nat) : BitVec 32 :=
  match target with
  | none => 7
  | some target =>
    let f := Execution.unpack (Pinwheel.Program.Resident.encode (p.fetch target))
    if f.kind == 4 then 4 else BitVec.ofNat 32
      (f.kind.toNat + f.levels.toNat * 8 + f.enabled.toNat * 64 + f.duration.toNat * 512 +
        index * 131072 + target.val * 4194304)

private def successor (p : Pinwheel.Program.Resident.Program) (current : Fin 256) (choice : Bool) : Option (Fin 256) :=
  let target := match p.fetch current with
    | .ordinary (.checked c) => match c.finish with
      | .sequential => current.val + 1
      | .jump t => t.val
      | .branch _ yes no => if choice then yes.val else no.val
    | _ => current.val + 1
  if h : target ≤ p.last.val then some ⟨target, by have := p.last.isLt; omega⟩ else none

private def targetParameter (p : Pinwheel.Program.Resident.Program) : Option (Fin 256) → BitVec 20
  | none => 0
  | some target => parameter (p.fetch target)

private def snapshot (p : Pinwheel.Program.Resident.Program) (s : Pinwheel.Program.Resident.State) : Values Register
  | _, .parameter _ index =>
    if index.toNat == 1 then targetParameter p (successor p (pc s.core.control) false)
    else if index.toNat == 2 then targetParameter p (successor p (pc s.core.control) true)
    else parameter (p.fetch (pc s.core.control))
  | _, .boot _ => word p (some 0) 0
  | _, .idle _ => p.idle.enabled ++ p.idle.levels
  | _, .valid => 1
  | _, .current => word p (some (pc s.core.control)) 0
  | _, .cached => parameter (p.fetch (pc s.core.control))
  | _, .mode => mode s.core.control
  | _, .remaining => remaining s.core.control
  | _, .waitLeft => waitLeft s.core.control
  | _, .payload => s.operand
  | _, .levels => s.core.pins.levels
  | _, .enabled => s.core.pins.enabled
  | _, .samples => packed s.core.samples
  | _, _ => 0

private def machineInputs (reset start : Bool) (payload : BitVec 8)
    (incoming : Pinwheel.Engine.Reactive.Inputs) : Loader.Machine.Inputs :=
  {init := reset, command := if start then 5 else 0,
    data := payload.zeroExtend 64, incoming := incoming}

private def inputs (p : Pinwheel.Program.Resident.Program) (s : Pinwheel.Program.Resident.State)
    (reset start : Bool) (payload : BitVec 8) (incoming : Pinwheel.Engine.Reactive.Inputs) : Values Input
  | _, .base b => (machineInputs reset start payload incoming).values b
  | _, .q _ => word p (successor p (pc s.core.control) true) 2 ++
      word p (successor p (pc s.core.control) false) 1

private def edge (n : Netlist Register (SramController.Out Loader.Machine.Output) Input)
    (p : Pinwheel.Program.Resident.Program) (s : Pinwheel.Program.Resident.State) (reset start : Bool) (payload : BitVec 8)
    (incoming : Pinwheel.Engine.Reactive.Inputs) (label : String) : IO Pinwheel.Program.Resident.State := do
  let expected := Pinwheel.Program.Resident.step p s reset start payload incoming
  let actual : Values Register := n.step (inputs p s reset start payload incoming) (snapshot p s)
  ensure (actual .mode == mode expected.core.control) s!"{label}: control mode differs"
  ensure (actual .remaining == remaining expected.core.control) s!"{label}: duration differs"
  ensure (actual .waitLeft == waitLeft expected.core.control) s!"{label}: qualification budget differs"
  ensure (actual .levels == expected.core.pins.levels) s!"{label}: output levels differ"
  ensure (actual .enabled == expected.core.pins.enabled) s!"{label}: output enables differ"
  ensure (actual .samples == packed expected.core.samples) s!"{label}: captures differ"
  ensure (actual .payload == expected.operand) s!"{label}: owned operand differs"
  if Pinwheel.Engine.Reactive.busy expected.core then
    ensure ((actual .current).extractLsb' 22 8 == BitVec.ofFin (pc expected.core.control))
      s!"{label}: dispatch address differs"
  return expected

private def shiftCases (n : Netlist Register (SramController.Out Loader.Machine.Output) Input) : IO Nat := do
  let mut count := 0
  for duration in [0, 3, 255] do
    for output in [:3] do
      for order in [Pinwheel.Program.Resident.Order.lsbFirst, .msbFirst] do
        for payload in [:256] do
          let instruction : Pinwheel.Program.Resident.Instruction := .shift ⟨output % 3, Nat.mod_lt _ (by decide)⟩ order
            (BitVec.ofNat 8 duration).toFin ⟨BitVec.ofNat 3 (payload % 8), 7⟩
          let p := program (fun target => if target.val < 2 then instruction else .ordinary .halt)
          let owned := BitVec.ofNat 8 payload
          let entered ← edge n p (state) false true owned 0 "SHIFT entry"
          let bit := if order.isMsbFirst then payload / 128 else payload % 2
          let literal := payload % 8
          let expectedLevels := BitVec.ofNat 3 ((literal &&& (7 - 2 ^ output)) ||| (bit * 2 ^ output))
          let expectedOperand := BitVec.ofNat 8 (if order.isMsbFirst then payload * 2 else payload / 2)
          ensure (entered.core.pins.levels == expectedLevels && entered.operand == expectedOperand)
            "SHIFT typed semantics differs from arithmetic bit oracle"
          let next ← edge n p entered false true (owned ^^^ 255) 3 "SHIFT held/dispatch"
          if duration > 0 then
            ensure (next.operand == entered.operand) "Held SHIFT consumed the byte twice"
          else
            ensure (next.operand == Pinwheel.Program.Resident.shifted order entered.operand) "Dispatch did not consume the next owned bit"
          let _ ← edge n p entered true true 255 3 "SHIFT reset priority"
          count := count + 1
  return count

private def keepCases (n : Netlist Register (SramController.Out Loader.Machine.Output) Input) : IO Nat := do
  let mut count := 0
  for mask in [:8] do
    for old in [:8] do
      for literal in [:8] do
        let keep : Pinwheel.Program.Resident.Instruction := .keep (BitVec.ofNat 3 mask) ⟨BitVec.ofNat 3 literal, 3⟩ none 3
        let p := program (fun target => if target == 0 then keep else .ordinary .halt)
        let entered ← edge n p (state (.stopped .ready) (BitVec.ofNat 3 old)) false true 0x53 0 "KEEP entry"
        ensure (entered.core.pins.levels == BitVec.ofNat 3 ((old &&& mask) ||| (literal &&& (7 - mask))))
          "KEEP typed semantics differs from arithmetic mask oracle"
        let held ← edge n p entered false true 255 3 "KEEP hold"
        ensure (held.operand == 0x53) "KEEP lost START operand ownership"
        count := count + 1
  for pin in [:2] do
    for slot in [:16] do
      for incoming in [:4] do
        let capture : Pinwheel.Engine.Reactive.Capture 15 := ⟨(BitVec.ofNat 1 pin).toFin, (BitVec.ofNat 4 slot).toFin⟩
        let keep : Pinwheel.Program.Resident.Instruction := .keep 1 ⟨2, 7⟩ (some capture) 3
        let p := program (fun target => if target == 0 then .ordinary (.action ⟨⟨1, 7⟩, 0, none⟩)
          else if target == 1 then keep else .ordinary .halt)
        let old := state (.active 0 0) 1
        let entered ← edge n p old false true 255 (BitVec.ofNat 2 incoming) "KEEP capture dispatch"
        let expected := BitVec.ofNat 16 ((0x5a5a &&& (65535 - 2 ^ slot)) |||
          (((incoming / 2 ^ pin) % 2) * 2 ^ slot))
        ensure (packed entered.core.samples == expected && entered.operand == old.operand)
          "KEEP capture changed another slot or the owned operand"
        count := count + 1
  return count

private def controlCases (n : Netlist Register (SramController.Out Loader.Machine.Output) Input) : IO Nat := do
  let mut count := 0
  let shift : Pinwheel.Program.Resident.Instruction := .shift 0 .msbFirst 0 ⟨2, 7⟩
  -- A checked terminal capture chooses between different target kinds. The
  -- ordinary checked operation remains intact inside the resident language.
  let checked : Pinwheel.Program.Resident.Instruction := .ordinary (.checked
    ⟨⟨⟨4, 7⟩, 0, none⟩, ⟨2, 2⟩, some ⟨0, 0⟩, .branch 0 0 2⟩)
  let p := program (fun target => if target == 0 then shift else if target == 1 then checked else .ordinary .halt)
  for incoming in [:4] do
    let s := state (.checked 1 0) 4 0x53
    let _ ← edge n p s false true 255 (BitVec.ofNat 2 incoming) "checked guard/capture/branch"
    count := count + 1
  -- Re-entry into an unchanged PC is still an entry, and both terminal and
  -- entry captures must run. This catches entry detection based only on PC.
  let self : Pinwheel.Program.Resident.Instruction := .ordinary (.checked
    ⟨⟨⟨1, 7⟩, 0, some ⟨1, 1⟩⟩, ⟨0, 0⟩, some ⟨0, 0⟩, .branch 0 0 0⟩)
  let selfProgram := program (fun target => if target == 0 then self else .ordinary .halt)
  for incoming in [:4] do
    let _ ← edge n selfProgram (state (.checked 0 0) 1) false false 0
      (BitVec.ofNat 2 incoming) "checked self branch re-entry"
    count := count + 1
  let wait : Pinwheel.Program.Resident.Instruction := .ordinary (.wait ⟨⟨0, 3⟩, ⟨0, true⟩, 3⟩)
  let qualify : Pinwheel.Program.Resident.Instruction := .ordinary (.qualify ⟨⟨3, 7⟩, ⟨2, 2⟩, 3, 3⟩)
  for instruction in [wait, qualify] do
    let p := program (fun target => if target == 0 then instruction else if target == 1 then shift else .ordinary .halt)
    for incoming in [:4] do
      let entered ← edge n p (state) false true 0x53 (BitVec.ofNat 2 incoming) "wait/qualify entry"
      let _ ← edge n p entered false true 255 (BitVec.ofNat 2 incoming) "wait/qualify held"
      let terminal := match instruction with
        | .ordinary (.wait _) => state (.waiting 0 0) 0 0x53
        | _ => state (.qualifying 0 0 0) 3 0x53
      let _ ← edge n p terminal false true 255 (BitVec.ofNat 2 incoming) "wait/qualify dispatch/timeout"
      count := count + 3
  let lastShift := program (fun _ => shift) 0
  let _ ← edge n lastShift (state (.active 0 0) 1) false true 255 0 "out-of-range successor fault"
  count := count + 1
  let halted := program (fun _ => .ordinary .halt) 0
  let stopped ← edge n halted (state) false true 0x53 3 "immediate HALT retains accepted byte"
  let _ ← edge n halted stopped false false 255 0 "stopped hold"
  count := count + 2
  return count

def main : IO Unit := do
  let .ok n := PairedValidation.core | throw (IO.userError "Selected paired core construction failed")
  let shifts ← shiftCases n
  let keeps ← keepCases n
  let controls ← controlCases n
  IO.println s!"Typed resident program: {shifts} SHIFT cases, {keeps} KEEP cases, {controls} ordinary control edges passed against the selected paired graph; canonical source, timed entry/hold, START/reset ownership, terminal capture and self branch. Local admitted-source snapshots only; initialized package lifecycle remains separate."

#print axioms Pinwheel.Program.Resident.encode_canonical
#print axioms Pinwheel.Program.Resident.source_valid
#print axioms Pinwheel.Program.Resident.enter_shift
#print axioms Pinwheel.Program.Resident.enter_keep
#print axioms Pinwheel.Program.Resident.advance_ordinary
#print axioms Pinwheel.Program.Resident.active_held
#print axioms Pinwheel.Program.Resident.busy_start_ignored
#print axioms Pinwheel.Program.Resident.reset_priority
#print axioms Pinwheel.Program.Resident.start_as_enter
