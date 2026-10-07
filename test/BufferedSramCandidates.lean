import Pinwheel.Hardware.Buffered.SramCandidates
import Pinwheel.Hardware.Buffered.SramProofs
import Lean

/-! Address and latency-one fixtures. These exercise the actual reactive
dispatch expressions, forced candidates, counted rollovers and unrelated SRAM
power-up contents. Whole-controller execution is checked separately. -/
open Pinwheel.Hardware
open Pinwheel.Hardware.Buffered

open Lean Elab Command in
elab "#audit_buffered_sram_candidates" : command => do
  let env ← getEnv
  let mut declarations : Nat := 0
  let mut proofs : Nat := 0
  for (name, info) in env.constants.toList do
    if name.toString.startsWith "Pinwheel.Hardware.Buffered.SramCandidates." then
      declarations := declarations + 1
      if info.isTheorem then proofs := proofs + 1
      let axioms ← collectAxioms name
      let unexpected := axioms.filter fun ax =>
        ax != ``propext && ax != ``Classical.choice && ax != ``Quot.sound
      unless unexpected.isEmpty do
        throwError "Unapproved buffered SRAM candidate axioms: {unexpected}"
  logInfo m!"Buffered SRAM candidates: {declarations} declarations, {proofs} theorems; standard axioms only."

#audit_buffered_sram_candidates

open Lean Elab Command in
elab "#audit_buffered_sram_schedule" : command => do
  let env ← getEnv
  let mut declarations : Nat := 0
  let mut proofs : Nat := 0
  for (name, info) in env.constants.toList do
    if name.toString.startsWith "Pinwheel.Hardware.Buffered.Sram." then
      declarations := declarations + 1
      if info.isTheorem then proofs := proofs + 1
      let axioms ← collectAxioms name
      let unexpected := axioms.filter fun ax =>
        ax != ``propext && ax != ``Classical.choice && ax != ``Quot.sound
      unless unexpected.isEmpty do
        throwError "Unapproved actual buffered SRAM scheduling axioms: {unexpected}"
  logInfo m!"Actual buffered SRAM schedule: {declarations} declarations, {proofs} theorems; standard axioms only."

#audit_buffered_sram_schedule

private def check (ok : Bool) (label : String) : IO Unit :=
  unless ok do throw (IO.userError ("Buffered SRAM candidate failure: " ++ label))

private def inputs (command : Nat := 0) (raw : Nat := 0)
    (cold : Bool := false) : Values Reactive.Input
  | _, .initialize => BitVec.ofBool cold
  | _, .command => BitVec.ofNat 3 command
  | _, .rawInputs => BitVec.ofNat 2 raw
  | _, .expectedGeneration => 1
  | _, .txLength => 32
  | _, .rxCapacity => 32
  | _, _ => 0

private def endpoint (pc : Nat) (halt : Bool) : Nat :=
  halt.toNat + (pc % 1024)*2 + (pc % 128)*2^11

private def branches (finish : Nat) (yesHalt noHalt : Bool) : BitVec 54 :=
  BitVec.ofNat 54 (finish + endpoint 2 yesHalt*2^6 + endpoint 5 noHalt*2^30)

private def loopControl : BitVec 22 :=
  BitVec.ofNat 22 (2 + 1*2^8 + 1*2^11 + 1*2^17 + 2^20 + 2^21)

private def state (phase remaining sample guard finish : Nat)
    (yesHalt noHalt : Bool) (outer inner : Nat := 0) : Values Reactive.Register
  | _, .phase => BitVec.ofNat 3 phase
  | _, .pc => 2
  | _, .remaining => BitVec.ofNat 8 remaining
  | _, .stage1 => 3
  | _, .stage2 => BitVec.ofNat 2 sample
  | _, .scratch => 32768
  | _, .cachedCheck => BitVec.ofNat 4 (if guard == 0 then 0 else 5)
  | _, .cachedWait => 2
  | _, .cachedTerminal => 1
  | _, .cachedBranch => branches finish yesHalt noHalt
  | _, .currentControl => loopControl
  | _, .outer => BitVec.ofNat 3 outer
  | _, .inner => BitVec.ofNat 3 inner
  | _, .valid => 1
  | _, .count => 64
  | _, .virtualSpan => 1024
  | _, .generation => 1
  | _, _ => 0

private def changedIgnored (s : Values Reactive.Register) : Values Reactive.Register
  | _, .stage1 => 0
  | _, .stage2 => 3
  | _, .scratch => 65535
  | _, .txData => 1234
  | _, .rxData => 5678
  | _, r => s r

private def addressCases : IO Nat := do
  let mut checked := 0
  for phase in List.range 8 do
    for remaining in [0, 1] do
      for sample in List.range 4 do
        for guard in [0, 1] do
          for finish in List.range 4 do
            for yesHalt in [false, true] do
              for noHalt in [false, true] do
                for (outer, inner) in [(0, 0), (0, 1), (1, 1)] do
                  let s : Values Reactive.Register :=
                    state phase remaining sample guard finish yesHalt noHalt outer inner
                  if Reactive.entering.eval inputs s == 1 then
                    check (Reactive.starting.eval inputs s == 0)
                      "ordinary command cannot START"
                    check (Reactive.entryPC.eval inputs s == SramCandidates.chosen.eval inputs s)
                      "actual entry selects a prefetched candidate"
                  for b in [false, true] do
                    let expected := (SramCandidates.candidate b).eval inputs s
                    check ((SramCandidates.candidate b).eval (inputs 7 3 true) s == expected)
                      "candidate ignores every changed input"
                    check ((SramCandidates.candidate b).eval inputs (changedIgnored s) == expected)
                      "candidate ignores sampler stages, scratch and buffers"
                  checked := checked + 1
  return checked

private def countedLoops : IO Unit := do
  for (outer, inner, wanted) in [(0, 0, 1), (0, 1, 0), (1, 1, 3)] do
    let s : Values Reactive.Register := state 1 0 0 0 0 false false outer inner
    check (Reactive.entryPC.eval inputs s == BitVec.ofNat 7 wanted)
      "reference inner restart, outer restart, nested exit"
    for b in [false, true] do
      check ((SramCandidates.candidate b).eval inputs s == BitVec.ofNat 7 wanted)
        "counted candidate agrees with the physical rollover"

private def starts : IO Unit := do
  for phase in [0, 5, 6, 7] do
    for sample in List.range 4 do
      let s : Values Reactive.Register := state phase 0 sample 0 2 false false
      check (Reactive.starting.eval (inputs 3) s == 1)
        "free valid states accept START"
      check (Reactive.entryPC.eval (inputs 3) s == 0)
        "START ignores old branch endpoints and returns to row zero"

private def memoryCases : IO Unit := do
  let arrays : Fin 2 → Memory.Sram.State 6 64 := fun port =>
    ⟨fun k => BitVec.ofNat 64 (91 + port.val*101 + k.toNat), BitVec.ofNat 64 (71 + port.val)⟩
  check ((arrays 0).q != (arrays 1).q &&
      (arrays 0).contents 63 != (arrays 1).contents 63)
    "independent arbitrary initial cells and Q"
  let writes : List (Memory.Request 6 64 2) := [
    ⟨⟨true, 0, 4096⟩, fun _ => 63⟩,
    ⟨⟨true, 1, 8192⟩, fun _ => 63⟩,
    ⟨⟨true, 2, 16384⟩, fun _ => 63⟩]
  let uploaded := writes.foldl (fun arrays request => Memory.Sram.step request arrays) arrays
  for port in List.finRange 2 do
    check ((uploaded port).q == (arrays port).q) "writes hold Q"
    check ((uploaded port).contents 0 == 4096 && (uploaded port).contents 1 == 8192 &&
        (uploaded port).contents 2 == 16384) "full-word writes broadcast to every replica"
    check ((uploaded port).contents 63 == (arrays port).contents 63)
      "unwritten tail stays arbitrary"
  let candidates : Fin 2 → BitVec 6 := fun port => if port == 0 then 1 else 2
  let ready := Memory.Sram.step (SramCandidates.readRequest candidates) uploaded
  check ((ready 0).q == 8192 && (ready 1).q == 16384)
    "two distinct candidates are available after one read edge"
  let following := Memory.Sram.step (SramCandidates.readRequest (fun _ => 0)) ready
  check ((ready 0).q != (following 0).q && (following 0).q == 4096)
    "following request does not retroactively change current response"
  let tail := Memory.Sram.step (SramCandidates.readRequest (fun _ => 63)) ready
  check ((tail 0).q != (tail 1).q &&
      SramCandidates.project false (tail 0).q == (0 : BitVec 64) &&
      SramCandidates.project false (tail 1).q == (0 : BitVec 64))
    "projection hides unrelated stale responses without clearing SRAM"
  let knownModel := writes.foldl Memory.Sram.Model.step Memory.Sram.Model.initial
  check (knownModel.contents 0 == some 4096 && knownModel.contents 1 == some 8192 &&
      knownModel.contents 2 == some 16384 && knownModel.contents 63 == none)
    "partial model only knows uploaded words"

private def upload (address instruction : Nat) : Values Sram.Input
  | _, .base .command => 1
  | _, .base .address => BitVec.ofNat 6 address
  | _, .base .word => BitVec.ofNat 64 instruction
  | _, .base p => inputs 0 0 false p
  | _, .q false => 121
  | _, .q true => 233

private def controllerState (phase : Nat := 0) : Values Sram.Register
  | _, .core .phase => BitVec.ofNat 3 phase
  | _, .startWord => 77
  | _, _ => 0

private def actualUpload : IO Unit := do
  let arrays : Fin 2 → Memory.Sram.State 6 64 := fun port =>
    ⟨fun k => BitVec.ofNat 64 (91 + port.val*101 + k.toNat), BitVec.ofNat 64 (71 + port.val)⟩
  let s : Values Sram.Register := controllerState
  let i : Values Sram.Input := upload 0 4096
  check ((Sram.request .write).eval i s == 1 && (Sram.request .read).eval i s == 0)
    "accepted row write occupies both actual single ports"
  check ((Sram.request (.address false)).eval i s == 0 &&
      (Sram.request (.address true)).eval i s == 0 && (Sram.request .data).eval i s == 4096)
    "actual ports broadcast row-zero address and instruction"
  let stepped := Memory.Sram.step (Sram.arrayRequest i s) arrays
  for port in List.finRange 2 do
    check ((stepped port).contents 0 == 4096 && (stepped port).q == (arrays port).q)
      "actual typed request updates both arrays and holds both Q"
  check ((Sram.circuit.step i s) .startWord == 4096)
    "same actual row-zero write updates START mirror"
  check ((Sram.circuit.step (upload 1 8192) s) .startWord == 77)
    "nonzero row leaves START mirror unchanged"
  let busy : Values Sram.Register := controllerState 1
  check ((Sram.request .write).eval i busy == 0 &&
      (Sram.request .read).eval i busy == 1 &&
      (Sram.circuit.step i busy) .startWord == 77)
    "busy rejected row write remains a read edge and preserves mirror"

def main : IO Unit := do
  let cases ← addressCases
  check (cases == 6144) "complete bounded address case inventory"
  countedLoops
  starts
  memoryCases
  actualUpload
  IO.println s!"Buffered SRAM candidates: {cases} address/dependency cases, 3 nested loop transitions, 16 START cases, arbitrary-initial SRAM write/read/projection and actual-controller upload-port fixtures passed."
