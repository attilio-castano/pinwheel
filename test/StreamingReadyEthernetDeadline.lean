import Pinwheel.Program.StreamingEthernetPacedHost
import Pinwheel.Program.StreamingEthernetRefill

/-! Check the same quad host program that sends the existing Ethernet
fixture. Alternate service delays and use the final full-burst deadline
twice. The neighboring late launch misses the first unserved bit. -/
namespace StreamingReadyEthernetDeadline
open Pinwheel.Program StreamingReady StreamingEthernetCore
open StreamingEthernetDeadline StreamingEthernetPacedHost
open StreamingEthernetSchedule hiding bodyPins
open StreamingEthernetRefill (Policy bodyPins alignmentPins aligned reservationCut)
open StreamingEthernetFrame (frameBits)

set_option maxRecDepth 30000

private def onDeadline : Policy := fun k => #[0, 173, 64, 173, 64, 160, 28, 128][k.val]

private def pastDeadline : Policy := fun k => if k.val = 0 then 175 else if k.val = 1 then 64 else 0

private def framePins (policy : Policy) (highWidth : Nat) : List Session.Pins :=
  ((bodyPins policy highWidth).drop 16).take 3457

private def groups (policy : Policy) (highWidth : Nat) : Option (List CellInputs × Input) :=
  StreamingEthernetCredit.splitCells
    ((aligned policy highWidth).runtimeInputs program false (framePins policy highWidth))

private def pretrace (policy : Policy) (highWidth : Nat) : BitTrace :=
  (preloaded.traceRun program false (started.traceRun program false {} afterStart) (alignmentPins policy highWidth))

private theorem pretrace_related (policy : Policy) (highWidth : Nat) :
    let s := (aligned policy highWidth).core
    let trace := pretrace policy highWidth
    trace.Related s ∧ trace.NaturalCounts s ∧ s.Structural ∧ s.Progress := by
  let owner := started_and_preloaded
  have entry : started.core = StreamingReady.State.start program ready.core (ready.command startPin).runtime :=
    ready.core_admitted_start program false startPin owner.startRuntime (by simp [owner.command, owner.admitted])
  let start := (ready.command startPin).runtime
  have mid := started_trace program ready.core start (started.runtimeInputs program false afterStart)
  dsimp only at mid
  rw [← entry, ← started.run_core] at mid
  simp only [← started.traceRun_runtimeInputs, ← show preloaded = started.run program false afterStart from rfl] at mid
  let pins := alignmentPins policy highWidth
  let inputs := preloaded.runtimeInputs program false pins
  let trace := started.traceRun program false {} afterStart
  have final : traceRun program preloaded.core trace inputs = pretrace policy highWidth :=
    (preloaded.traceRun_runtimeInputs program false trace pins).symm
  have execution : StreamingReady.run program preloaded.core inputs = (aligned policy highWidth).core :=
    (preloaded.run_core program false pins).symm
  dsimp only at mid ⊢
  rw [← final, ← execution]
  exact ⟨traceRun_related program _ _ inputs mid.1 mid.2.2.1,
    traceRun_natural program _ _ inputs mid.2.1 mid.1 mid.2.2.1 mid.2.2.2,
    run_structural program _ inputs mid.2.2.1, run_progress program _ inputs mid.2.2.2⟩

private def checkHost (s : State 1) (inputs : List Input) : Bool :=
  inputs.all fun i =>
    !i.initialize && i.command == 0 &&
      (!i.txPush || (i.expectedGeneration == s.generation && i.expectedTransfer == s.transfer && i.txBits == 32))

private theorem checkHost_sound (s : State 1) (inputs : List Input) (good : checkHost s inputs = true) :
    ∀ i ∈ inputs, HostClock s.generation s.transfer i := by
  intro i member
  have facts := List.all_eq_true.mp good i member
  simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq, Bool.or_eq_true] at facts
  refine ⟨⟨facts.1.1, facts.1.2⟩, ?_⟩
  intro push
  rcases facts.2 with falsePush | h
  · simp [push] at falsePush
  · exact ⟨h.1.1, h.1.2, h.2⟩

private def checkPhy (width : Nat → Fin 2) (cells : List CellInputs) : Bool :=
  cells.zipIdx.all fun (cell, k) =>
    (List.finRange 6).all fun tick =>
      (cell.inputs[tick.val]?.getD {}).rawInputs[0] == phyLevel width (6 * k + tick.val)

private theorem checkPhy_sound (width : Nat → Fin 2) (cells : List CellInputs) (good : checkPhy width cells = true) :
    PhyClock width cells := by
  intro k tick
  have atCell : (cells[k.val], k.val) ∈ cells.zipIdx := by
    apply List.mem_iff_getElem.mpr
    exact ⟨k.val, by simp, by simp [List.getElem_zipIdx]⟩
  simpa using List.all_eq_true.mp (List.all_eq_true.mp good _ atCell) tick (by simp)

private def widths (highWidth : Nat) : Nat → Fin 2 := fun _ => if highWidth = 2 then 1 else 0

private def checked (highWidth : Nat) : Bool :=
  match groups onDeadline highWidth with
  | none => false
  | some (cells, finish) =>
    let s := (aligned onDeadline highWidth).core
    let trace := pretrace onDeadline highWidth
    let inputs := blocks cells
    (s.phase == .boundary && s.current == streamRow && s.pc == 4 &&
      s.remaining.toNat == cells.length && s.pins == txPins false) &&
    (s.txConsumed == 0 && cells.length == frameBits.length && frameBits.length == 576) &&
    (trace.txQueued.all fun word => word.validBits == 32) &&
    (checkHost s inputs && checkPhy (widths highWidth) cells &&
      decide (RefillPlan trace.accepted.length s.txConsumed.toNat cells)) &&
    (trace.accepted ++ offers inputs == frameBits && decide (frameBits.length ≤ s.total.toNat)) &&
    (!finish.initialize && finish.command == 0 && !finish.txPush)

private theorem body_exact (highWidth : Nat) (ok : checked highWidth = true) :
    let s := aligned onDeadline highWidth
    let pins := framePins onDeadline highWidth
    (s.run program false pins).core.phase = .completed ∧
      pinTrace program s.core (s.runtimeInputs program false pins) = frameBits.flatMap cellPins ++ [txPins false, idlePins] ∧
      (s.traceRun program false (pretrace onDeadline highWidth) pins).consumed = frameBits := by
  cases eq : groups onDeadline highWidth with
  | none => simp [checked, eq] at ok
  | some parts =>
    obtain ⟨chunks, finish⟩ := parts
    simp only [checked, eq, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', decide_eq_true_eq, List.all_eq_true] at ok
    obtain ⟨⟨⟨⟨⟨boundary, size⟩, full⟩, hosts⟩, payload⟩, terminal⟩ := ok
    let s := (aligned onDeadline highWidth).core
    let trace := pretrace onDeadline highWidth
    obtain ⟨related, counts, structural, progress⟩ := pretrace_related onDeadline highWidth
    have author : WordTrace s trace :=
      ⟨related, counts, structural, progress, by simp [s, boundary.1.1.1.1, Phase.busy], full⟩
    have atBoundary : Boundary s chunks.length :=
      ⟨boundary.1.1.1.1, boundary.1.1.1.2, boundary.1.1.2, boundary.1.2, by omega, boundary.2⟩
    have exactWire := frame_from_offers s chunks finish trace frameBits (widths highWidth) atBoundary author
      size.1.1 size.1.2.symm (checkPhy_sound _ _ hosts.1.2) (checkHost_sound s _ hosts.1.1)
      hosts.2 payload.1 payload.2 ⟨terminal.1.1, terminal.1.2⟩ terminal.2
    have inputEq := StreamingEthernetCredit.splitCells_sound _ chunks finish eq
    dsimp only
    rw [Session.State.run_core, Session.State.traceRun_runtimeInputs, inputEq]
    exact exactWire

/-- The finite offer and clock checks certify exact source pins and all
576 TX bits without inspecting the source model's reservation credit. -/
example (highWidth : Nat) (ok : checked highWidth = true) :
    let start := aligned onDeadline highWidth
    let active := framePins onDeadline highWidth
    (start.run program false active).core.phase = .completed ∧
      pinTrace program start.core (start.runtimeInputs program false active) =
        frameBits.flatMap cellPins ++ [txPins false, idlePins] ∧
      (start.traceRun program false (pretrace onDeadline highWidth) active).consumed = frameBits :=
  body_exact highWidth ok

/-- The previous burst's second word has moved into the shifter before
the first push. Both new words are visible by the next burst's first cut. -/
example (policy : Policy) (round : Fin 8) (delay : policy round ≤ 173) :
    reservationCut (64 * round.val + 32) < StreamingEthernetRefill.launch policy round + 91 ∧
    StreamingEthernetRefill.launch policy round + 93 ≤ reservationCut (64 * (round.val + 1)) := by
  simp [reservationCut, StreamingEthernetRefill.launch, refillStart, firstSample]
  omega

def verify : IO Unit := do
  for highWidth in [1, 2] do
    unless checked highWidth do
      throw (IO.userError s!"Ethernet service or clock obligations changed at width {highWidth}")
    let start := aligned onDeadline highWidth
    let pins := framePins onDeadline highWidth
    let trace := pretrace onDeadline highWidth
    unless (start.run program false pins).core.phase == .completed &&
      pinTrace program start.core (start.runtimeInputs program false pins) ==
        frameBits.flatMap cellPins ++ [txPins false, idlePins] &&
      (start.traceRun program false trace pins).consumed == frameBits do
      throw (IO.userError s!"Ethernet exact source frame changed at width {highWidth}")
  unless StreamingEthernetRefill.firstReservationMiss pastDeadline 1 == .ok (some 64) do
    throw (IO.userError "Ethernet same-edge offer unexpectedly supplied bit-64 credit")
  IO.println "Verified jittered Ethernet offers at two PHY widths and exact same-edge reservation miss"

end StreamingReadyEthernetDeadline

def main : IO Unit := StreamingReadyEthernetDeadline.verify
