import Pinwheel.Program.StreamingEthernetCoreFrame
import Pinwheel.Program.StreamingReadyCustodySession

/-! A host-policy-independent check of the inputs to the timed Ethernet core
theorem. The checker consumes the real session's runtime commands starting at
the first reservation and ending on the HALT edge. -/
namespace Pinwheel.Program.StreamingEthernetCredit
open StreamingReady StreamingEthernetCore

private def splitCells : List Input → Option (List CellInputs × Input)
  | [finish] => some ([], finish)
  | reserve :: low :: sample :: poll :: ready :: high :: rest =>
    (splitCells rest).map fun (cells, finish) => (⟨reserve, low, sample, poll, ready, high⟩ :: cells, finish)
  | _ => none

private theorem splitCells_sound (inputs : List Input) (cells : List CellInputs) (finish : Input)
    (split : splitCells inputs = some (cells, finish)) : inputs = blocks cells ++ [finish] := by
  fun_induction splitCells inputs generalizing cells finish
  case case1 last =>
    cases Option.some.inj split
    rfl
  case case2 reserve low sample poll ready high rest ih =>
    cases parsed : splitCells rest with
    | none => simp [parsed] at split
    | some value =>
      obtain ⟨tail, last⟩ := value
      have suffix := ih tail last parsed
      simp only [parsed, Option.map_some] at split
      cases Option.some.inj split
      simp [blocks, CellInputs.inputs, suffix]
  case case3 => contradiction

private def checkRuntime (i : Input) : Bool := decide (i.initialize = false ∧ i.command ≠ 15)

private def checkTimed (cell : CellInputs) : Bool :=
  cell.inputs.all checkRuntime &&
    !cell.reserve.rawInputs[0] && !cell.low.rawInputs[0] && cell.sample.rawInputs[0]

private theorem checkTimed_sound (cell : CellInputs) (good : checkTimed cell = true) : cell.Timed := by
  simp only [checkTimed, Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true, checkRuntime,
    decide_eq_true_eq] at good
  exact ⟨good.1.1.1, good.1.1.2, good.1.2, good.2⟩

private def checkReady (s : State a) : List CellInputs → Bool
  | [] => true
  | cell :: rest => checkTimed cell && s.canReserve && checkReady (run program s cell.inputs) rest

private theorem checkReady_sound (s : State a) (cells : List CellInputs)
    (good : checkReady s cells = true) : ReadySchedule s cells := by
  induction cells generalizing s with
  | nil => trivial
  | cons cell rest ih =>
    simp only [checkReady, Bool.and_eq_true] at good
    exact ⟨checkTimed_sound cell good.1.1, good.1.2, ih _ good.2⟩

private def checkBoundary (s : State a) (n : Nat) : Bool :=
  decide (s.phase = .boundary ∧ s.current = streamRow ∧ s.pc = 4 ∧
    s.remaining.toNat = n ∧ 0 < n ∧ s.pins = txPins false)

private theorem checkBoundary_sound (s : State a) (n : Nat) (good : checkBoundary s n = true) :
    Boundary s n := by
  obtain ⟨phase, row, pc, remaining, positive, pins⟩ := of_decide_eq_true good
  exact ⟨phase, row, pc, remaining, positive, pins⟩

private def checkCore (s : State a) (inputs : List Input) (expected : List Bool) : Bool :=
  match splitCells inputs with
  | none => false
  | some (cells, finish) =>
    checkBoundary s cells.length && checkReady s cells && checkRuntime finish &&
      ((traceRun program s {} inputs).consumed == expected)

/-- Check clock alignment, reservation credit, and the data consumed by the
engine. The checker uses no public-pad output or observed timing result. -/
def check (s : Session.State a) (pins : List Session.Pins) (expected : List Bool) : Bool :=
  checkCore s.core (s.runtimeInputs program false pins) expected

private theorem checkCore_sound (s : State a) (inputs : List Input) (expected : List Bool)
    (good : checkCore s inputs expected = true) :
    (run program s inputs).phase = .completed ∧
      pinTrace program s inputs = expected.flatMap cellPins ++ [txPins false, idlePins] ∧
      (traceRun program s {} inputs).consumed = expected := by
  cases split : splitCells inputs with
  | none => simp [checkCore, split] at good
  | some parts =>
    obtain ⟨cells, finish⟩ := parts
    simp only [checkCore, split, Bool.and_eq_true, checkRuntime, decide_eq_true_eq, beq_iff_eq] at good
    have grouped := splitCells_sound inputs cells finish split
    have framed := frame_exact s cells finish {} (checkBoundary_sound s cells.length good.1.1.1)
      (checkReady_sound s cells good.1.1.2) good.1.2
    obtain ⟨completed, sent, _, pads, consumed⟩ := framed
    rw [← grouped] at completed pads consumed
    have sentEq : sent = expected := consumed.symm.trans good.2
    exact ⟨completed, sentEq ▸ pads, good.2⟩

/-- The same wire and consumption theorem applies to every host scheduling
policy whose post-alignment runtime commands pass the credit check. -/
theorem session_frame_exact (s : Session.State a) (pins : List Session.Pins) (expected : List Bool)
    (good : check s pins expected = true) :
    (s.run program false pins).core.phase = .completed ∧
      pinTrace program s.core (s.runtimeInputs program false pins) =
        expected.flatMap cellPins ++ [txPins false, idlePins] ∧
      (s.traceRun program false {} pins).consumed = expected := by
  rw [s.run_core, s.traceRun_runtimeInputs]
  exact checkCore_sound s.core _ expected good

end Pinwheel.Program.StreamingEthernetCredit
