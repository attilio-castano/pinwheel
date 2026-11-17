import Pinwheel.Program.StreamingEthernetCore

namespace Pinwheel.Program.StreamingEthernetCore
open StreamingReady

def blocks (cells : List CellInputs) : List Input := cells.flatMap CellInputs.inputs

/-- Host service guarantees a queued or shifted bit at each reservation.
The clock waveform imposes the three necessary raw slot levels independently
of that queue state. -/
def ReadySchedule (s : State a) : List CellInputs → Prop
  | [] => True
  | cell :: rest => cell.Timed ∧ s.canReserve = true ∧ ReadySchedule (run program s cell.inputs) rest

def cellPins (bit : Bool) : List Pins := txPins false :: List.replicate 5 (txPins bit)

private theorem run_append (s : State a) (first rest : List Input) :
    run program s (first ++ rest) = run program (run program s first) rest := List.foldl_append

private theorem pins_append (s : State a) (first rest : List Input) :
    pinTrace program s (first ++ rest) = (pinTrace program s first).take first.length ++
      pinTrace program (run program s first) rest := by
  induction first generalizing s with
  | nil => rfl
  | cons i tail ih => simp [pinTrace, run, ih]

private theorem trace_append (s : State a) (trace : BitTrace) (first rest : List Input) :
    traceRun program s trace (first ++ rest) =
      traceRun program (run program s first) (traceRun program s trace first) rest := by
  induction first generalizing s trace with
  | nil => rfl
  | cons i tail ih => exact ih (step program i s) (trace.step s i)

/-- All cell bits on the wire equal the exact TX reservation trace. The
six-clock length of each cell and continuous TX_EN hold across word cuts. -/
theorem frame_exact (s : State a) (cells : List CellInputs) (finish : Input) (trace : BitTrace)
    (start : Boundary s cells.length) (schedule : ReadySchedule s cells) (terminal : finish.Runtime) :
    let inputs := blocks cells ++ [finish]
    (run program s inputs).phase = .completed ∧
    ∃ sent : List Bool, sent.length = cells.length ∧
      pinTrace program s inputs = sent.flatMap cellPins ++ [txPins false, idlePins] ∧
      (traceRun program s trace inputs).consumed = trace.consumed ++ sent := by
  induction cells generalizing s trace with
  | nil =>
    have impossible := start.positive
    simp at impossible
  | cons cell rest ih =>
    let next := run program s cell.inputs
    let bit := s.selectedTx.data[31]
    let prefixTrace := traceRun program s trace cell.inputs
    have block := cell_exact s _ cell trace start schedule.2.1 schedule.1
    change (if 1 < (cell :: rest).length then Boundary next ((cell :: rest).length - 1)
      else HaltReady next) ∧ _ at block
    have takePins : (pinTrace program s cell.inputs).take cell.inputs.length = cellPins bit := by
      rw [block.2.1]
      rfl
    have inputs : blocks (cell :: rest) ++ [finish] = cell.inputs ++ (blocks rest ++ [finish]) := by
      simp [blocks, List.append_assoc]
    dsimp only
    rw [inputs, run_append, pins_append, trace_append, takePins]
    cases rest with
    | nil =>
      have atHalt : HaltReady next := by simpa using block.1
      have event := halt_exact next finish prefixTrace atHalt terminal
      refine ⟨event.1, [bit], rfl, ?_, ?_⟩
      · change cellPins bit ++ [next.pins, (step program finish next).pins] = _
        rw [atHalt.pins, event.2.1]
        rfl
      · change (prefixTrace.step next finish).consumed = _
        rw [event.2.2, block.2.2]
    | cons first tail =>
      have atBoundary : Boundary next (first :: tail).length := by
        have more : 1 < (cell :: first :: tail).length := by simp
        have nextBoundary := block.1
        rw [if_pos more] at nextBoundary
        simpa only [List.length_cons, Nat.add_sub_cancel] using nextBoundary
      obtain ⟨completed, sent, size, tracePins, consumed⟩ :=
        ih next prefixTrace atBoundary schedule.2.2
      refine ⟨completed, bit :: sent, by simp [size], ?_, ?_⟩
      · rw [tracePins]
        simp [List.append_assoc]
      · rw [consumed, block.2.2, List.append_assoc]
        rfl

private theorem bit_pin (bit : Bool) (cut : Nat) (within : 1 ≤ cut ∧ cut ≤ 5) :
    (cellPins bit)[cut]? = some (txPins bit) := by
  have choices : cut = 1 ∨ cut = 2 ∨ cut = 3 ∨ cut = 4 ∨ cut = 5 := by omega
  rcases choices with rfl | rfl | rfl | rfl | rfl <;> rfl

/-- Cut 2 in each six-clock slot is the PHY edge. Cuts 1–5 use the same
bit and the same asserted enable, including between successive TX words. -/
theorem cell_pin_at (sent : List Bool) (tail : List Pins) (index cut : Nat)
    (inFrame : index < sent.length) (valid : 1 ≤ cut ∧ cut ≤ 5) :
    (sent.flatMap cellPins ++ tail)[6 * index + cut]? = some (txPins sent[index]) := by
  induction sent generalizing index with
  | nil => simp at inFrame
  | cons first rest ih =>
    cases index with
    | zero =>
      rw [List.flatMap_cons, List.append_assoc, Nat.mul_zero, Nat.zero_add, List.getElem?_append_left]
      · exact bit_pin first cut valid
      · simpa [cellPins] using (show cut < 6 by omega)
    | succ index =>
      have within : index < rest.length := by simpa using inFrame
      rw [List.flatMap_cons, List.append_assoc, List.getElem?_append_right]
      · change _ = some (txPins rest[index])
        rw [show (cellPins first).length = 6 by rfl,
          show 6 * (index + 1) + cut - 6 = 6 * index + cut by omega]
        exact ih index within
      · change 6 ≤ 6 * (index + 1) + cut
        omega

end Pinwheel.Program.StreamingEthernetCore
