import Pinwheel.Program.StreamingReadySegments

/-! Observable execution of checked segment rows. Service observations are
    pre-edge samples from the second sampler stage. The TX list supplies the
    logical transaction data, while each cell's parking count records the
    delay before credit allowed its reservation. -/
namespace Pinwheel.Program.StreamingReadySegments.Execution

open StreamingReady (Cell Guard Pins)

inductive Observation where
  | wait (samples : List (BitVec 2))
  | cell (parked : Nat) (samples : List (BitVec 2))
  deriving DecidableEq, Repr

inductive Event where
  | fetch (pc : Nat)
  | drive (pins : Pins)
  | dwell (clocks : Nat)
  | park (clocks : Nat)
  | reserve (bit : Bool)
  | poll (sample : BitVec 2)
  | capture (bit : Bool)
  | branch (sample taken : Bool)
  deriving DecidableEq, Repr

inductive Terminal where
  | planned (outcome : PathEnd)
  | timeout (pc slot : Nat)
  deriving DecidableEq, Repr

structure Result where
  terminal : Terminal
  events : List Event
  remainingTX : List Bool
  remainingObservations : List Observation
  deriving DecidableEq, Repr

def Result.rxBits (result : Result) : List Bool :=
  result.events.filterMap fun event => match event with
  | .capture bit => some bit
  | _ => none

def Result.txBits (result : Result) : List Bool :=
  result.events.filterMap fun event => match event with
  | .reserve bit => some bit
  | _ => none

def Result.fetchPCs (result : Result) : List Nat :=
  result.events.filterMap fun event => match event with
  | .fetch pc => some pc
  | _ => none

def Result.branches (result : Result) : List (Bool × Bool) :=
  result.events.filterMap fun event => match event with
  | .branch sample taken => some (sample, taken)
  | _ => none

/-- A guard window ends at the first qualified sample or at the final
    missed poll of a bounded guard. An unbounded guard can only qualify.
    Insufficient, surplus and post-qualification samples are rejected. -/
def pollWindow (guard : Guard) (samples : List (BitVec 2)) : Option (Option (BitVec 2)) := do
  let last ← samples.getLast?
  if samples.dropLast.any guard.matches then none else
    match guard.limit with
    | .unbounded => if guard.matches last then some (some last) else none
    | .misses misses =>
      let budget := misses.val + 1
      if samples.length > budget then none
      else if guard.matches last then some (some last)
      else if samples.length == budget then some none else none

/-- After a prefix of misses, the next qualified poll succeeds even at the
    last eligible cut. A miss settles only at the end of the aperture. -/
theorem pollWindow_after_misses (guard : Guard) (limit : Fin 255)
    (bounded : guard.limit = .misses limit) (prior : List (BitVec 2)) (last : BitVec 2)
    (misses : prior.any guard.matches = false) (within : prior.length ≤ limit.val) :
    pollWindow guard (prior ++ [last]) =
      if guard.matches last then some (some last)
      else if prior.length == limit.val then some none else none := by
  simp [pollWindow, bounded, misses, Nat.not_lt_of_ge within]
  done

theorem pollWindow_unbounded (guard : Guard) (unbounded : guard.limit = .unbounded)
    (prior : List (BitVec 2)) (last : BitVec 2) (misses : prior.any guard.matches = false) :
    pollWindow guard (prior ++ [last]) = if guard.matches last then some (some last) else none := by
  simp [pollWindow, unbounded, misses]

structure Machine where
  tx : List Bool
  observations : List Observation
  capture : Option Bool := none
  eventsRev : List Event := []

def Machine.emit (s : Machine) (event : Event) : Machine :=
  {s with eventsRev := event :: s.eventsRev}

def Machine.poll (s : Machine) (samples : List (BitVec 2)) : Machine :=
  samples.foldl (fun state sample => state.emit (.poll sample)) s

private def Machine.finish (s : Machine) (idle : Pins) (endAt : Terminal) : Result :=
  ⟨endAt, (s.emit (.drive idle)).eventsRev.reverse, s.tx, s.observations⟩

inductive RowEffect where
  | advance (state : Machine)
  | expired (slot : Nat) (state : Machine)

def reserve (s : Machine) (cell : Cell) : Option (Machine × Bool) :=
  if cell.transmit then
    match s.tx with
    | bit :: rest => some (({s with tx := rest} : Machine).emit (.reserve bit), bit)
    | [] => none
  else some (s, false)

def runCells (cell : Cell) (guard : Option Guard) (slot : Nat) :
    Nat → Machine → Option RowEffect
  | 0, s => some (.advance s)
  | remaining + 1, s => do
    let .cell parked samples :: rest := s.observations | none
    let last := remaining == 0
    let s : Machine := {s with observations := rest}
    let s := if parked == 0 then s else s.emit (.park parked)
    let (s, bit) ← reserve s cell
    let s := ((s.emit (.drive (cell.dataPins false last bit))).emit (.dwell (cell.lowDuration.val + 1)))
      |>.emit (.drive (cell.dataPins true last bit))
    let matched ← match guard with
      | none => match samples with
        | [sample] => some (some sample)
        | _ => none
      | some g => pollWindow g samples
    let s := if guard.isSome then s.poll samples else s
    match matched with
    | none => some (.expired slot s)
    | some sample =>
      let s := if cell.receive then
        let value := sample[cell.rxInput.val]
        ({s with capture := some value} : Machine).emit (.capture value)
        else s
      let s := (s.emit (.dwell (cell.highDuration.val + 1))).emit (.drive (cell.basePins false last))
      runCells cell guard (slot + 1) remaining s

private def perform (row : Row) (cursor : Cursor) (s : Machine) : Option RowEffect :=
  match row with
  | .count _ => some (.advance {s with capture := none})
  | .cell (.stream cell guard) => do
    let slots ← cursor.slots
    runCells cell guard 0 slots (s.emit (.drive (cell.basePins false (slots == 1))))
  | .cell (.pulse cell) =>
    let s := (s.emit (.drive cell.lowPins)).emit (.dwell (cell.lowDuration.val + 1))
    let s := (s.emit (.drive cell.highPins)).emit (.dwell (cell.highDuration.val + 1))
    some (.advance (s.emit (.drive cell.lowPins)))
  | .cell (.driveWait pins guard) => do
    let .wait samples :: rest := s.observations | none
    let matched ← pollWindow guard samples
    let s := (({s with observations := rest} : Machine).emit (.drive pins)).poll samples
    some (if matched.isSome then .advance s else .expired 0 s)
  | _ => some (.advance s)

private def execute (rows : List Row) (budget : Nat) (idle : Pins) :
    Nat → Cursor → Machine → Option Result
  | 0, _, _ => none
  | fuel + 1, cursor, machine => do
    let checked ← successors rows budget cursor
    let row ← rows[cursor.pc]?
    let effect ← perform row cursor (machine.emit (.fetch cursor.pc))
    match effect with
    | .expired slot after => some (after.finish idle (.timeout cursor.pc slot))
    | .advance after =>
      match checked with
      | .finish outcome => some (after.finish idle (.planned outcome))
      | .next next => execute rows budget idle fuel next after
      | .both no yes => do
        let .branch _ onBit := row | none
        let capture ← after.capture
        let taken := capture == onBit
        let following := if taken then yes else no
        let after : Machine := {after with capture := none}
        execute rows budget idle fuel following (after.emit (.branch capture taken))

def run (rows : List Row) (txBudget : Nat) (tx : List Bool) (observations : List Observation)
    (idle : Pins := {}) : Option Result :=
  if tx.length == txBudget then
    execute rows txBudget idle rows.length {} ⟨tx, observations, none, []⟩
  else none

private theorem execute_reaches (rows : List Row) (budget : Nat) (idle : Pins)
    (fuel : Nat) (cursor : Cursor) (machine : Machine) (result : Result) (outcome : PathEnd)
    (ran : execute rows budget idle fuel cursor machine = some result)
    (planned : result.terminal = .planned outcome) : Reaches rows budget cursor outcome := by
  induction fuel generalizing cursor machine with
  | zero => simp [execute] at ran
  | succ fuel ih =>
    cases checked : successors rows budget cursor with
    | none => simp [execute, checked] at ran
    | some next =>
      cases loaded : rows[cursor.pc]? with
      | none => simp [execute, checked, loaded] at ran
      | some row =>
        cases effect : perform row cursor (machine.emit (.fetch cursor.pc)) with
        | none => simp [execute, checked, loaded, effect] at ran
        | some step =>
          cases step with
          | expired slot after =>
            simp [execute, checked, loaded, effect] at ran
            simp [← ran, Machine.finish] at planned
          | advance after =>
            cases next with
            | finish endAt =>
              simp [execute, checked, loaded, effect] at ran
              have same : endAt = outcome := by simpa [← ran, Machine.finish] using planned
              exact .finish (same ▸ checked)
            | next following =>
              exact .next checked (ih _ _ (by simpa [execute, checked, loaded, effect] using ran))
            | both no yes =>
              cases row <;> simp [execute, checked, loaded, effect] at ran
              rename_i target onBit
              cases capture : after.capture with
              | none => simp [capture] at ran
              | some bit =>
                exact .branch checked (bit == onBit) (ih _ _ (by simpa [capture] using ran))

/-- The executable completed/discard/explicit-fault paths refine the existing
    structural certificate. A guard timeout can interrupt a planned path. -/
theorem run_covers (image : Image rows budget) (ran : run rows budget tx observations idle = some result)
    (planned : result.terminal = .planned outcome) : outcome ∈ image.outcomes := by
  apply image.covers
  unfold run at ran
  split at ran
  · exact execute_reaches _ _ _ _ _ _ _ _ ran planned
  · simp at ran

end Pinwheel.Program.StreamingReadySegments.Execution
