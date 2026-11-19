import Pinwheel.Program.StreamingReadyCompile
import Pinwheel.I2C.RegisterRead

/-! Checked forward control flow over the existing Ready cells. Each stream
    consumes its own count, and each branch consumes a qualified capture. -/
namespace Pinwheel.Program.StreamingReadySegments

open StreamingReady (I2cProfile)

inductive Row where
  | cell (instruction : StreamingReady.Instruction)
  | count (slots : BitVec 16)
  | branch (target : BitVec 6) (onBit : Bool)
  | discard
  deriving DecidableEq, Repr

def Row.encode : Row → BitVec 64
  | .cell instruction => StreamingReady.encode instruction
  | .count slots => (0#45) ++ slots ++ (5#3)
  | .branch target onBit => (0#54) ++ BitVec.ofBool onBit ++ target ++ (6#3)
  | .discard => 7

theorem Row.count_fields (slots : BitVec 16) :
    (Row.count slots).encode.extractLsb' 0 3 = 5 ∧
    (Row.count slots).encode.extractLsb' 3 16 = slots ∧
    (Row.count slots).encode.extractLsb' 19 45 = 0 := by
  refine ⟨?_, ?_, ?_⟩
  all_goals unfold Row.encode
  all_goals repeat first
    | rw [BitVec.extractLsb'_append_eq_of_le (by decide)]
    | rw [BitVec.extractLsb'_append_eq_of_add_le (by decide)]
  all_goals simp
  done

theorem Row.branch_fields (target : BitVec 6) (onBit : Bool) :
    (Row.branch target onBit).encode.extractLsb' 0 3 = 6 ∧
    (Row.branch target onBit).encode.extractLsb' 3 6 = target ∧
    (Row.branch target onBit).encode.extractLsb' 9 1 = BitVec.ofBool onBit ∧
    (Row.branch target onBit).encode.extractLsb' 10 54 = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals unfold Row.encode
  all_goals repeat first
    | rw [BitVec.extractLsb'_append_eq_of_le (by decide)]
    | rw [BitVec.extractLsb'_append_eq_of_add_le (by decide)]
  all_goals simp
  done

inductive Exit where
  | complete | discard | fault
  deriving DecidableEq, Repr

structure Cursor where
  pc : Nat := 0
  slots : Option Nat := none
  capture : Bool := false
  tx : Nat := 0
  rx : Nat := 0
  coreClocks : Nat := 0
  deriving DecidableEq, Repr

structure PathEnd where
  exit : Exit
  tx : Nat
  rx : Nat
  coreClocks : Nat
  deriving DecidableEq, Repr

inductive Successors where
  | finish (result : PathEnd)
  | next (cursor : Cursor)
  | both (fallthrough taken : Cursor)

private def boundedWait : StreamingReady.WaitLimit → Option Nat
  | .unbounded => none
  | .misses n => some (n.val + 1)

private def guardClocks : Option StreamingReady.Guard → Option Nat
  | none => some 0
  | some guard => boundedWait guard.limit

private def cellClocks (cell : StreamingReady.Cell) : Nat :=
  1 + (cell.lowDuration.val + 1) + (cell.highDuration.val + 1)

private def Cursor.next (cursor : Cursor) (clocks : Nat) : Cursor :=
  {cursor with pc := cursor.pc + 1, coreClocks := cursor.coreClocks + clocks}

private def Cursor.finish (cursor : Cursor) (exit : Exit) : Successors :=
  .finish ⟨exit, cursor.tx, cursor.rx, cursor.coreClocks + 1⟩

/-- Successful instruction boundaries under timely guard responses and
    immediate queue credit. `coreClocks` includes each worst-case guard poll
    window. Waiting for host credit is accounted for separately at runtime. -/
def successors (rows : List Row) (txBudget : Nat) (cursor : Cursor) : Option Successors := do
  let row ← rows[cursor.pc]?
  match row with
  | .count slots =>
    if cursor.slots.isNone && slots != 0 then
      some (.next {(cursor.next 1) with slots := some slots.toNat, capture := false})
    else none
  | .branch target _ =>
    if cursor.slots.isNone && cursor.capture && cursor.pc + 1 < rows.length &&
        cursor.pc < target.toNat && target.toNat < rows.length then
      let next := {(cursor.next 1) with capture := false}
      some (.both next {next with pc := target.toNat})
    else none
  | .discard => if cursor.slots.isNone && cursor.tx ≤ txBudget then some (cursor.finish .discard) else none
  | .cell instruction =>
    if ¬ instruction.Canonical then none else
    match instruction with
    | .halt => if cursor.slots.isNone && cursor.tx == txBudget then some (cursor.finish .complete) else none
    | .fault => if cursor.slots.isNone then some (cursor.finish .fault) else none
    | .pulse cell => if cursor.slots.isNone then some (.next (cursor.next (1 + cellClocks cell))) else none
    | .driveWait _ guard => do
      let clocks ← boundedWait guard.limit
      if cursor.slots.isNone then some (.next (cursor.next (1 + clocks))) else none
    | .stream cell guard => do
      let slots ← cursor.slots
      let polls ← guardClocks guard
      let tx := cursor.tx + if cell.transmit then slots else 0
      let rx := cursor.rx + if cell.receive then slots else 0
      if 0 < slots && tx ≤ txBudget && rx < 65536 && cell.txOutput.val < 3 then
        some (.next {(cursor.next (1 + slots * (cellClocks cell + polls))) with
          slots := none, capture := cell.receive, tx, rx})
      else none

def paths (rows : List Row) (txBudget : Nat) : Nat → Cursor → Option (List PathEnd)
  | 0, _ => none
  | fuel + 1, cursor => do
    match ← successors rows txBudget cursor with
    | .finish result => some [result]
    | .next next => paths rows txBudget fuel next
    | .both fallthrough taken => do
      let first ← paths rows txBudget fuel fallthrough
      let second ← paths rows txBudget fuel taken
      some (first ++ second)

/-- A path through the abstract instruction boundaries. Each stream here
    reached its final cell, and both outcomes of each qualified branch are included. -/
inductive Reaches (rows : List Row) (txBudget : Nat) : Cursor → PathEnd → Prop where
  | finish (entry : successors rows txBudget cursor = some (.finish result)) :
      Reaches rows txBudget cursor result
  | next (entry : successors rows txBudget cursor = some (.next following))
      (suffix : Reaches rows txBudget following result) : Reaches rows txBudget cursor result
  | branch (entry : successors rows txBudget cursor = some (.both fallthrough taken)) (bit : Bool)
      (suffix : Reaches rows txBudget (if bit then taken else fallthrough) result) :
      Reaches rows txBudget cursor result

private theorem paths_cover (checked : paths rows txBudget fuel cursor = some outcomes)
    (reached : Reaches rows txBudget cursor result) : result ∈ outcomes := by
  induction fuel generalizing cursor outcomes with
  | zero => simp [paths] at checked
  | succ fuel ih =>
    cases reached with
    | finish entry =>
      have equal : outcomes = [result] := by simpa [paths, entry] using checked.symm
      simp [equal]
    | next entry suffix => exact ih (by simpa [paths, entry] using checked) suffix
    | @branch cursor fallthrough taken result entry bit suffix =>
      have eitherPath : (paths rows txBudget fuel fallthrough).bind (fun no =>
          (paths rows txBudget fuel taken).bind fun yes => some (no ++ yes)) = some outcomes := by
        simpa [paths, entry] using checked
      obtain ⟨no, noPath, remaining⟩ := Option.bind_eq_some_iff.mp eitherPath
      obtain ⟨yes, yesPath, equal⟩ := Option.bind_eq_some_iff.mp remaining
      have outcomesEq := Option.some.inj equal
      subst outcomes
      cases bit
      · exact List.mem_append_left _ (ih noPath suffix)
      · exact List.mem_append_right _ (ih yesPath suffix)
  done

/-- Each reachable instruction must satisfy the local obligations and each
    choice must terminate within the physical row bound. -/
def check (rows : List Row) (txBudget : Nat) : Option (List PathEnd) :=
  if 0 < rows.length && rows.length ≤ 64 && txBudget < 65536 then paths rows txBudget rows.length {} else none

structure Image (rows : List Row) (txBudget : Nat) where
  outcomes : List PathEnd
  checked : check rows txBudget = some outcomes

theorem Image.covers (image : Image rows budget) (reached : Reaches rows budget {} result) :
    result ∈ image.outcomes := by
  have checked := image.checked
  unfold check at checked
  split at checked
  · exact paths_cover checked reached
  · contradiction
  done

def Image.words (_ : Image rows budget) : List (BitVec 64) := rows.map Row.encode

def Image.txBudget (_ : Image rows budget) : Nat := budget

def compile (rows : List Row) (txBudget : Nat) : Except String (Image rows txBudget) :=
  match h : check rows txBudget with
  | some outcomes => .ok ⟨outcomes, h⟩
  | none => .error "Invalid segment graph: inspect rows, count, capture, branch target, guard and TX/RX bounds"

def registerReadTX (request : I2C.RegisterRead.Request) : List Bool :=
  List.ofFn (I2C.RegisterRead.releaseData request)

private def i2cStream (profile : I2cProfile) : Row :=
  .cell (.stream (StreamingReady.i2cCell profile) (some (StreamingReady.i2cGuard profile 1 1)))

private def lowReleased (profile : I2cProfile) : Row :=
  .cell (.pulse {
    lowDuration := profile.lowDuration, highDuration := profile.highDuration,
    lowPins := ⟨0, 1⟩, highPins := ⟨0, 1⟩ })

private def stop (profile : I2cProfile) : List Row :=
  [.cell (StreamingReady.i2cStopLow profile),
   .cell (.driveWait ⟨0, 2⟩ (StreamingReady.i2cGuard profile 1 1)),
   .cell (StreamingReady.i2cHold profile 2)]

/-- Host-provided data is fixed before START. The captured ACK selects the
    forward STOP target, and a successful register write takes repeated START. -/
def registerReadRows (profile : I2cProfile) : List Row :=
  let start : List Row := [.cell (.driveWait ⟨0, 0⟩ (StreamingReady.i2cGuard profile 3 3)),
    .cell (StreamingReady.i2cHold profile 2)]
  let restart := lowReleased profile :: start
  let byte : List Row := [.count 9, i2cStream profile, .branch 20 true]
  start ++ byte ++ byte ++ restart ++ byte ++ [.count 9, i2cStream profile] ++
    stop profile ++ [.cell .halt] ++ stop profile ++ [.discard]

def registerReadCheck (profile : I2cProfile) : Option (List PathEnd) := check (registerReadRows profile) 36

set_option maxRecDepth 8192 in
def registerReadImage : Image (registerReadRows .standard) 36 where
  outcomes := [⟨.complete, 36, 36, 1598⟩, ⟨.discard, 27, 27, 1236⟩,
    ⟨.discard, 18, 18, 821⟩, ⟨.discard, 9, 9, 458⟩]
  checked := by decide +kernel

theorem registerRead_rows : registerReadImage.words.length = 24 := rfl

theorem registerReadTX_length (request : I2C.RegisterRead.Request) : (registerReadTX request).length = 36 := by
  simp [registerReadTX]

end Pinwheel.Program.StreamingReadySegments
