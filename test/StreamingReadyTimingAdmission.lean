import Pinwheel.Hardware.StreamingReady.SegmentTimingContract

/-! The environment supplies one flat list of ordinary raw pin clocks. A
    ready last aperture continues to HALT; moving the same raw transition
    one clock later expires the wait on either instruction store. -/
namespace Pinwheel.Test.StreamingReadyTimingAdmission

open Pinwheel.Hardware Pinwheel.Hardware.StreamingReady
open SegmentAdmission SegmentCore SegmentPathControl SegmentTiming SegmentTransaction
open Pinwheel.Program.StreamingReady (Instruction)
open Pinwheel.Program.StreamingReadySegments

private def pins : Pinwheel.Program.StreamingReady.Pins := ⟨0, 1⟩
private def guard : Pinwheel.Program.StreamingReady.Guard := ⟨1, 1, .misses 0⟩
private def rows : List Row := [.cell (.driveWait pins guard), .cell .halt]

private def image : Image rows 0 := ⟨[⟨.complete, 0, 0, 3⟩], by decide +kernel⟩

private def installedState : Values (Register 1)
  | _, .base .valid => 1
  | _, .base .count => 2
  | _, .base (.word k) => (rows[k.toNat]?.map Row.encode).getD 0
  | _, .fetched => (rows[0]?.map Row.encode).getD 0
  | _, _ => 0

private theorem installed : Installed rows installedState := by
  refine ⟨by decide, rfl, rfl, ?_⟩
  intro atIndex
  have small : atIndex.val < 64 := Nat.lt_trans atIndex.isLt (by decide)
  simp [installedState, BitVec.toNat_ofNat, Nat.mod_eq_of_lt small]

private def clock (command : BitVec 4) (raw : Bool) : Values StreamingReady.Core.Input
  | _, .command => command
  | _, .rawInputs => BitVec.ofNat 2 raw.toNat
  | _, _ => 0

private def start (timely : Bool) : Values StreamingReady.Core.Input := clock 3 timely

private def clocks (timely : Bool) : List (Values StreamingReady.Core.Input) :=
  [clock 0 (!timely), clock 0 false, clock 0 false]

private def started (registered timely : Bool) : Values (Register 1) :=
  (circuit 1 registered).step (start timely) installedState

private theorem admits_start (timely : Bool) :
    StreamingReady.Core.starting.eval (start timely) (project installedState) = 1#1 := by
  cases timely <;> decide +kernel

private theorem clock_clean (timely : Bool) (i : Values StreamingReady.Core.Input)
    (member : @i ∈ clocks timely) : ProtocolOwnership.DrainInput i := by
  simp [clocks] at member
  rcases member with rfl | rfl <;> exact ⟨rfl, rfl, rfl⟩

private theorem fetch_bounds (registered timely : Bool) (k : Fin 4) :
    let state : Values (Register 1) := run registered (started registered timely) ((clocks timely).take k.val)
    state (.base .phase) = 1#3 →
      k.val < 3 ∧ (state (.base .pc) = 0#7 → k.val = 0) := by
  cases registered <;> cases timely <;> decide +revert +kernel

private theorem finish_phase (registered timely : Bool) (k : Fin 4) :
    let phase := run registered (started registered timely) ((clocks timely).take k.val) (.base .phase)
    phase = 5#3 ∨ phase = 6#3 → phase = (if timely then 5#3 else 6#3) := by
  cases registered <;> cases timely <;> decide +revert +kernel

private theorem take_elapsed (partition : trace = elapsed ++ remainder) :
    List.take elapsed.length trace = elapsed := by
  rw [partition, List.take_left' rfl]

private theorem timing (registered timely : Bool) :
    SegmentTimingContract.Timing registered rows (started registered timely) (clocks timely) 0 := by
  constructor
  · intro i member
    have clean := clock_clean timely i member
    exact ⟨clean.1, by simp [clean.2.1]⟩
  · intro elapsed remaining partition phase
    have lengths := congrArg List.length partition
    simp only [clocks, List.length_cons, List.length_nil, List.length_append] at lengths
    let index : Fin 4 := ⟨elapsed.length, by omega⟩
    have atFetch := fetch_bounds registered timely index
    dsimp only [index] at atFetch
    rw [take_elapsed partition] at atFetch
    have earlier : elapsed.length < 3 := (atFetch phase).1
    cases remaining with
    | nil => simp at lengths; omega
    | cons head tail =>
      have clean := clock_clean timely head (by rw [partition]; simp)
      exact ⟨head, tail, rfl, clean⟩
  · intro elapsed remaining pc instruction partition phase position row
    have inBounds := (List.getElem?_eq_some_iff.mp row).1
    have atRow : pc = 0 ∨ pc = 1 := by
      change pc < 2 at inBounds
      omega
    rcases atRow with first | second
    · have exactRow : Instruction.driveWait pins guard = instruction := by simpa [rows, first] using row
      subst instruction
      have lengths := congrArg List.length partition
      simp only [clocks, List.length_cons, List.length_nil, List.length_append] at lengths
      let index : Fin 4 := ⟨elapsed.length, by omega⟩
      have atFetch := fetch_bounds registered timely index
      dsimp only [index] at atFetch
      rw [take_elapsed partition] at atFetch
      have physical : (run registered (started registered timely) elapsed (.base .pc)).toNat = 0 :=
        position.trans first
      have atStart : elapsed.length = 0 := (atFetch phase).2 (BitVec.eq_of_toNat_eq physical)
      intro n limit
      have zero : n = 0 := by simpa [guard] using limit.symm
      refine ⟨by rw [zero]; change 2 ≤ remaining.length; omega, ?_⟩
      intro i member
      apply clock_clean timely i
      rw [partition]
      exact List.mem_append_right _ (List.mem_of_mem_take member)
    · have halt : Instruction.halt = instruction := by simpa [rows, second] using row
      subst instruction
      trivial

example (registered timely : Bool) :
    ∃ (active : List (Values StreamingReady.Core.Input)) (last : Values StreamingReady.Core.Input)
      (rest : List (Values StreamingReady.Core.Input)) (ending : Terminal),
      clocks timely = active ++ @last :: rest ∧
      Admitted image registered installedState (start timely) active last ending ∧
      run registered (started registered timely) (active ++ [@last]) (.base .phase) =
        (if timely then 5#3 else 6#3) := by
  have supported : SegmentTimingImages.SupportedRows rows := by decide +kernel
  obtain ⟨active, last, rest, ending, partition, accepted⟩ := SegmentTimingContract.from_start
    image supported registered installedState (start timely) (clocks timely) 0 installed (admits_start timely)
      (timing registered timely)
  refine ⟨active, last, rest, ending, partition, accepted, ?_⟩
  have lengths := congrArg List.length partition
  simp only [clocks, List.length_cons, List.length_nil, List.length_append] at lengths
  let index : Fin 4 := ⟨(active ++ [@last]).length, by simp; omega⟩
  have phase := finish_phase registered timely index
  dsimp only [index] at phase
  have cut : clocks timely = (active ++ [@last]) ++ rest := by
    simpa only [List.append_assoc, List.singleton_append] using partition
  rw [take_elapsed cut] at phase
  apply phase
  rw [SegmentTiming.run_append]
  let state : Values (Register 1) := (circuit 1 registered).step last (run registered (started registered timely) active)
  change state (.base .phase) = 5#3 ∨ state (.base .phase) = 6#3
  have actual : state (.base .phase) = phaseOf ending := accepted.terminal.1
  rw [actual]
  cases ending with
  | planned result => cases exit : result.exit <;> simp [phaseOf, terminalPhase, exit]
  | timeout => simp [phaseOf]

end Pinwheel.Test.StreamingReadyTimingAdmission
