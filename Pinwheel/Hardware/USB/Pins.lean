import Pinwheel.Hardware.USB.Transaction

namespace Pinwheel.Hardware.USB
open Pinwheel.Hardware Pinwheel.USBOnlineFeasibility
open Pinwheel.USBWaveformConstruction (ackSymbols ackClocks ack_clock_count padValue)

set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

private def levelsAt (index : BitVec 9) : List (Wire × Nat) → BitVec 3 :=
  List.foldr (fun (line, slot) later =>
    if index.toNat < (BitVec.ofNat 9 ((slot+1)*16)).toNat
    then BitVec.ofNat 3 (padValue line) else later) 0

private theorem ackLevels_eval (i : Values Input) (s : CoreState) :
    ackLevels.eval i s = levelsAt (304#9-s .timer) ackSymbols.zipIdx := by
  unfold ackLevels
  generalize ackSymbols.zipIdx = cells
  induction cells with
  | nil => rfl
  | cons c tail ih =>
    rcases c with ⟨line,slot⟩
    simp [levelsAt,List.foldr_cons,lt,Expr.eval,ih]
    split
    · rfl
    · simpa [levelsAt,lt] using ih

private theorem checked_ack_table :
    ((List.range 304).map (fun n => levelsAt (BitVec.ofNat 9 n) ackSymbols.zipIdx)) =
      ackClocks.map (fun line => BitVec.ofNat 3 (padValue line)) := by
  decide +kernel

private theorem finite_ack_table (index : Fin 304) :
    levelsAt (BitVec.ofNat 9 index.val) ackSymbols.zipIdx =
      BitVec.ofNat 3 (padValue (ackClocks[index.val]'(by rw [ack_clock_count]; exact index.isLt))) := by
  have lookup := congrArg (fun table : List (BitVec 3) => table[index.val]?) checked_ack_table
  have inside : index.val < ackClocks.length := by rw [ack_clock_count]; exact index.isLt
  simpa [List.getElem?_map,List.getElem?_range,index.isLt,List.getElem?_eq_getElem inside] using lookup

theorem ack_pins (i : Values Input) (s : CoreState) (sendingMode : s .mode = 5#3)
    (positive : 0 < (s .timer).toNat) (within : (s .timer).toNat ≤ 304) :
    circuit.observe i s .enabled = 3 ∧ circuit.observe i s .levels =
      BitVec.ofNat 3 (padValue (ackClocks[304-(s .timer).toNat]'(by rw [ack_clock_count]; omega))) := by
  let index : Fin 304 := ⟨304-(s .timer).toNat,by omega⟩
  have shift : (304#9-s .timer).toNat = index.val :=
    BitVec.toNat_sub_of_le (show (s .timer).toNat ≤ (304#9).toNat by exact within)
  have address : 304#9-s .timer = BitVec.ofNat 9 index.val := by
    apply BitVec.eq_of_toNat_eq
    rw [shift, BitVec.toNat_ofNat]
    exact (Nat.mod_eq_of_lt (by have := index.isLt; omega)).symm
  constructor
  · simp [Circuit.observe,circuit,output,sending,isMode,eq,Expr.eval,sendingMode]
  · change (output .levels).eval i s = _
    simp only [output,Expr.eval]
    have active : sending.eval i s = 1 := by simp [sending,isMode,eq,Expr.eval,sendingMode]
    rw [if_pos active,ackLevels_eval,address]
    exact finite_ack_table index

theorem two_stage (i : Values Input) (s : CoreState) (q : Quiet i) :
    circuit.step i s (.base .stage1) = i .rawInputs ∧
    circuit.step i s (.base .stage2) = s (.base .stage1) := by
  have reset := quiet_reset i s q
  have oldReset : StreamingReady.Core.resetting.eval i (baseState s) = 0 := by simpa using reset
  constructor <;>
    simp [Circuit.step,circuit,next,nextBase,receivingBase,Expr.eval,StreamingReady.Core.next,
      StreamingReady.Core.nextRaw,oldReset,baseState]

theorem legacy_step (i : Values Input) (s : CoreState)
    (off : s .mode = 0#3) (unselected : entering.eval i s = 0#1)
    (r : StreamingReady.Core.Register 1 w) :
    circuit.step i s (.base r) = (StreamingReady.Core.circuit 1).step i (baseState s) r := by
  simp [Circuit.step,circuit,next,nextBase,both,either,active,Expr.eval,off,unselected,
    StreamingReady.Core.circuit]

theorem legacy_status (i : Values Input) (s : CoreState) (off : s .mode = 0#3) (p : Output w) :
    circuit.observe i s p = (StreamingReady.Core.circuit 1).observe i (baseState s) p := by
  cases p <;> simp [Circuit.observe,circuit,output,sending,isMode,eq,Expr.eval,off,
    StreamingReady.Core.circuit]

end Pinwheel.Hardware.USB
