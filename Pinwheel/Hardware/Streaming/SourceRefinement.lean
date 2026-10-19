import Pinwheel.Hardware.Streaming.Core
import Pinwheel.Hardware.Streaming.PinCorrespondence
import Pinwheel.Program.StreamingCompile
import Pinwheel.Program.StreamingExecution
import Pinwheel.Program.StreamingSafety

/-! Source-to-expression correspondence for an installed streaming image.
The raw unused word bank is retained, rather than replaced by invented padding. -/
namespace Pinwheel.Hardware.Streaming.SourceRefinement
open Pinwheel.Hardware Pinwheel.Program.Streaming

structure Image (p : Program) where
  words : BitVec 6 → BitVec 64
  written : BitVec 64
  pending : BitVec 1
  source : ∀ k, k.toNat < p.length → words k = encode (p.memory[k.toNat]'(by have := k.isLt; omega))
  canonical : ∀ k : Fin 64, k.val < p.length → (p.memory[k.val]).Canonical

def values (image : Image p) (s : State a) : Values (Core.Register a) := fun r =>
  match r with
  | .word k => image.words k
  | .txWord k => (s.tx.memory[k.toNat]'(by exact k.isLt)).data
  | .txBits k => BitVec.ofNat 6 (s.tx.memory[k.toNat]'(by exact k.isLt)).validBits
  | .rxWord k => (s.rx.memory[k.toNat]'(by exact k.isLt)).data
  | .rxBits k => BitVec.ofNat 6 (s.rx.memory[k.toNat]'(by exact k.isLt)).validBits
  | .written => image.written | .pending => image.pending | .valid => 1
  | .count => BitVec.ofNat 7 p.length
  | .idleLevels => p.idle.levels | .idleEnabled => p.idle.enabled
  | .generation => s.generation | .transfer => s.transfer
  | .phase => s.phase.code | .pc => s.pc | .currentWord => encode s.current
  | .total => s.total | .remaining => s.remaining | .countdown => s.countdown
  | .cellBit => BitVec.ofBool s.cellBit | .levels => s.pins.levels | .enabled => s.pins.enabled
  | .txHead => BitVec.ofNat a s.tx.head.val | .txTail => BitVec.ofNat a s.tx.tail.val
  | .txCount => BitVec.ofNat 4 s.tx.count.val
  | .rxHead => BitVec.ofNat a s.rx.head.val | .rxTail => BitVec.ofNat a s.rx.tail.val
  | .rxCount => BitVec.ofNat 4 s.rx.count.val
  | .txShift => s.txShift | .txValid => s.txValid | .rxPartial => s.rxPartial | .rxUsed => s.rxUsed
  | .txAccepted => s.txAccepted | .txConsumed => s.txConsumed
  | .rxProduced => s.rxProduced | .rxPopped => s.rxPopped
  | .stage1 => s.samplerFirst | .stage2 => s.samplerSecond

def inputs (i : Input) : Values Core.Input := fun r => match r with
  | .initialize => BitVec.ofBool i.initialize | .command => i.command
  | .address => 0 | .word => 0 | .count => 0 | .idleLevels => 0 | .idleEnabled => 0
  | .startCount => i.startCount
  | .expectedGeneration => i.expectedGeneration | .expectedTransfer => i.expectedTransfer
  | .txPush => BitVec.ofBool i.txPush | .txData => i.txData | .txBits => i.txBits
  | .rxPop => BitVec.ofBool i.rxPop | .rawInputs => i.rawInputs

def RuntimeInput (i : Input) : Prop :=
  i.initialize = false ∧ i.command ≠ 15 ∧ i.command ≠ 1 ∧ i.command ≠ 2

abbrev Bounds (s : State a) := s.Structural

def operation : Instruction → BitVec 3
  | .pulse _ => 0 | .stream _ => 1 | .halt => 2 | .fault => 3

theorem encode_fields (instruction : Instruction) :
    WordFields (encode instruction) instruction.cell (operation instruction) := by
  cases instruction with
  | pulse c => exact cellWord_fields c 0
  | stream c => exact cellWord_fields c 1
  | halt => constructor <;> rfl
  | fault => constructor <;> rfl

private theorem and_bool (x y : Bool) :
    BitVec.ofBool x &&& BitVec.ofBool y = BitVec.ofBool (x && y) := by
  cases x <;> cases y <;> rfl

private theorem ofBool_one (x : Bool) : (BitVec.ofBool x = 1) ↔ x = true := by
  cases x <;> decide

private theorem inv_bool (x : Bool) : ~~~BitVec.ofBool x = BitVec.ofBool (!x) := by
  cases x <;> rfl

private theorem or_bool (x y : Bool) :
    ~~~(~~~BitVec.ofBool x &&& ~~~BitVec.ofBool y) = BitVec.ofBool (x || y) := by
  cases x <;> cases y <;> rfl

private theorem one_and (x : BitVec 1) : (1 : BitVec 1) &&& x = x := by
  have cases : x = 0 ∨ x = 1 := by bv_omega
  rcases cases with rfl | rfl <;> rfl

private theorem and_one_middle (x y z : Bool) :
    BitVec.ofBool x &&& (BitVec.ofBool y &&& ((1 : BitVec 1) &&& BitVec.ofBool z)) =
      BitVec.ofBool (x && (y && z)) := by
  cases x <;> cases y <;> cases z <;> rfl

theorem busy_eval (image : Image p) (s : State a) (i : Input) :
    Core.busy.eval (inputs i) (values image s) = BitVec.ofBool s.phase.busy := by
  cases phase : s.phase <;> simp [Core.busy,Core.both,Expr.eval,values,phase,Phase.code,Phase.busy]

theorem retained_eval (image : Image p) (s : State a) (i : Input) :
    Core.retained.eval (inputs i) (values image s) = BitVec.ofBool s.phase.retained := by
  cases phase : s.phase <;> simp [Core.retained,Core.either,Core.isPhase,Expr.eval,values,
    phase,Phase.code,Phase.retained]

theorem resetting_eval (image : Image p) (s : State a) (i : Input) (hi : RuntimeInput i) :
    Core.resetting.eval (inputs i) (values image s) = 0 := by
  rcases hi with ⟨cold,warm,write,commit⟩
  change i.command ≠ 15#4 at warm
  simp [Core.resetting,Core.warm,Core.cold,Core.cmd,Core.both,Core.either,Expr.eval,inputs,cold,warm]

theorem owned_eval (image : Image p) (s : State a) (i : Input) :
    Core.owned.eval (inputs i) (values image s) = BitVec.ofBool (s.phase.busy || s.phase.retained) := by
  simp only [Core.owned,Core.either,Expr.eval,busy_eval,retained_eval,or_bool]

theorem identity_eval (image : Image p) (s : State a) (i : Input) :
    Core.identity.eval (inputs i) (values image s) =
      BitVec.ofBool (i.expectedGeneration == s.generation && i.expectedTransfer == s.transfer) := by
  simp only [Core.identity,Core.both,Expr.eval,inputs,values,and_bool,Bool.beq_eq_decide_eq]
  rfl
  done

theorem free_eval (image : Image p) (s : State a) (i : Input) (hi : RuntimeInput i) :
    Core.free.eval (inputs i) (values image s) = BitVec.ofBool (s.phase == .free) := by
  cases phase : s.phase <;> simp [Core.free,Core.both,Expr.eval,resetting_eval image s i hi,
    values,phase,Phase.code,Bool.beq_eq_decide_eq]

theorem hostOwner_eval (image : Image p) (s : State a) (i : Input) (hi : RuntimeInput i) :
    Core.hostOwner.eval (inputs i) (values image s) = BitVec.ofBool (s.owned i) := by
  simp [Core.hostOwner,Core.both,Expr.eval,resetting_eval image s i hi,owned_eval,
    identity_eval,State.owned,Bool.and_assoc]
  exact one_and _
  done

theorem stream_eval (image : Image p) (s : State a) (i : Input) :
    Core.stream.eval (inputs i) (values image s) = BitVec.ofBool s.current.isStream := by
  cases current : s.current <;> simp [Core.stream,Core.field,Expr.eval,values,current,
    (encode_fields _).operation,operation,Instruction.isStream]
  done

theorem transmit_eval (image : Image p) (s : State a) (i : Input) :
    Core.transmit.eval (inputs i) (values image s) =
      BitVec.ofBool (s.current.isStream && s.current.cell.transmit) := by
  simp only [Core.transmit,Core.both,Expr.eval,stream_eval,Core.field,values,
    (encode_fields s.current).transmit,and_bool]
  done

theorem receive_eval (image : Image p) (s : State a) (i : Input) :
    Core.receive.eval (inputs i) (values image s) =
      BitVec.ofBool (s.current.isStream && s.current.cell.receive) := by
  simp only [Core.receive,Core.both,Expr.eval,stream_eval,Core.field,values,
    (encode_fields s.current).receive,and_bool]
  done

theorem lastCell_eval (image : Image p) (s : State a) (i : Input) :
    Core.lastCell.eval (inputs i) (values image s) = BitVec.ofBool s.lastCell := by
  simp only [Core.lastCell,Core.both,Expr.eval,stream_eval,values,State.lastCell,
    and_bool,Bool.beq_eq_decide_eq]
  rfl
  done

private theorem queue_count_lt (q : Queue a) (ha : a ≤ 3) : q.count.val < 16 := by
  have depth : 2^a ≤ 2^3 := Nat.pow_le_pow_right (by decide) ha
  have count := q.count.isLt
  unfold queueDepth at count
  omega

theorem queue_count_toNat (q : Queue a) (ha : a ≤ 3) :
    (BitVec.ofNat 4 q.count.val).toNat = q.count.val := by
  exact Nat.mod_eq_of_lt (queue_count_lt q ha)

private theorem bitvec_eq_nat (x y : BitVec w) : x = y ↔ x.toNat = y.toNat :=
  ⟨congrArg BitVec.toNat,BitVec.eq_of_toNat_eq⟩

theorem depth_toNat (ha : a ≤ 3) : (BitVec.ofNat 4 (2^a)).toNat = 2^a := by
  have depth : 2^a ≤ 2^3 := Nat.pow_le_pow_right (by decide) ha
  exact Nat.mod_eq_of_lt (by omega)

theorem txRoom_eval (image : Image p) (s : State a) (i : Input) (ha : a ≤ 3) :
    Core.txRoom.eval (inputs i) (values image s) = BitVec.ofBool s.tx.writable := by
  simp only [Core.txRoom,Core.depth,Expr.eval,values,queue_count_toNat _ ha,depth_toNat ha,
    Queue.writable,queueDepth]
  rfl

theorem rxRoom_eval (image : Image p) (s : State a) (i : Input) (ha : a ≤ 3) :
    Core.rxRoom.eval (inputs i) (values image s) = BitVec.ofBool s.rx.writable := by
  simp only [Core.rxRoom,Core.depth,Expr.eval,values,queue_count_toNat _ ha,depth_toNat ha,
    Queue.writable,queueDepth]
  rfl

theorem txAvailable_eval (image : Image p) (s : State a) (i : Input) (ha : a ≤ 3) :
    Core.txAvailable.eval (inputs i) (values image s) =
      BitVec.ofBool (s.txValid != 0 || s.tx.readable) := by
  have countZero : (BitVec.ofNat 4 s.tx.count.val = 0) ↔ s.tx.count.val = 0 := by
    rw [bitvec_eq_nat,queue_count_toNat _ ha]
    rfl
  simp only [Core.txAvailable,Core.either,Expr.eval,values,countZero,inv_bool,and_bool,Queue.readable]
  simp [bne,Bool.beq_eq_decide_eq]
  rfl
  done

theorem credit_eval (image : Image p) (s : State a) (i : Input) (ha : a ≤ 3) :
    Core.credit.eval (inputs i) (values image s) = BitVec.ofBool s.canReserve := by
  simp only [Core.credit,Core.both,Core.either,Expr.eval,transmit_eval,receive_eval,
    txAvailable_eval image s i ha,rxRoom_eval image s i ha,State.canReserve,
    State.txReady,State.rxReady,inv_bool,and_bool]
  cases s.current.isStream <;> simp [Bool.or_assoc]
  done

theorem starting_eval (image : Image p) (s : State a) (i : Input) (hi : RuntimeInput i) :
    Core.starting.eval (inputs i) (values image s) = BitVec.ofBool (i.command == 3 && s.canStart i) := by
  simp +instances [Core.starting,Core.both,Core.cmd,Core.space,Expr.eval,free_eval image s i hi,
    values,inputs,State.canStart,bne,Bool.beq_eq_decide_eq,
    Bool.and_assoc,Bool.and_comm,Bool.and_left_comm]
  exact and_one_middle _ _ _
  done

private theorem queue_count_zero (q : Queue a) (ha : a ≤ 3) :
    (BitVec.ofNat 4 q.count.val = 0) ↔ q.count = 0 := by
  rw [bitvec_eq_nat,queue_count_toNat _ ha]
  change (q.count.val = 0) ↔ q.count = 0
  constructor
  · intro h
    apply Fin.ext
    simpa using h
  · intro h
    simpa using congrArg Fin.val h

private theorem binary_congr (f : α → β → γ) {a b : α} {c d : β}
    (hab : a = b) (hcd : c = d) : f a c = f b d := by
  cases hab
  cases hcd
  rfl

theorem drained_eval (image : Image p) (s : State a) (i : Input) (ha : a ≤ 3) :
    Core.drained.eval (inputs i) (values image s) = BitVec.ofBool s.drained := by
  simp +instances [Core.drained,Core.both,Expr.eval,values,
    State.drained,Bool.beq_eq_decide_eq,Bool.and_assoc]
  exact congrArg BitVec.ofBool (binary_congr Bool.and
    (decide_eq_decide.mpr (queue_count_zero s.tx ha))
    (binary_congr Bool.and (decide_eq_decide.mpr (queue_count_zero s.rx ha)) rfl))
  done

theorem releasing_eval (image : Image p) (s : State a) (i : Input) (ha : a ≤ 3) (hi : RuntimeInput i) :
    Core.releasing.eval (inputs i) (values image s) =
      BitVec.ofBool (i.command == 4 && s.canRelease i) := by
  simp +instances [Core.releasing,Core.both,Core.cmd,Expr.eval,hostOwner_eval image s i hi,
    retained_eval,drained_eval image s i ha,inputs,State.canRelease,
    Bool.beq_eq_decide_eq,Bool.and_assoc,Bool.and_comm,Bool.and_left_comm]
  rfl
  done

theorem popping_eval (image : Image p) (s : State a) (i : Input) (ha : a ≤ 3) (hi : RuntimeInput i) :
    Core.popping.eval (inputs i) (values image s) = BitVec.ofBool (s.rx.willPop (s.hostPop i)) := by
  simp +instances [Core.popping,Core.both,Expr.eval,hostOwner_eval image s i hi,inputs,values,
    Queue.willPop,Queue.readable,State.hostPop,bne,
    Bool.beq_eq_decide_eq,Bool.and_assoc]
  exact congrArg BitVec.ofBool (binary_congr Bool.and rfl (binary_congr Bool.and rfl
    (congrArg Bool.not (decide_eq_decide.mpr (queue_count_zero s.rx ha)))))
  done


theorem pushing_eval (image : Image p) (s : State a) (i : Input) (ha : a ≤ 3)
    (hi : RuntimeInput i) (hs : s.Structural) :
    Core.pushing.eval (inputs i) (values image s) = BitVec.ofBool (s.tx.willPush (s.hostPush i)) := by
  have sub : (s.total - s.txAccepted).toNat = s.total.toNat - s.txAccepted.toNat :=
    BitVec.toNat_sub_of_le (by simpa only [BitVec.le_def] using hs.accepted)
  have bits : ((0 : BitVec 10) ++ i.txBits).toNat = i.txBits.toNat := by
    exact (BitVec.toNat_append (0#10) i.txBits).trans (by simp)
  have budget : (s.total - s.txAccepted).toNat < i.txBits.toNat ↔
      ¬ (s.txAccepted.toNat + i.txBits.toNat ≤ s.total.toNat) := by
    rw [sub]
    have bound := hs.accepted
    omega
  simp only [Core.pushing,Core.both,Core.txBits16,Expr.eval,
    hostOwner_eval image s i hi,txRoom_eval image s i ha,inputs,values,
    inv_bool,and_bool]
  change BitVec.ofBool (s.owned i && (i.txPush &&
    (s.tx.writable && (!decide (i.txBits = 0) &&
    (!decide (32 < i.txBits.toNat) &&
      !decide ((s.total - s.txAccepted).toNat < ((0 : BitVec 10) ++ i.txBits).toNat)))))) = _
  simp only [bits,budget]
  have zero : (i.txBits = 0) ↔ i.txBits.toNat = 0 := bitvec_eq_nat _ _
  by_cases owner : s.owned i = true <;> by_cases push : i.txPush = true <;>
    by_cases positive : 0 < i.txBits.toNat <;>
    by_cases width : i.txBits.toNat ≤ 32 <;>
    by_cases budget : s.txAccepted.toNat + i.txBits.toNat ≤ s.total.toNat <;>
    simp_all [State.hostPush,Queue.willPush,Bool.not_eq_true]
  all_goals try (split <;> simp_all <;> try omega)
  all_goals have nonzero : i.txBits.toNat ≠ 0 := by omega
  all_goals have widthnot : ¬ (32 < i.txBits.toNat) := by omega
  all_goals simp only [nonzero,widthnot,decide_false,Bool.not_false,Bool.and_true]
  all_goals rfl
  done


private theorem pointer_toNat (k : Fin (queueDepth a)) :
    (BitVec.ofNat a k.val).toNat = k.val := Nat.mod_eq_of_lt k.isLt

theorem txHeadWord_eval (image : Image p) (s : State a) (i : Input) :
    Core.txHeadWord.eval (inputs i) (values image s) = s.tx.peek.data := by
  simp only [Core.txHeadWord,Execution.readTree_correct,Expr.eval,values,pointer_toNat,Queue.peek]

theorem txHeadBits_eval (image : Image p) (s : State a) (i : Input) :
    Core.txHeadBits.eval (inputs i) (values image s) = BitVec.ofNat 6 s.tx.peek.validBits := by
  simp only [Core.txHeadBits,Execution.readTree_correct,Expr.eval,values,pointer_toNat,Queue.peek]

theorem rxHeadWord_eval (image : Image p) (s : State a) (i : Input) :
    Core.rxHeadWord.eval (inputs i) (values image s) = s.rx.peek.data := by
  simp only [Core.rxHeadWord,Execution.readTree_correct,Expr.eval,values,pointer_toNat,Queue.peek]

theorem rxHeadBits_eval (image : Image p) (s : State a) (i : Input) :
    Core.rxHeadBits.eval (inputs i) (values image s) = BitVec.ofNat 6 s.rx.peek.validBits := by
  simp only [Core.rxHeadBits,Execution.readTree_correct,Expr.eval,values,pointer_toNat,Queue.peek]

private theorem mux_projection (b : Bool) (f : α → β) (x y : α) :
    (if BitVec.ofBool b = 1 then f x else f y) = f (if b then x else y) := by
  cases b <;> rfl

theorem txSource_eval (image : Image p) (s : State a) (i : Input) :
    Core.txSource.eval (inputs i) (values image s) = s.selectedTx.data := by
  simp only [Core.txSource,Expr.eval,values,txHeadWord_eval,State.selectedTx,Bool.beq_eq_decide_eq]
  exact mux_projection (s.txValid == 0) Chunk.data s.tx.peek
    ⟨s.txShift, ⟨(s.txValid.toNat - 1) % 32, Nat.mod_lt _ (by decide)⟩⟩

theorem txSourceBits_eval (image : Image p) (s : State a) (i : Input) (hs : s.Structural) :
    Core.txSourceBits.eval (inputs i) (values image s) = BitVec.ofNat 6 s.selectedTx.validBits := by
  have semantic :
      (if BitVec.ofBool (s.txValid == 0) = 1 then BitVec.ofNat 6 s.tx.peek.validBits else s.txValid) =
        BitVec.ofNat 6 s.selectedTx.validBits := by
    by_cases zero : s.txValid = 0
    · simp [zero,State.selectedTx]
    · have positive : 0 < s.txValid.toNat := by bv_omega
      have bound := hs.txValid
      have mod : (s.txValid.toNat - 1) % 32 = s.txValid.toNat - 1 := Nat.mod_eq_of_lt (by omega)
      simp only [Bool.beq_eq_decide_eq,zero,decide_false,BitVec.ofBool_false,
        BitVec.reduceEq,ite_false,State.selectedTx,Chunk.validBits,Bool.false_eq_true]
      apply BitVec.eq_of_toNat_eq
      change s.txValid.toNat = ((s.txValid.toNat - 1) % 32 + 1) % 64
      rw [mod]
      omega
  simp only [Core.txSourceBits,Expr.eval,values,txHeadBits_eval]
  exact semantic


theorem isPhase_eval (image : Image p) (s : State a) (i : Input) (phase : Phase) :
    (Core.isPhase phase.code).eval (inputs i) (values image s) = BitVec.ofBool (s.phase == phase) := by
  cases state : s.phase <;> cases phase <;>
    simp [Core.isPhase,Expr.eval,values,state,Phase.code,Bool.beq_eq_decide_eq]

theorem reserving_eval (image : Image p) (s : State a) (i : Input) (ha : a ≤ 3) (hi : RuntimeInput i) :
    Core.reserving.eval (inputs i) (values image s) =
      BitVec.ofBool (s.phase == .boundary && s.canReserve) := by
  simp only [Core.reserving,Core.both,Expr.eval,resetting_eval image s i hi,
    show (2 : BitVec 3) = Phase.boundary.code from rfl,isPhase_eval,
    credit_eval image s i ha,and_bool]
  exact one_and _

theorem takingTX_eval (image : Image p) (s : State a) (i : Input) (ha : a ≤ 3) (hi : RuntimeInput i) :
    Core.takingTX.eval (inputs i) (values image s) =
      BitVec.ofBool (s.phase == .boundary && s.canReserve &&
        s.current.isStream && s.current.cell.transmit) := by
  simp only [Core.takingTX,Core.both,Expr.eval,reserving_eval image s i ha hi,transmit_eval,and_bool]
  simp only [Bool.and_assoc]

theorem loadingTX_eval (image : Image p) (s : State a) (i : Input) (ha : a ≤ 3) (hi : RuntimeInput i) :
    Core.loadingTX.eval (inputs i) (values image s) = BitVec.ofBool s.enginePop := by
  simp only [Core.loadingTX,Core.both,Expr.eval,takingTX_eval image s i ha hi,values,
    and_bool,State.enginePop,Bool.beq_eq_decide_eq]
  rfl

theorem capture_eval (image : Image p) (s : State a) (i : Input) (hi : RuntimeInput i) :
    Core.capture.eval (inputs i) (values image s) =
      BitVec.ofBool (s.phase == .low && s.countdown == 0) := by
  simp only [Core.capture,Core.both,Expr.eval,resetting_eval image s i hi,
    show (3 : BitVec 3) = Phase.low.code from rfl,isPhase_eval,values,and_bool,
    Bool.beq_eq_decide_eq]
  exact one_and _

theorem capturingRX_eval (image : Image p) (s : State a) (i : Input) (hi : RuntimeInput i) :
    Core.capturingRX.eval (inputs i) (values image s) = BitVec.ofBool s.captures := by
  simp only [Core.capturingRX,Core.both,Expr.eval,capture_eval image s i hi,receive_eval,
    and_bool,State.captures,Bool.beq_eq_decide_eq,Bool.and_assoc]

theorem emittingRX_eval (image : Image p) (s : State a) (i : Input) (hi : RuntimeInput i) :
    Core.emittingRX.eval (inputs i) (values image s) = BitVec.ofBool s.enginePush.isSome := by
  simp only [Core.emittingRX,Core.both,Core.either,Expr.eval,capturingRX_eval image s i hi,
    lastCell_eval,values,and_bool,or_bool,State.enginePush,Bool.beq_eq_decide_eq]
  have optionSome (b : Bool) (x : Chunk) : (if b then some x else none).isSome = b := by
    cases b <;> rfl
  simp only [optionSome,State.lastCell]
  have semantic (capture stream used last : Bool) (h : capture = true → stream = true) :
      (capture && (used || (stream && last))) = (capture && (used || last)) := by
    cases capture <;> cases stream <;> cases used <;> cases last <;> simp_all
  exact congrArg BitVec.ofBool (semantic s.captures s.current.isStream (s.rxUsed == 31)
    (s.remaining == 1) (by
      intro h
      simp only [State.captures,Bool.and_eq_true] at h
      exact h.1.2))

theorem highEnd_eval (image : Image p) (s : State a) (i : Input) (hi : RuntimeInput i) :
    Core.highEnd.eval (inputs i) (values image s) =
      BitVec.ofBool (s.phase == .high && s.countdown == 0) := by
  simp only [Core.highEnd,Core.both,Expr.eval,resetting_eval image s i hi,
    show (4 : BitVec 3) = Phase.high.code from rfl,isPhase_eval,values,and_bool,
    Bool.beq_eq_decide_eq]
  exact one_and _

theorem repeating_eval (image : Image p) (s : State a) (i : Input) :
    Core.repeating.eval (inputs i) (values image s) =
      BitVec.ofBool (s.current.isStream && decide (1 < s.remaining.toNat)) := by
  simp only [Core.repeating,Core.both,Expr.eval,stream_eval,values,and_bool]
  rfl

theorem fetching_eval (image : Image p) (s : State a) (i : Input) (hi : RuntimeInput i) :
    Core.fetching.eval (inputs i) (values image s) = BitVec.ofBool (s.phase == .fetch) := by
  simp only [Core.fetching,Core.both,Expr.eval,resetting_eval image s i hi,
    show (1 : BitVec 3) = Phase.fetch.code from rfl,isPhase_eval]
  exact one_and _


theorem increment (x : BitVec w) : x - BitVec.ofNat w (2^w-1) = x + 1 := by
  have ones : BitVec.ofNat w (2^w-1) = BitVec.allOnes w := by
    exact (BitVec.ofNatLT_eq_ofNat (Nat.sub_lt (Nat.two_pow_pos w) (by decide))).symm
  exact (congrArg (fun y => x-y) ones).trans
    ((congrArg (fun y => x-y) BitVec.neg_one_eq_allOnes.symm).trans BitVec.sub_neg)

theorem inc_eval (x : Core.E a w) (i : Values Core.Input) (r : Values (Core.Register a)) :
    (Core.inc x).eval i r = x.eval i r + 1 := increment _

theorem addition (x y : BitVec w) : x - (0 - y) = x + y := by
  exact (congrArg (fun z => x-z) (BitVec.zero_sub (x := y))).trans BitVec.sub_neg

private theorem slice_bit (x : BitVec w) (k : Nat) :
    x.extractLsb' k 1 = BitVec.ofBool (x.getLsbD k) := by
  apply BitVec.eq_of_getLsbD_eq
  intro j
  by_cases h : j = 0
  · subst j
    simp
  · simp [BitVec.getLsbD_ofBool,BitVec.getLsbD_extractLsb',show ¬ j < 1 from by omega,h]

theorem nextBit_eval (image : Image p) (s : State a) (i : Input) :
    Core.nextBit.eval (inputs i) (values image s) = BitVec.ofBool s.selectedTx.data[31] := by
  simp only [Core.nextBit,Expr.eval,txSource_eval,slice_bit]
  exact congrArg BitVec.ofBool (BitVec.getLsbD_eq_getElem (by decide))

theorem inputBit_eval (image : Image p) (s : State a) (i : Input) :
    Core.inputBit.eval (inputs i) (values image s) =
      BitVec.ofBool s.samplerSecond[s.current.cell.rxInput.val] := by
  simp only [Core.inputBit,Core.field,Expr.eval,values,(encode_fields s.current).rxInput]
  have cases : s.current.cell.rxInput.val = 0 ∨ s.current.cell.rxInput.val = 1 := by
    have bound := s.current.cell.rxInput.isLt
    omega
  rcases cases with h | h <;> simp [h,slice_bit,BitVec.getLsbD_eq_getElem]

theorem append_bit (x : BitVec 32) (bit : Bool) :
    x.extractLsb' 0 31 ++ BitVec.ofBool bit =
      (x <<< 1) ||| BitVec.ofNat 32 (if bit then 1 else 0) := by
  apply BitVec.eq_of_getLsbD_eq
  intro j
  rw [BitVec.getLsbD_append (x := x.extractLsb' 0 31) (y := BitVec.ofBool bit)]
  by_cases zero : j = 0
  · subst j
    cases bit <;> simp
  · have positive : 1 ≤ j := by omega
    simp only [BitVec.getLsbD_extractLsb',BitVec.getLsbD_or,BitVec.getLsbD_shiftLeft]
    cases bit <;> simp [zero,show ¬ j < 1 from by omega]
    all_goals by_cases bound : j < 32 <;> simp [bound,show j-1<31 ↔ j<32 from by omega]
    all_goals exact (BitVec.getLsbD_of_ge x (by omega)).symm

theorem assembled_eval (image : Image p) (s : State a) (i : Input) :
    Core.assembled.eval (inputs i) (values image s) = s.capturedWord := by
  simp only [Core.assembled,Expr.eval,values,inputBit_eval,append_bit,State.capturedWord]


theorem length_positive (p : Program) : 0 < p.length := by simp [Program.length]
theorem length_le (p : Program) : p.length ≤ 64 := by
  have bound := p.lengthMinusOne.isLt
  unfold Program.length
  omega

theorem entryBounds_eval (image : Image p) (s : State a) (i : Input) :
    Core.entryBounds.eval (inputs i) (values image s) = BitVec.ofBool (decide (s.pc.toNat < p.length)) := by
  have size : (BitVec.ofNat 7 p.length).toNat = p.length := Nat.mod_eq_of_lt (by have := length_le p; omega)
  simp only [Core.entryBounds,Expr.eval,values,size]

theorem entryWord_eval (image : Image p) (s : State a) (i : Input) (h : s.pc.toNat < p.length) :
    Core.entryWord.eval (inputs i) (values image s) =
      encode (p.memory[s.pc.toNat]'(by have := length_le p; omega)) := by
  simp only [Core.entryWord,Execution.readTree_correct,Expr.eval,values]
  have address : (s.pc.extractLsb' 0 6).toNat = s.pc.toNat := by
    change s.pc.toNat % 64 = s.pc.toNat
    exact Nat.mod_eq_of_lt (by have := length_le p; omega)
  have word := image.source (s.pc.extractLsb' 0 6) (by rw [address]; exact h)
  simpa only [address] using word

theorem fetch_some (image : Image p) (s : State a) (i : Input) (instruction : Instruction)
    (fetch : p.fetch s.pc.toNat = some instruction) :
    Core.entryWord.eval (inputs i) (values image s) = encode instruction ∧ instruction.Canonical := by
  by_cases bound : s.pc.toNat < p.length
  · have selected : p.memory[s.pc.toNat]'(by have := length_le p; omega) = instruction := by
      simpa only [Program.fetch,bound,dif_pos,Option.some.injEq] using fetch
    constructor
    · simpa only [selected] using entryWord_eval image s i bound
    · simpa only [selected] using image.canonical ⟨s.pc.toNat,by have := length_le p; omega⟩ bound
  · simp [Program.fetch,bound] at fetch

theorem writing_eval (image : Image p) (s : State a) (i : Input) (hi : RuntimeInput i) :
    Core.writing.eval (inputs i) (values image s) = 0 := by
  have cmd : (Core.cmd (a := a) 1).eval (inputs i) (values image s) = 0 := by
    change BitVec.ofBool (decide (i.command = 1)) = 0
    simp only [hi.2.2.1,decide_false,BitVec.ofBool_false]
  simp only [Core.writing,Core.both,Expr.eval,cmd]
  exact BitVec.and_zero

theorem committing_eval (image : Image p) (s : State a) (i : Input) (hi : RuntimeInput i) :
    Core.committing.eval (inputs i) (values image s) = 0 := by
  have cmd : (Core.cmd (a := a) 2).eval (inputs i) (values image s) = 0 := by
    change BitVec.ofBool (decide (i.command = 2)) = 0
    simp only [hi.2.2.2,decide_false,BitVec.ofBool_false]
  simp only [Core.committing,Core.both,Expr.eval,cmd]
  have zero_middle (x y : BitVec 1) : x &&& (0 &&& y) = 0 :=
    (congrArg (fun z => x &&& z) BitVec.zero_and).trans BitVec.and_zero
  exact zero_middle _ _


theorem entryCanonical_of_word (image : Image p) (s : State a) (i : Input) (instruction : Instruction)
    (word : Core.entryWord.eval (inputs i) (values image s) = encode instruction)
    (canonical : instruction.Canonical) :
    Core.entryCanonical.eval (inputs i) (values image s) = 1 := by
  cases instruction with
  | pulse c =>
    simp only [Core.entryCanonical,Core.entryPulse,Core.entryKind,Core.entryField,
      Expr.eval,word,encode,(cellWord_fields c 0).operation,
      cellWord_pulse_upper c canonical]
    rfl
  | stream c =>
    have selector : (BitVec.ofNat 2 c.txOutput.val).toNat < 3 := by
      have bound := c.txOutput.isLt
      change c.txOutput.val % 4 < 3
      omega
    simp only [Core.entryCanonical,Core.entryPulse,Core.entryStream,Core.entryKind,
      Core.entryField,Core.both,Core.either,Expr.eval,word,encode,
      (cellWord_fields c 1).operation,(cellWord_fields c 1).reserved,
      (cellWord_fields c 1).transmit,(cellWord_fields c 1).txOutput]
    change ((1 : BitVec 1) &&& ~~~(~~~(~~~BitVec.ofBool c.transmit) &&&
      ~~~BitVec.ofBool (decide ((BitVec.ofNat 2 c.txOutput.val).toNat < 3)))) = 1
    simp only [selector,decide_true]
    cases c.transmit <;> rfl
  | halt =>
    simp [Core.entryCanonical,Core.entryPulse,Core.entryStream,Core.entryKind,
      Core.entryField,Core.entryHalt,Core.entryFault,Core.both,Core.either,Expr.eval,word,encode]
  | fault =>
    simp [Core.entryCanonical,Core.entryPulse,Core.entryStream,Core.entryKind,
      Core.entryField,Core.entryHalt,Core.entryFault,Core.both,Core.either,Expr.eval,word,encode]


private theorem encode_ne_terminal (instruction : Instruction) (n : Nat)
    (h : operation instruction ≠ (BitVec.ofNat 64 n).extractLsb' 0 3) :
    encode instruction ≠ BitVec.ofNat 64 n := by
  intro equal
  exact h ((encode_fields instruction).operation.symm.trans
    (congrArg (fun x : BitVec 64 => x.extractLsb' 0 3) equal))

theorem encode_halt (instruction : Instruction) : (encode instruction = 2) ↔ instruction = .halt := by
  cases instruction with
  | pulse c =>
    constructor
    · intro h; exact False.elim (encode_ne_terminal (.pulse c) 2 (by simp only [operation]; decide) h)
    · intro h; cases h
  | stream c =>
    constructor
    · intro h; exact False.elim (encode_ne_terminal (.stream c) 2 (by simp only [operation]; decide) h)
    · intro h; cases h
  | halt => simp [encode]
  | fault => simp [encode]

theorem encode_fault (instruction : Instruction) : (encode instruction = 3) ↔ instruction = .fault := by
  cases instruction with
  | pulse c =>
    constructor
    · intro h; exact False.elim (encode_ne_terminal (.pulse c) 3 (by simp only [operation]; decide) h)
    · intro h; cases h
  | stream c =>
    constructor
    · intro h; exact False.elim (encode_ne_terminal (.stream c) 3 (by simp only [operation]; decide) h)
    · intro h; cases h
  | halt => simp [encode]
  | fault => simp [encode]

theorem entryHalt_of_word (image : Image p) (s : State a) (i : Input) (instruction : Instruction)
    (word : Core.entryWord.eval (inputs i) (values image s) = encode instruction) :
    Core.entryHalt.eval (inputs i) (values image s) = BitVec.ofBool (instruction == .halt) := by
  simp only [Core.entryHalt,Expr.eval,word,encode_halt,Bool.beq_eq_decide_eq]

theorem entryFault_of_word (image : Image p) (s : State a) (i : Input) (instruction : Instruction)
    (word : Core.entryWord.eval (inputs i) (values image s) = encode instruction) :
    Core.entryFault.eval (inputs i) (values image s) = BitVec.ofBool (instruction == .fault) := by
  simp only [Core.entryFault,Expr.eval,word,encode_fault,Bool.beq_eq_decide_eq]

theorem entryStream_of_word (image : Image p) (s : State a) (i : Input) (instruction : Instruction)
    (word : Core.entryWord.eval (inputs i) (values image s) = encode instruction) :
    Core.entryStream.eval (inputs i) (values image s) = BitVec.ofBool instruction.isStream := by
  simp only [Core.entryStream,Core.entryKind,Core.entryField,Expr.eval,word,
    (encode_fields instruction).operation]
  cases instruction <;> rfl

theorem entryBad_of_fetch (image : Image p) (s : State a) (i : Input) (instruction : Instruction)
    (fetch : p.fetch s.pc.toNat = some instruction) :
    Core.entryBad.eval (inputs i) (values image s) = 0 := by
  have bound : s.pc.toNat < p.length := by
    by_cases h : s.pc.toNat < p.length
    · exact h
    · simp [Program.fetch,h] at fetch
  have word := fetch_some image s i instruction fetch
  simp only [Core.entryBad,Core.either,Expr.eval,entryBounds_eval,
    entryCanonical_of_word image s i instruction word.1 word.2,bound,decide_true]
  rfl

theorem entryBad_of_none (image : Image p) (s : State a) (i : Input)
    (fetch : p.fetch s.pc.toNat = none) :
    Core.entryBad.eval (inputs i) (values image s) = 1 := by
  have bound : ¬ s.pc.toNat < p.length := by
    intro h
    simp [Program.fetch,h] at fetch
  simp only [Core.entryBad,Core.either,Expr.eval,entryBounds_eval,bound,decide_false]
  have any (x : BitVec 1) : ~~~(~~~(~~~BitVec.ofBool false) &&& ~~~(~~~x)) = 1 := by
    have cases : x = 0 ∨ x = 1 := by bv_omega
    rcases cases with rfl | rfl <;> rfl
  exact any _


theorem enginePop_readable (s : State a) (pop : s.enginePop = true) : s.tx.readable = true := by
  have all : (s.phase == .boundary) = true ∧ s.canReserve = true ∧
      s.current.isStream = true ∧ s.current.cell.transmit = true ∧ s.txValid == 0 := by
    simpa only [State.enginePop,Bool.and_eq_true,and_assoc] using pop
  have reserve := all.2.1
  simp only [State.canReserve,State.txReady,State.rxReady,all.2.2.1,
    all.2.2.2.1,Bool.not_true,Bool.false_or,Bool.and_eq_true] at reserve
  have valid : s.txValid = 0 := beq_iff_eq.mp all.2.2.2.2
  simpa only [valid,bne,beq_self_eq_true,Bool.not_true,Bool.false_or] using reserve.1

theorem enginePop_take (s : State a) : s.tx.willPop s.enginePop = s.enginePop := by
  cases pop : s.enginePop
  · simp [Queue.willPop]
  · simp [Queue.willPop,enginePop_readable s pop]

theorem enginePush_writable (s : State a) (hs : s.Structural) (push : s.enginePush.isSome = true) :
    s.rx.writable = true := by
  have capture : s.captures = true := by
    unfold State.enginePush at push
    split at push
    · rename_i condition
      have both : s.captures = true ∧ (s.rxUsed == 31 || s.remaining == 1) = true := by
        simpa only [Bool.and_eq_true] using condition
      exact both.1
    · contradiction
  have condition : s.phase = .low ∧ s.countdown = 0 ∧
      s.current.isStream = true ∧ s.current.cell.receive = true := by
    simpa only [State.captures,Bool.and_eq_true,Bool.beq_eq_decide_eq,decide_eq_true_eq,and_assoc] using capture
  exact hs.rx_writable s condition.1 condition.2.2.1 condition.2.2.2

theorem enginePush_put (s : State a) (hs : s.Structural) :
    s.rx.willPush s.enginePush = s.enginePush.isSome := by
  cases push : s.enginePush.isSome
  · simp [Queue.willPush,push]
  · simp [Queue.willPush,push,enginePush_writable s hs push]

theorem hostPush_bits (s : State a) (i : Input) (push : (s.hostPush i).isSome = true) :
    BitVec.ofNat 6 (s.hostPush i |>.getD {}).validBits = i.txBits := by
  unfold State.hostPush at push ⊢
  split at push
  · rename_i condition
    simp only [condition,Chunk.validBits]
    have positive := condition.2.2.1
    have width := condition.2.2.2.1
    apply BitVec.eq_of_toNat_eq
    change (i.txBits.toNat - 1 + 1) % 64 = i.txBits.toNat
    have bound := i.txBits.isLt
    omega
  · contradiction

theorem enginePush_bits (s : State a) (hs : s.Structural) (push : s.enginePush.isSome = true) :
    BitVec.ofNat 6 (s.enginePush.getD {}).validBits = s.rxUsed + 1 := by
  unfold State.enginePush at push ⊢
  split at push
  · rename_i condition
    simp only [condition,ite_true,Option.getD_some,Chunk.validBits]
    apply BitVec.eq_of_toNat_eq
    have bound := hs.rxUsed
    change (s.rxUsed.toNat % 32 + 1) % 64 = (s.rxUsed + 1).toNat
    rw [Nat.mod_eq_of_lt bound]
    bv_omega
  · contradiction


theorem start_step (image : Image p) (s : State a) (i : Input) (ha : a ≤ 3) (hi : RuntimeInput i)
    (start : (i.command == 3 && s.canStart i) = true) (r : Core.Register a w) :
    (Core.circuit a).step (inputs i) (values image s) r = values image (s.start p i) r := by
  have free : s.phase = .free := by
    simp only [Bool.and_eq_true,State.canStart] at start
    have all : (i.command == 3) = true ∧ (s.phase == .free) = true ∧
      (i.expectedGeneration == s.generation) = true ∧ (s.transfer != 65535) = true := by
      simpa only [Bool.and_eq_true,and_assoc] using start
    exact beq_iff_eq.mp all.2.1
  have starting : Core.starting.eval (inputs i) (values image s) = 1 := by
    rw [starting_eval image s i hi,start]
    rfl
  have releasing : Core.releasing.eval (inputs i) (values image s) = 0 := by
    rw [releasing_eval image s i ha hi]
    simp [State.canRelease,free,Phase.retained]
  cases r <;>
    simp [Core.circuit,Circuit.step,Core.next,Core.nextRaw,Core.nextPins,Core.clearedRuntime,
      Core.both,Core.either,Core.cold,Expr.eval,starting,releasing,writing_eval image s i hi,
      committing_eval image s i hi,resetting_eval image s i hi,inputs,values,hi.1,
      State.start,Queue.empty,Chunk.validBits,inc_eval]
  all_goals rfl
  done


theorem release_step (image : Image p) (s : State a) (i : Input) (ha : a ≤ 3) (hi : RuntimeInput i)
    (release : (i.command == 4 && s.canRelease i) = true) (r : Core.Register a w) :
    (Core.circuit a).step (inputs i) (values image s) r = values image (s.release p i) r := by
  have retained : s.phase.retained = true := by
    have all : (i.command == 4) = true ∧ s.phase.retained = true ∧ s.owned i = true ∧ s.drained = true := by
      simpa only [State.canRelease,Bool.and_eq_true,and_assoc] using release
    exact all.2.1
  have notfree : (s.phase == .free) = false := by
    cases phase : s.phase <;> simp_all [Phase.retained]
  have starting : Core.starting.eval (inputs i) (values image s) = 0 := by
    rw [starting_eval image s i hi]
    simp [State.canStart,notfree]
  have releasing : Core.releasing.eval (inputs i) (values image s) = 1 := by
    rw [releasing_eval image s i ha hi,release]
    rfl
  cases r <;>
    simp [Core.circuit,Circuit.step,Core.next,Core.nextRaw,Core.nextPins,Core.clearedRuntime,
      Core.both,Core.either,Core.cold,Expr.eval,starting,releasing,writing_eval image s i hi,
      committing_eval image s i hi,resetting_eval image s i hi,inputs,values,hi.1,
      State.release,Queue.empty,Chunk.validBits]
  all_goals rfl
  done


theorem pointer_increment (k : Fin (queueDepth a)) :
    BitVec.ofNat a (Queue.nextIndex k).val = BitVec.ofNat a k.val + 1 := by
  apply BitVec.eq_of_toNat_eq
  change ((k.val + 1) % 2^a) % 2^a = ((BitVec.ofNat a k.val) + 1).toNat
  rw [Nat.mod_mod,BitVec.toNat_add,pointer_toNat]
  change (k.val + 1) % 2^a = (k.val + 1 % 2^a) % 2^a
  simpa only [Nat.mod_eq_of_lt (show k.val < 2^a from k.isLt)] using Nat.add_mod k.val 1 (2^a)

theorem pointer_equal (k : Fin (queueDepth a)) (address : BitVec a) :
    (BitVec.ofNat a k.val = address) ↔ k.val = address.toNat := by
  rw [bitvec_eq_nat,pointer_toNat]

private theorem count_transition (n : Nat) (bound : n < 16) (put take : Bool)
    (putBound : put = true → n < 15) (takeBound : take = true → 0 < n) :
    (if put then (if take then BitVec.ofNat 4 n else BitVec.ofNat 4 n + 1)
      else if take then BitVec.ofNat 4 n - 1 else BitVec.ofNat 4 n) =
      BitVec.ofNat 4 (n + (if put then 1 else 0) - (if take then 1 else 0)) := by
  cases put <;> cases take
  case false.false => rfl
  case false.true =>
    apply BitVec.eq_of_toNat_eq
    change (16 - 1 + n % 16) % 16 = (n - 1) % 16
    have positive := takeBound rfl
    omega
  case true.false =>
    apply BitVec.eq_of_toNat_eq
    change (n % 16 + 1) % 16 = (n + 1) % 16
    have room := putBound rfl
    omega
  case true.true =>
    simp only [ite_true,Nat.add_sub_cancel]

theorem queueCount_eval (q : Queue a) (incoming : Option Chunk) (outgoing : Bool)
    (ha : a ≤ 3) (old : Core.E a 4) (put take : Core.E a 1)
    (i : Values Core.Input) (r : Values (Core.Register a))
    (hold : old.eval i r = BitVec.ofNat 4 q.count.val)
    (hput : put.eval i r = BitVec.ofBool (q.willPush incoming))
    (htake : take.eval i r = BitVec.ofBool (q.willPop outgoing)) :
    (Core.queueCount old put take).eval i r = BitVec.ofNat 4 (q.tick incoming outgoing).count.val := by
  have putBound : q.willPush incoming = true → q.count.val < 15 := by
    intro h
    have both : incoming.isSome = true ∧ q.writable = true := by
      simpa only [Queue.willPush,Bool.and_eq_true] using h
    have room : q.count.val < queueDepth a := by simpa only [Queue.writable,decide_eq_true_eq] using both.2
    have depth : 2^a ≤ 2^3 := Nat.pow_le_pow_right (by decide) ha
    unfold queueDepth at room
    omega
  have takeBound : q.willPop outgoing = true → 0 < q.count.val := by
    intro h
    have readable : q.readable = true := by
      cases outgoing <;> simp_all [Queue.willPop]
    have nonzero : q.count.val ≠ 0 := by
      intro zero
      simp [Queue.readable,zero] at readable
    omega
  simp only [Core.queueCount,Expr.eval,hold,hput,htake,inc_eval,ofBool_one]
  exact count_transition q.count.val (queue_count_lt q ha) _ _ putBound takeBound

theorem queue_memory (q : Queue a) (incoming : Option Chunk) (outgoing : Bool)
    (address : BitVec a) (f : Chunk → β) :
    f ((q.tick incoming outgoing).memory[address.toNat]'address.isLt) =
      if q.willPush incoming && decide (BitVec.ofNat a q.tail.val = address)
      then f (incoming.getD {}) else f (q.memory[address.toNat]'address.isLt) := by
  have equal := pointer_equal q.tail address
  change f ((if q.willPush incoming then q.memory.set q.tail.val (incoming.getD {})
    else q.memory)[address.toNat]'address.isLt) = _
  cases put : q.willPush incoming
  · rfl
  · simp only [ite_true,Vector.getElem_set,equal,Bool.true_and,decide_eq_true_eq]
    split <;> rfl


def NoAdmission (s : State a) (i : Input) : Prop :=
  (i.command == 3 && s.canStart i) = false ∧ (i.command == 4 && s.canRelease i) = false

theorem starting_zero (image : Image p) (s : State a) (i : Input) (hi : RuntimeInput i)
    (no : NoAdmission s i) : Core.starting.eval (inputs i) (values image s) = 0 := by
  rw [starting_eval image s i hi,no.1]
  rfl

theorem releasing_zero (image : Image p) (s : State a) (i : Input) (ha : a ≤ 3) (hi : RuntimeInput i)
    (no : NoAdmission s i) : Core.releasing.eval (inputs i) (values image s) = 0 := by
  rw [releasing_eval image s i ha hi,no.2]
  rfl

theorem cleared_zero (image : Image p) (s : State a) (i : Input) (ha : a ≤ 3) (hi : RuntimeInput i)
    (no : NoAdmission s i) : Core.clearedRuntime.eval (inputs i) (values image s) = 0 := by
  simp only [Core.clearedRuntime,Core.either,Expr.eval,starting_zero image s i hi no,
    releasing_zero image s i ha hi no,resetting_eval image s i hi]
  rfl

theorem hostPush_data (s : State a) (i : Input) (push : (s.hostPush i).isSome = true) :
    (s.hostPush i |>.getD {}).data = i.txData := by
  unfold State.hostPush at push ⊢
  split at push
  · rename_i condition
    simp only [condition]
    rfl
  · contradiction

theorem enginePush_data (s : State a) (push : s.enginePush.isSome = true) :
    (s.enginePush.getD {}).data = s.capturedWord := by
  unfold State.enginePush at push ⊢
  split at push
  · rename_i condition
    simp only [condition,ite_true,Option.getD_some]
  · contradiction

private theorem mux_value (b : Bool) (x y : α) :
    (if BitVec.ofBool b = 1 then x else y) = if b then x else y := by
  cases b <;> rfl

theorem clock_txWord (image : Image p) (s : State a) (i : Input) (ha : a ≤ 3)
    (hi : RuntimeInput i) (hs : s.Structural) (no : NoAdmission s i) (k : BitVec a) :
    (Core.circuit a).step (inputs i) (values image s) (.txWord k) =
      values image (clock p i s) (.txWord k) := by
  change _ = ((s.tx.tick (s.hostPush i) s.enginePop).memory[k.toNat]'k.isLt).data
  refine Eq.trans ?_ (queue_memory s.tx (s.hostPush i) s.enginePop k Chunk.data).symm
  simp only [Core.circuit,Circuit.step,Core.next,Core.nextRaw,Expr.eval,
    cleared_zero image s i ha hi no,Core.both,pushing_eval image s i ha hi hs,values,inputs,
    and_bool,ofBool_one]
  have semantic (put : Bool) (old fresh actual : BitVec 32) (address : Bool)
      (h : put = true → fresh = actual) :
      (if put && address then actual else old) = if put && address then fresh else old := by
    cases put <;> simp_all
  exact semantic (s.tx.willPush (s.hostPush i)) _ _ i.txData _ (by
    intro push
    have both : (s.hostPush i).isSome = true ∧ s.tx.writable = true := by
      simpa only [Queue.willPush,Bool.and_eq_true] using push
    exact hostPush_data s i both.1)


theorem clock_txBits (image : Image p) (s : State a) (i : Input) (ha : a ≤ 3)
    (hi : RuntimeInput i) (hs : s.Structural) (no : NoAdmission s i) (k : BitVec a) :
    (Core.circuit a).step (inputs i) (values image s) (.txBits k) =
      values image (clock p i s) (.txBits k) := by
  change _ = BitVec.ofNat 6 ((s.tx.tick (s.hostPush i) s.enginePop).memory[k.toNat]'k.isLt).validBits
  refine Eq.trans ?_ (queue_memory s.tx (s.hostPush i) s.enginePop k (fun c => BitVec.ofNat 6 c.validBits)).symm
  simp only [Core.circuit,Circuit.step,Core.next,Core.nextRaw,Expr.eval,
    cleared_zero image s i ha hi no,Core.both,pushing_eval image s i ha hi hs,values,inputs,
    and_bool,ofBool_one]
  have semantic (put : Bool) (old fresh actual : BitVec 6) (address : Bool)
      (h : put = true → fresh = actual) :
      (if put && address then actual else old) = if put && address then fresh else old := by
    cases put <;> simp_all
  exact semantic (s.tx.willPush (s.hostPush i)) _ _ i.txBits _ (by
    intro push
    have both : (s.hostPush i).isSome = true ∧ s.tx.writable = true := by
      simpa only [Queue.willPush,Bool.and_eq_true] using push
    exact hostPush_bits s i both.1)

theorem clock_rxWord (image : Image p) (s : State a) (i : Input) (ha : a ≤ 3)
    (hi : RuntimeInput i) (hs : s.Structural) (no : NoAdmission s i) (k : BitVec a) :
    (Core.circuit a).step (inputs i) (values image s) (.rxWord k) =
      values image (clock p i s) (.rxWord k) := by
  change _ = ((s.rx.tick s.enginePush (s.hostPop i)).memory[k.toNat]'k.isLt).data
  refine Eq.trans ?_ (queue_memory s.rx s.enginePush (s.hostPop i) k Chunk.data).symm
  simp only [Core.circuit,Circuit.step,Core.next,Core.nextRaw,Expr.eval,
    cleared_zero image s i ha hi no,Core.both,emittingRX_eval image s i hi,values,
    assembled_eval,and_bool,ofBool_one,enginePush_put s hs]
  have semantic (put : Bool) (old fresh actual : BitVec 32) (address : Bool)
      (h : put = true → fresh = actual) :
      (if put && address then actual else old) = if put && address then fresh else old := by
    cases put <;> simp_all
  exact semantic s.enginePush.isSome _ _ s.capturedWord _ (enginePush_data s)

theorem clock_rxBits (image : Image p) (s : State a) (i : Input) (ha : a ≤ 3)
    (hi : RuntimeInput i) (hs : s.Structural) (no : NoAdmission s i) (k : BitVec a) :
    (Core.circuit a).step (inputs i) (values image s) (.rxBits k) =
      values image (clock p i s) (.rxBits k) := by
  change _ = BitVec.ofNat 6 ((s.rx.tick s.enginePush (s.hostPop i)).memory[k.toNat]'k.isLt).validBits
  refine Eq.trans ?_ (queue_memory s.rx s.enginePush (s.hostPop i) k (fun c => BitVec.ofNat 6 c.validBits)).symm
  simp only [Core.circuit,Circuit.step,Core.next,Core.nextRaw,Expr.eval,
    cleared_zero image s i ha hi no,Core.both,emittingRX_eval image s i hi,values,
    inc_eval,and_bool,ofBool_one,enginePush_put s hs]
  have semantic (put : Bool) (old fresh actual : BitVec 6) (address : Bool)
      (h : put = true → fresh = actual) :
      (if put && address then actual else old) = if put && address then fresh else old := by
    cases put <;> simp_all
  exact semantic s.enginePush.isSome _ _ (s.rxUsed + 1) _ (enginePush_bits s hs)


theorem queue_head (q : Queue a) (incoming : Option Chunk) (outgoing : Bool) :
    BitVec.ofNat a (q.tick incoming outgoing).head.val =
      if q.willPop outgoing then BitVec.ofNat a q.head.val + 1 else BitVec.ofNat a q.head.val := by
  change BitVec.ofNat a (if q.willPop outgoing then Queue.nextIndex q.head else q.head).val = _
  cases take : q.willPop outgoing
  · rfl
  · exact pointer_increment q.head

theorem queue_tail (q : Queue a) (incoming : Option Chunk) (outgoing : Bool) :
    BitVec.ofNat a (q.tick incoming outgoing).tail.val =
      if q.willPush incoming then BitVec.ofNat a q.tail.val + 1 else BitVec.ofNat a q.tail.val := by
  change BitVec.ofNat a (if q.willPush incoming then Queue.nextIndex q.tail else q.tail).val = _
  cases put : q.willPush incoming
  · rfl
  · exact pointer_increment q.tail

theorem clock_txHead (image : Image p) (s : State a) (i : Input) (ha : a ≤ 3)
    (hi : RuntimeInput i) (no : NoAdmission s i) :
    (Core.circuit a).step (inputs i) (values image s) .txHead = values image (clock p i s) .txHead := by
  change _ = BitVec.ofNat a (s.tx.tick (s.hostPush i) s.enginePop).head.val
  refine Eq.trans ?_ (queue_head s.tx (s.hostPush i) s.enginePop).symm
  simp only [Core.circuit,Circuit.step,Core.next,Core.nextRaw,Core.either,Expr.eval,
    resetting_eval image s i hi,starting_zero image s i hi no,releasing_zero image s i ha hi no,
    loadingTX_eval image s i ha hi,inc_eval,values,enginePop_take,ofBool_one]
  rfl

theorem clock_txTail (image : Image p) (s : State a) (i : Input) (ha : a ≤ 3)
    (hi : RuntimeInput i) (hs : s.Structural) (no : NoAdmission s i) :
    (Core.circuit a).step (inputs i) (values image s) .txTail = values image (clock p i s) .txTail := by
  change _ = BitVec.ofNat a (s.tx.tick (s.hostPush i) s.enginePop).tail.val
  refine Eq.trans ?_ (queue_tail s.tx (s.hostPush i) s.enginePop).symm
  simp only [Core.circuit,Circuit.step,Core.next,Core.nextRaw,Core.either,Expr.eval,
    resetting_eval image s i hi,starting_zero image s i hi no,releasing_zero image s i ha hi no,
    pushing_eval image s i ha hi hs,inc_eval,values,ofBool_one]
  rfl

theorem clock_rxHead (image : Image p) (s : State a) (i : Input) (ha : a ≤ 3)
    (hi : RuntimeInput i) (no : NoAdmission s i) :
    (Core.circuit a).step (inputs i) (values image s) .rxHead = values image (clock p i s) .rxHead := by
  change _ = BitVec.ofNat a (s.rx.tick s.enginePush (s.hostPop i)).head.val
  refine Eq.trans ?_ (queue_head s.rx s.enginePush (s.hostPop i)).symm
  simp only [Core.circuit,Circuit.step,Core.next,Core.nextRaw,Core.either,Expr.eval,
    resetting_eval image s i hi,starting_zero image s i hi no,releasing_zero image s i ha hi no,
    popping_eval image s i ha hi,inc_eval,values,ofBool_one]
  rfl

theorem clock_rxTail (image : Image p) (s : State a) (i : Input) (ha : a ≤ 3)
    (hi : RuntimeInput i) (hs : s.Structural) (no : NoAdmission s i) :
    (Core.circuit a).step (inputs i) (values image s) .rxTail = values image (clock p i s) .rxTail := by
  change _ = BitVec.ofNat a (s.rx.tick s.enginePush (s.hostPop i)).tail.val
  refine Eq.trans ?_ (queue_tail s.rx s.enginePush (s.hostPop i)).symm
  simp only [Core.circuit,Circuit.step,Core.next,Core.nextRaw,Core.either,Expr.eval,
    resetting_eval image s i hi,starting_zero image s i hi no,releasing_zero image s i ha hi no,
    emittingRX_eval image s i hi,inc_eval,values,enginePush_put s hs,ofBool_one]
  rfl

theorem clock_txCount (image : Image p) (s : State a) (i : Input) (ha : a ≤ 3)
    (hi : RuntimeInput i) (hs : s.Structural) (no : NoAdmission s i) :
    (Core.circuit a).step (inputs i) (values image s) .txCount = values image (clock p i s) .txCount := by
  change _ = BitVec.ofNat 4 (s.tx.tick (s.hostPush i) s.enginePop).count.val
  simp only [Core.circuit,Circuit.step,Core.next,Core.nextRaw,Core.either,Expr.eval,
    resetting_eval image s i hi,starting_zero image s i hi no,releasing_zero image s i ha hi no]
  change (Core.queueCount (.reg .txCount) Core.pushing Core.loadingTX).eval (inputs i) (values image s) = _
  exact queueCount_eval s.tx (s.hostPush i) s.enginePop ha _ _ _ (inputs i) (values image s) rfl
    (pushing_eval image s i ha hi hs)
    ((loadingTX_eval image s i ha hi).trans (congrArg BitVec.ofBool (enginePop_take s).symm))

theorem clock_rxCount (image : Image p) (s : State a) (i : Input) (ha : a ≤ 3)
    (hi : RuntimeInput i) (hs : s.Structural) (no : NoAdmission s i) :
    (Core.circuit a).step (inputs i) (values image s) .rxCount = values image (clock p i s) .rxCount := by
  change _ = BitVec.ofNat 4 (s.rx.tick s.enginePush (s.hostPop i)).count.val
  simp only [Core.circuit,Circuit.step,Core.next,Core.nextRaw,Core.either,Expr.eval,
    resetting_eval image s i hi,starting_zero image s i hi no,releasing_zero image s i ha hi no]
  change (Core.queueCount (.reg .rxCount) Core.emittingRX Core.popping).eval (inputs i) (values image s) = _
  exact queueCount_eval s.rx s.enginePush (s.hostPop i) ha _ _ _ (inputs i) (values image s) rfl
    ((emittingRX_eval image s i hi).trans (congrArg BitVec.ofBool (enginePush_put s hs).symm))
    (popping_eval image s i ha hi)


theorem entryTerminal_of_word (image : Image p) (s : State a) (i : Input) (instruction : Instruction)
    (word : Core.entryWord.eval (inputs i) (values image s) = encode instruction) :
    Core.entryTerminal.eval (inputs i) (values image s) =
      BitVec.ofBool (instruction == .halt || instruction == .fault) := by
  simp only [Core.entryTerminal,Core.either,Expr.eval,entryHalt_of_word image s i instruction word,
    entryFault_of_word image s i instruction word,or_bool]

theorem entrySkip_of_word (image : Image p) (s : State a) (i : Input) (instruction : Instruction)
    (word : Core.entryWord.eval (inputs i) (values image s) = encode instruction) :
    Core.entrySkip.eval (inputs i) (values image s) =
      BitVec.ofBool (instruction.isStream && s.remaining == 0) := by
  simp only [Core.entrySkip,Core.both,Expr.eval,entryStream_of_word image s i instruction word,
    values,and_bool,Bool.beq_eq_decide_eq]
  rfl

theorem entryLast_of_word (image : Image p) (s : State a) (i : Input) (instruction : Instruction)
    (word : Core.entryWord.eval (inputs i) (values image s) = encode instruction) :
    Core.entryLast.eval (inputs i) (values image s) =
      BitVec.ofBool (instruction.isStream && s.remaining == 1) := by
  simp only [Core.entryLast,Core.both,Expr.eval,entryStream_of_word image s i instruction word,
    values,and_bool,Bool.beq_eq_decide_eq]
  rfl

private theorem either_value (x y : BitVec w) : ~~~(~~~x &&& ~~~y) = x ||| y := by
  rw [BitVec.not_and,BitVec.not_not,BitVec.not_not]

theorem basePins_eval (image : Image p) (s : State a) (i : Input) (high enabled : Bool) :
    (Core.basePins high enabled).eval (inputs i) (values image s) =
      if enabled then (s.current.cell.basePins high s.lastCell).enabled
      else (s.current.cell.basePins high s.lastCell).levels := by
  exact PinCorrespondence.base_fields (inputs i) (values image s) s.current.cell (operation s.current)
    high enabled s.lastCell (encode_fields s.current) (lastCell_eval image s i)

theorem driven_eval (image : Image p) (s : State a) (i : Input) (high enabled : Bool) (bit : Core.E a 1) :
    let pins := if s.current.isStream then s.current.cell.dataPins high (s.remaining == 1)
      ((bit.eval (inputs i) (values image s)).getLsbD 0)
      else if high then s.current.cell.highPins else s.current.cell.lowPins
    (Core.driven high enabled bit).eval (inputs i) (values image s) =
      if enabled then pins.enabled else pins.levels := by
  exact PinCorrespondence.driven_instruction (inputs i) (values image s) s.current high enabled bit rfl

theorem entryLow_of_word (image : Image p) (s : State a) (i : Input) (instruction : Instruction)
    (enabled : Bool) (word : Core.entryWord.eval (inputs i) (values image s) = encode instruction) :
    (Core.entryLow enabled).eval (inputs i) (values image s) =
      let pins := instruction.cell.basePins false (instruction.isStream && s.remaining == 1)
      if enabled then pins.enabled else pins.levels := by
  have fields := encode_fields instruction
  simp only [Core.entryLow,Core.either,Core.entryField,Expr.eval,word,
    entryLast_of_word image s i instruction word,either_value,ofBool_one]
  cases enabled <;> cases last : (instruction.isStream && s.remaining == 1) <;>
    simp only [fields.lowLevels,fields.lowEnabled,fields.lastLowLevels,fields.lastLowEnabled,
      Cell.basePins,ite_false,ite_true,Bool.false_eq_true]
  all_goals first | rfl | exact BitVec.or_zero


theorem clock_nextPins (image : Image p) (s : State a) (i : Input) (ha : a ≤ 3)
    (hi : RuntimeInput i) (no : NoAdmission s i) (enabled : Bool) :
    (Core.nextPins enabled).eval (inputs i) (values image s) =
      if enabled then (engine p s).pins.enabled else (engine p s).pins.levels := by
  simp only [Core.nextPins,Core.enteringCell,Core.both,Core.either,Expr.eval,
    starting_zero image s i hi no,releasing_zero image s i ha hi no,
    fetching_eval image s i hi,reserving_eval image s i ha hi,
    capture_eval image s i hi,highEnd_eval image s i hi,basePins_eval,driven_eval,
    nextBit_eval,values,BitVec.ofNat_eq_ofNat]
  cases phase : s.phase <;>
    simp [phase,engine,Bool.beq_eq_decide_eq,State.stop,BitVec.ofNat_eq_ofNat]
  case free => cases enabled <;> rfl
  case completed => cases enabled <;> rfl
  case fault => cases enabled <;> rfl
  case high =>
    cases enabled <;> by_cases count : s.countdown = 0#8 <;> simp [count,Expr.eval,values]
  case low =>
    cases enabled <;> by_cases count : s.countdown = 0#8 <;>
      cases stream : s.current.isStream <;>
      simp [count,stream,State.lastCell,Expr.eval,values,Bool.beq_eq_decide_eq,BitVec.ofNat_eq_ofNat]
  case boundary =>
    cases enabled <;> cases credit : s.canReserve <;> cases stream : s.current.isStream <;>
      cases transmit : s.current.cell.transmit <;>
      simp [stream,transmit,State.lastCell,Cell.dataPins,Expr.eval,values,
        Bool.beq_eq_decide_eq,BitVec.ofNat_eq_ofNat]
  case fetch =>
    cases fetch : p.fetch s.pc.toNat with
    | none =>
      have bad := entryBad_of_none image s i fetch
      cases enabled <;> simp [bad,Expr.eval,values]
    | some instruction =>
      have word := (fetch_some image s i instruction fetch).1
      have bad := entryBad_of_fetch image s i instruction fetch
      simp only [bad,entryTerminal_of_word image s i instruction word,
        entrySkip_of_word image s i instruction word,entryLow_of_word image s i instruction enabled word]
      cases instruction <;> cases enabled <;>
        by_cases remaining : s.remaining = 0#16 <;>
        simp [remaining,Instruction.isStream,Instruction.cell,Cell.basePins,Expr.eval,values,
          Bool.beq_eq_decide_eq,BitVec.ofNat_eq_ofNat]
  done


theorem add_eval (x y : Core.E a w) (i : Values Core.Input) (r : Values (Core.Register a)) :
    (Core.add x y).eval i r = x.eval i r + y.eval i r := addition _ _

theorem shift_zero (x : BitVec 32) : x.extractLsb' 0 31 ++ 0#1 = x <<< 1 :=
  (append_bit x false).trans BitVec.or_zero

theorem chunk_decrement (c : Chunk) :
    BitVec.ofNat 6 c.validBits - 1#6 = BitVec.ofNat 6 (c.validBits - 1) := by
  apply BitVec.eq_of_toNat_eq
  change (64 - 1 + c.validBits % 64) % 64 = (c.validBits - 1) % 64
  have positive := c.validBits_positive
  have bound := c.validBits_le
  omega

theorem chunk_extend (c : Chunk) :
    (0#10 ++ BitVec.ofNat 6 c.validBits) = BitVec.ofNat 16 c.validBits := by
  apply BitVec.eq_of_toNat_eq
  have joined := BitVec.toNat_append (0#10) (BitVec.ofNat 6 c.validBits)
  change (0#10 ++ BitVec.ofNat 6 c.validBits).toNat = c.validBits % 65536
  rw [joined]
  simp only [show (0#10).toNat = 0 from rfl,Nat.zero_shiftLeft,Nat.zero_or,BitVec.toNat_ofNat]
  change c.validBits % 64 = c.validBits % 65536
  have bound := c.validBits_le
  omega

theorem hostPush_extend (s : State a) (i : Input) (push : (s.hostPush i).isSome = true) :
    (0#10 ++ i.txBits) = BitVec.ofNat 16 (s.hostPush i |>.getD {}).validBits := by
  exact (congrArg (fun v : BitVec 6 => 0#10 ++ v) (hostPush_bits s i push).symm).trans (chunk_extend _)

theorem clock_txAccepted (image : Image p) (s : State a) (i : Input) (ha : a ≤ 3)
    (hi : RuntimeInput i) (hs : s.Structural) (no : NoAdmission s i) :
    (Core.circuit a).step (inputs i) (values image s) .txAccepted = values image (clock p i s) .txAccepted := by
  simp only [Core.circuit,Circuit.step,Core.next,Core.nextRaw,Core.either,Expr.eval,
    resetting_eval image s i hi,starting_zero image s i hi no,releasing_zero image s i ha hi no,
    pushing_eval image s i ha hi hs,Core.txBits16,add_eval,values,inputs,clock,
    BitVec.ofNat_eq_ofNat]
  cases push : s.tx.willPush (s.hostPush i)
  · simp
  · have some : (s.hostPush i).isSome = true := by
      have both : (s.hostPush i).isSome = true ∧ s.tx.writable = true := by
        simpa only [Queue.willPush,Bool.and_eq_true] using push
      exact both.1
    simp only [ite_true,hostPush_extend s i some]
    rfl

theorem clock_rxPopped (image : Image p) (s : State a) (i : Input) (ha : a ≤ 3)
    (hi : RuntimeInput i) (no : NoAdmission s i) :
    (Core.circuit a).step (inputs i) (values image s) .rxPopped = values image (clock p i s) .rxPopped := by
  simp only [Core.circuit,Circuit.step,Core.next,Core.nextRaw,Core.either,Expr.eval,
    resetting_eval image s i hi,starting_zero image s i hi no,releasing_zero image s i ha hi no,
    popping_eval image s i ha hi,add_eval,rxHeadBits_eval,chunk_extend,values,clock,
    BitVec.ofNat_eq_ofNat]
  cases pop : s.rx.willPop (s.hostPop i) <;> simp


theorem clock_levels (image : Image p) (s : State a) (i : Input) (ha : a ≤ 3)
    (hi : RuntimeInput i) (no : NoAdmission s i) :
    (Core.circuit a).step (inputs i) (values image s) .levels = values image (clock p i s) .levels := by
  simp only [Core.circuit,Circuit.step,Core.next,Core.nextRaw,Expr.eval,resetting_eval image s i hi]
  change (Core.nextPins false).eval (inputs i) (values image s) = (engine p s).pins.levels
  exact clock_nextPins image s i ha hi no false

theorem clock_enabled (image : Image p) (s : State a) (i : Input) (ha : a ≤ 3)
    (hi : RuntimeInput i) (no : NoAdmission s i) :
    (Core.circuit a).step (inputs i) (values image s) .enabled = values image (clock p i s) .enabled := by
  simp only [Core.circuit,Circuit.step,Core.next,Core.nextRaw,Expr.eval,resetting_eval image s i hi]
  change (Core.nextPins true).eval (inputs i) (values image s) = (engine p s).pins.enabled
  exact clock_nextPins image s i ha hi no true

private theorem conditional_add (b : Bool) (x y : BitVec w) :
    (if b then x+y else x) = x + (if b then y else 0) := by
  cases b <;> simp

theorem clock_step (image : Image p) (s : State a) (i : Input) (ha : a ≤ 3)
    (hi : RuntimeInput i) (hs : s.Structural) (no : NoAdmission s i) (r : Core.Register a w) :
    (Core.circuit a).step (inputs i) (values image s) r = values image (clock p i s) r := by
  cases r
  case txWord k => exact clock_txWord image s i ha hi hs no k
  case txBits k => exact clock_txBits image s i ha hi hs no k
  case rxWord k => exact clock_rxWord image s i ha hi hs no k
  case rxBits k => exact clock_rxBits image s i ha hi hs no k
  case txHead => exact clock_txHead image s i ha hi no
  case txTail => exact clock_txTail image s i ha hi hs no
  case rxHead => exact clock_rxHead image s i ha hi no
  case rxTail => exact clock_rxTail image s i ha hi hs no
  case txCount => exact clock_txCount image s i ha hi hs no
  case rxCount => exact clock_rxCount image s i ha hi hs no
  case txAccepted => exact clock_txAccepted image s i ha hi hs no
  case rxPopped => exact clock_rxPopped image s i ha hi no
  case levels => exact clock_levels image s i ha hi no
  case enabled => exact clock_enabled image s i ha hi no
  all_goals simp only [Core.circuit,Circuit.step,Core.next,Core.nextRaw,Core.cold,
    Core.enteringCell,Core.advancing,Core.both,Core.either,Core.field,Expr.eval,
    starting_zero image s i hi no,releasing_zero image s i ha hi no,
    resetting_eval image s i hi,cleared_zero image s i ha hi no,
    writing_eval image s i hi,committing_eval image s i hi,
    fetching_eval image s i hi,reserving_eval image s i ha hi,
    takingTX_eval image s i ha hi,transmit_eval,capture_eval image s i hi,capturingRX_eval image s i hi,
    emittingRX_eval image s i hi,highEnd_eval image s i hi,repeating_eval,stream_eval,
    txSource_eval,txSourceBits_eval image s i hs,assembled_eval,nextBit_eval,inc_eval,
    values,inputs,hi.1,clock,(encode_fields s.current).lowDuration,(encode_fields s.current).highDuration,
    and_bool,inv_bool,shift_zero,chunk_decrement,BitVec.ofNat_eq_ofNat]
  all_goals cases phase : s.phase <;>
    simp [phase,engine,Bool.beq_eq_decide_eq,State.stop,Phase.code,BitVec.ofNat_eq_ofNat,
      Core.isPhase,Expr.eval,values,State.captures]
  all_goals first
    | (have fetchPhase : s.phase = .fetch := phase
       cases fetch : p.fetch s.pc.toNat with
       | none =>
         have bad := entryBad_of_none image s i fetch
         simp [bad]
       | some instruction =>
         have word := (fetch_some image s i instruction fetch).1
         have bad := entryBad_of_fetch image s i instruction fetch
         try simp only [bad,entryTerminal_of_word image s i instruction word,
           entrySkip_of_word image s i instruction word,entryFault_of_word image s i instruction word,word]
         cases instruction <;> by_cases remaining : s.remaining = 0#16 <;>
           simp [remaining,Instruction.isStream,Bool.beq_eq_decide_eq,BitVec.ofNat_eq_ofNat])
    | (cases credit : s.canReserve <;> by_cases count : s.countdown = 0#8 <;>
       cases stream : s.current.isStream <;> cases transmit : s.current.cell.transmit <;>
       by_cases repeating : 1 < s.remaining.toNat <;>
       try simp [count,repeating,phase,BitVec.ofNat_eq_ofNat])
  all_goals first | exact chunk_decrement _ | exact conditional_add _ _ _
  done


/-- Every register agrees for every installed source state satisfying the independently
preserved structural bounds, and every non-loader/non-reset sampled input. -/
theorem step_correct (image : Image p) (s : State a) (i : Input) (ha : a ≤ 3)
    (hi : RuntimeInput i) (hs : s.Structural) (r : Core.Register a w) :
    (Core.circuit a).step (inputs i) (values image s) r = values image (step p i s) r := by
  have warm : (i.command == 15) = false := by
    simpa only [Bool.beq_eq_decide_eq] using (decide_eq_false hi.2.1)
  by_cases start : (i.command == 3 && s.canStart i) = true
  · simpa only [step,hi.1,warm,start,Bool.false_eq_true,ite_false,ite_true] using
      start_step image s i ha hi start r
  · have notstart : (i.command == 3 && s.canStart i) = false := by
      cases h : (i.command == 3 && s.canStart i) <;> simp_all
    by_cases release : (i.command == 4 && s.canRelease i) = true
    · simpa only [step,hi.1,warm,notstart,release,Bool.false_eq_true,ite_false,ite_true] using
        release_step image s i ha hi release r
    · have notrelease : (i.command == 4 && s.canRelease i) = false := by
        cases h : (i.command == 4 && s.canRelease i) <;> simp_all
      simpa only [step,hi.1,warm,notstart,notrelease,Bool.false_eq_true,ite_false] using
        clock_step image s i ha hi hs ⟨notstart,notrelease⟩ r

theorem step_values (image : Image p) (s : State a) (i : Input) (ha : a ≤ 3)
    (hi : RuntimeInput i) (hs : s.Structural) :
    @Circuit.step _ _ _ (Core.circuit a) (inputs i) (values image s) =
      @values p a image (step p i s) := by
  funext w r
  exact step_correct image s i ha hi hs r

/-- The ordinary actual expression circuit clocks once for every sampled input. -/
def runCircuit (registers : Values (Core.Register a)) (samples : List Input) : Values (Core.Register a) :=
  samples.foldl (α := Values (Core.Register a))
    (fun r i => @Circuit.step _ _ _ (Core.circuit a) (inputs i) r) registers

theorem run_correct (image : Image p) (s : State a) (samples : List Input) (ha : a ≤ 3)
    (hi : ∀ i ∈ samples, RuntimeInput i) (hs : s.Structural) :
    @runCircuit a (values image s) samples = @values p a image (run p s samples) := by
  induction samples generalizing s with
  | nil => rfl
  | cons i rest ih =>
    have runtime : RuntimeInput i := hi i (by simp)
    have tail : ∀ j ∈ rest, RuntimeInput j := by
      intro j member
      exact hi j (by simp [member])
    change @runCircuit a (@Circuit.step _ _ _ (Core.circuit a) (inputs i) (values image s)) rest =
      @values p a image (run p (step p i s) rest)
    rw [step_values image s i ha runtime hs]
    exact ih (step p i s) tail (step_structural p s i hs)

end Pinwheel.Hardware.Streaming.SourceRefinement
