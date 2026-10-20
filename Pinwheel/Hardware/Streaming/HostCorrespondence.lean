import Pinwheel.Hardware.Streaming.Frontend
import Pinwheel.Program.StreamingHostExecution

/-! All-state source correspondence for the finite physical host frontend. -/
namespace Pinwheel.Hardware.Streaming.HostCorrespondence
open Pinwheel.Hardware Pinwheel.Program.Streaming

def statusValues (t : Host.Status) : Values Core.Output := fun p => match p with
  | .valid => BitVec.ofBool t.valid | .busy => BitVec.ofBool t.busy
  | .retained => BitVec.ofBool t.retained | .pending => BitVec.ofBool t.pending
  | .rejected => BitVec.ofBool t.rejected | .stalled => BitVec.ofBool t.stalled
  | .fault => BitVec.ofBool t.fault | .waitingTX => BitVec.ofBool t.waitingTX
  | .waitingRX => BitVec.ofBool t.waitingRX | .generation => t.generation | .transfer => t.transfer
  | .phase => t.phase | .pc => t.pc | .remaining => t.remaining | .total => t.total
  | .levels => t.levels | .enabled => t.enabled
  | .txFree => t.txFree | .txQueued => t.txQueued | .rxQueued => t.rxQueued
  | .rxData => t.rxData | .rxBits => t.rxBits
  | .txAccepted => t.txAccepted | .txConsumed => t.txConsumed
  | .rxProduced => t.rxProduced | .rxPopped => t.rxPopped
  | .stage1 => t.stage1 | .stage2 => t.stage2

def inputs (i : Host.Input) : Values Frontend.Input := fun p => match p with
  | .initialize => BitVec.ofBool i.initialize | .sck => BitVec.ofBool i.sck
  | .csn => BitVec.ofBool i.csn | .mosi => i.mosi | .rawInputs => i.rawInputs
  | .status p => statusValues i.status p

def values (s : Host.State) : Values Frontend.Register := fun p => match p with
  | .sckPrev => BitVec.ofBool s.sckPrev | .csnPrev => BitVec.ofBool s.csnPrev
  | .active => BitVec.ofBool s.active | .reading => BitVec.ofBool s.reading
  | .count => s.count | .request => s.request | .requestCRC => s.requestCRC
  | .phase => s.phase | .code => s.code | .sequence => s.sequence
  | .cacheReply => BitVec.ofBool s.cacheReply | .response => s.response | .ready => BitVec.ofBool s.ready
  | .lastValid => BitVec.ofBool s.lastValid | .lastRequest => s.lastRequest | .lastReply => s.lastReply
  | .txLeft => s.txLeft | .txStaging => s.txStaging
  | .rxPending => BitVec.ofBool s.rxPending | .workBulk => BitVec.ofBool s.workBulk
  | .exportData => s.exportData | .exportStart => s.exportStart | .exportBits => s.exportBits
  | .ackOffset => s.ackOffset | .replyLogical => s.replyLogical | .crcWork => s.crcWork
  | .crc => s.crc | .crcCount => s.crcCount

def commandValues (c : Host.Command) : Values Core.Input := fun p => match p with
  | .initialize => BitVec.ofBool c.runtime.initialize | .command => c.runtime.command
  | .address => c.address | .word => c.word | .count => c.count
  | .idleLevels => c.idle.levels | .idleEnabled => c.idle.enabled
  | .startCount => c.runtime.startCount | .expectedGeneration => c.runtime.expectedGeneration
  | .expectedTransfer => c.runtime.expectedTransfer | .txPush => BitVec.ofBool c.runtime.txPush
  | .txData => c.runtime.txData | .txBits => c.runtime.txBits | .rxPop => BitVec.ofBool c.runtime.rxPop
  | .rawInputs => c.runtime.rawInputs

@[simp] private theorem ofBool_eq_one (b : Bool) : (BitVec.ofBool b = 1#1) ↔ b = true := by
  cases b <;> decide

@[simp] private theorem ofBool_eq_zero (b : Bool) : (BitVec.ofBool b = 0#1) ↔ b = false := by
  cases b <;> decide

@[simp] private theorem ofBool_ite (condition yes no : Bool) :
    BitVec.ofBool (if condition then yes else no) =
      if condition then BitVec.ofBool yes else BitVec.ofBool no := by
  cases condition <;> rfl

@[simp] private theorem ofBool_ite_prop (condition : Prop) [Decidable condition] (yes no : Bool) :
    BitVec.ofBool (if condition then yes else no) =
      if condition then BitVec.ofBool yes else BitVec.ofBool no := by
  by_cases condition <;> simp_all

@[simp] private theorem if_ofBool_true (condition : Prop) [Decidable condition] (yes : Bool) :
    (if condition then BitVec.ofBool yes else 1#1) = BitVec.ofBool (!decide condition || yes) := by
  by_cases condition <;> simp_all

@[simp] private theorem if_true_ofBool (condition : Prop) [Decidable condition] (no : Bool) :
    (if condition then 1#1 else BitVec.ofBool no) = BitVec.ofBool (decide condition || no) := by
  by_cases condition <;> simp_all

@[simp] private theorem if_false_ofBool (condition : Prop) [Decidable condition] (no : Bool) :
    (if condition then 0#1 else BitVec.ofBool no) = BitVec.ofBool (!decide condition && no) := by
  by_cases condition <;> simp_all

private theorem either_value (x y : BitVec w) : ~~~(~~~x &&& ~~~y) = x ||| y := by
  rw [BitVec.not_and, BitVec.not_not, BitVec.not_not]

private theorem xor_value (x y : BitVec w) :
    ~~~(~~~(x &&& ~~~y) &&& ~~~(~~~x &&& y)) = x ^^^ y := by
  apply BitVec.eq_of_getLsbD_eq
  intro k within
  simp only [BitVec.getLsbD_not, BitVec.getLsbD_and, BitVec.getLsbD_xor, within,
    decide_true, Bool.true_and]
  cases x.getLsbD k <;> cases y.getLsbD k <;> rfl

private theorem maximum_eq_allOnes (w : Nat) :
    BitVec.ofNat w (2^w - 1) = BitVec.allOnes w := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (Nat.sub_lt (Nat.two_pow_pos w) (by decide : 0 < (1 : Nat)))]

@[simp] theorem either_eval (i : Values Frontend.Input) (s : Values Frontend.Register)
    (x y : Frontend.E w) :
    (Frontend.either x y).eval i s = x.eval i s ||| y.eval i s := by
  exact either_value _ _

@[simp] theorem xor_eval (i : Values Frontend.Input) (s : Values Frontend.Register)
    (x y : Frontend.E w) :
    (Frontend.xor x y).eval i s = x.eval i s ^^^ y.eval i s := by
  exact xor_value _ _

@[simp] theorem inc_eval (i : Values Frontend.Input) (s : Values Frontend.Register)
    (x : Frontend.E w) : (Frontend.inc x).eval i s = x.eval i s + 1 := by
  simp only [Frontend.inc, Expr.eval, maximum_eq_allOnes, ← BitVec.neg_one_eq_allOnes, BitVec.sub_neg,
    BitVec.ofNat_eq_ofNat]

@[simp] theorem add_eval (i : Values Frontend.Input) (s : Values Frontend.Register)
    (x y : Frontend.E w) : (Frontend.add x y).eval i s = x.eval i s + y.eval i s := by
  simp only [Frontend.add, Expr.eval, BitVec.ofNat_eq_ofNat, BitVec.zero_sub, BitVec.sub_neg]

@[simp] theorem payload_eval (i : Host.Input) (s : Host.State) (start len : Nat) (fits : start+len ≤ 128) :
    (Frontend.payload start len fits).eval (inputs i) (values s) = s.payload start len := rfl

@[simp] theorem opcode_eval (i : Host.Input) (s : Host.State) :
    Frontend.opcode.eval (inputs i) (values s) = s.opcode := rfl

@[simp] theorem requestSequence_eval (i : Host.Input) (s : Host.State) :
    Frontend.requestSequence.eval (inputs i) (values s) = s.requestSequence := rfl

@[simp] theorem op_eval (i : Host.Input) (s : Host.State) (operation : BitVec 4) :
    (Frontend.op operation).eval (inputs i) (values s) = BitVec.ofBool (s.opcode == operation) := by
  simp only [Frontend.op, Expr.eval, opcode_eval, Bool.beq_eq_decide_eq]
  rfl

@[simp] theorem isPhase_eval (i : Host.Input) (s : Host.State) (phase : BitVec 3) :
    (Frontend.isPhase phase).eval (inputs i) (values s) = BitVec.ofBool (s.phase == phase) := by
  simp only [Frontend.isPhase, Expr.eval, values, Bool.beq_eq_decide_eq]
  rfl

@[simp] theorem status_eval (i : Host.Input) (s : Host.State) (p : Core.Output w) :
    (Frontend.status p).eval (inputs i) (values s) = statusValues i.status p := rfl

@[simp] theorem startingFrame_eval (i : Host.Input) (s : Host.State) :
    Frontend.startingFrame.eval (inputs i) (values s) = BitVec.ofBool (s.startingFrame i) := by
  simp [Frontend.startingFrame, Frontend.both, Expr.eval, inputs, values,
    Host.State.startingFrame, Bool.and_assoc, BitVec.ofNat_eq_ofNat]

@[simp] theorem bulk_eval (i : Host.Input) (s : Host.State) :
    Frontend.bulk.eval (inputs i) (values s) = BitVec.ofBool s.bulk := by
  simp [Frontend.bulk, Host.State.bulk, Bool.or_assoc]

@[simp] theorem supported_eval (i : Host.Input) (s : Host.State) :
    Frontend.supported.eval (inputs i) (values s) = BitVec.ofBool s.supported := by
  simp [Frontend.supported, Host.State.supported, Bool.or_assoc]

@[simp] theorem headerValid_eval (i : Host.Input) (s : Host.State) :
    Frontend.headerValid.eval (inputs i) (values s) = BitVec.ofBool s.headerValid := by
  simp [Frontend.headerValid, Frontend.both, Expr.eval, values, Host.State.headerValid,
    Bool.beq_eq_decide_eq]
  rfl

@[simp] theorem closing_eval (i : Host.Input) (s : Host.State) :
    Frontend.closing.eval (inputs i) (values s) = BitVec.ofBool (s.closing i) := by
  simp [Frontend.closing, Frontend.both, Expr.eval, inputs, values, Host.State.closing, Bool.and_assoc]

@[simp] theorem taking_eval (i : Host.Input) (s : Host.State) :
    Frontend.taking.eval (inputs i) (values s) = BitVec.ofBool (s.taking i) := by
  simp [Frontend.taking, Frontend.rising, Frontend.both, Expr.eval, inputs, values,
    Host.State.taking, Bool.and_assoc]

@[simp] theorem receiving_eval (i : Host.Input) (s : Host.State) :
    Frontend.receiving.eval (inputs i) (values s) = BitVec.ofBool (s.receiving i) := by
  simp [Frontend.receiving, Frontend.both, Expr.eval, values, Host.State.receiving, Bool.and_assoc]

private theorem xor_bit_value : ∀ (x y : BitVec 1),
    x ^^^ y = BitVec.ofBool (x.getLsbD 0 != y.getLsbD 0) := by
  decide +kernel

@[simp] theorem crcBit_eval (i : Values Frontend.Input) (s : Values Frontend.Register)
    (crc : Frontend.E 16) (bit : Frontend.E 1) :
    (Frontend.crcBit crc bit).eval i s = Host.crcBit (crc.eval i s) ((bit.eval i s).getLsbD 0) := by
  simp only [Frontend.crcBit, Expr.eval, xor_eval, xor_bit_value,
    BitVec.getLsbD_extractLsb', Nat.add_zero, show decide (0 < 1) = true from rfl,
    Bool.true_and, ofBool_eq_one, Host.crcBit, BitVec.ofNat_eq_ofNat]

@[simp] theorem crcNibble_eval (i : Values Frontend.Input) (s : Values Frontend.Register)
    (crc : Frontend.E 16) (nibble : Frontend.E 4) :
    (Frontend.crcNibble crc nibble).eval i s = Host.crcNibble (crc.eval i s) (nibble.eval i s) := by
  simp [Frontend.crcNibble, Host.crcNibble, List.range_succ, Expr.eval]

@[simp] private theorem zero_extend (x : BitVec n) (m : Nat) :
    0#m ++ x = x.setWidth (m+n) := by
  apply BitVec.eq_of_getLsbD_eq
  intro k within
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_setWidth, within, decide_true, Bool.true_and]
  by_cases inside : k < n
  · simp [inside]
  · simp [inside, BitVec.getLsbD_of_ge x k (by omega)]

@[simp] theorem closingRequest_eval (i : Host.Input) (s : Host.State) :
    Frontend.closingRequest.eval (inputs i) (values s) = BitVec.ofBool (s.closingRequest i) := by
  simp [Frontend.closingRequest, Frontend.both, Expr.eval, values, Host.State.closingRequest]

@[simp] theorem closingReadExact_eval (i : Host.Input) (s : Host.State) :
    Frontend.closingReadExact.eval (inputs i) (values s) = BitVec.ofBool (s.closingReadExact i) := by
  simp [Frontend.closingReadExact, Frontend.both, Expr.eval, values, Host.State.closingReadExact,
    Bool.and_assoc, Bool.beq_eq_decide_eq]
  rfl

@[simp] theorem wireValid_eval (i : Host.Input) (s : Host.State) :
    Frontend.wireValid.eval (inputs i) (values s) = BitVec.ofBool s.wireValid := by
  simp [Frontend.wireValid, Frontend.both, Expr.eval, values, Host.State.wireValid,
    Bool.and_assoc, Bool.beq_eq_decide_eq]
  rfl

@[simp] theorem duplicate_eval (i : Host.Input) (s : Host.State) :
    Frontend.duplicate.eval (inputs i) (values s) = BitVec.ofBool s.duplicate := by
  simp [Frontend.duplicate, Frontend.both, Expr.eval, values, Host.State.duplicate,
    Bool.and_assoc, Bool.beq_eq_decide_eq]
  rfl

@[simp] theorem sequenceNew_eval (i : Host.Input) (s : Host.State) :
    Frontend.sequenceNew.eval (inputs i) (values s) = BitVec.ofBool s.sequenceNew := by
  simp [Frontend.sequenceNew, Frontend.both, Expr.eval, values, Host.State.sequenceNew,
    bne_eq, Bool.beq_eq_decide_eq]
  rfl

@[simp] theorem exportEnd_eval (i : Host.Input) (s : Host.State) :
    Frontend.exportEnd.eval (inputs i) (values s) = s.exportEnd := by
  simp [Frontend.exportEnd, Expr.eval, values, Host.State.exportEnd]
  exact zero_extend s.exportBits 9

@[simp] theorem unacknowledged_eval (i : Host.Input) (s : Host.State) :
    Frontend.unacknowledged.eval (inputs i) (values s) = BitVec.ofBool s.unacknowledged := by
  simp [Frontend.unacknowledged, Expr.eval, values, Host.State.unacknowledged,
    bne_eq, Bool.beq_eq_decide_eq]

@[simp] theorem payloadCanonical_eval (i : Host.Input) (s : Host.State) :
    Frontend.payloadCanonical.eval (inputs i) (values s) = BitVec.ofBool s.payloadCanonical := by
  simp [Frontend.payloadCanonical, Frontend.reserved, Expr.eval, Host.State.payloadCanonical,
    Bool.beq_eq_decide_eq]
  rfl

@[simp] theorem closingCode_eval (i : Host.Input) (s : Host.State) :
    Frontend.closingCode.eval (inputs i) (values s) = s.closingCode := by
  simp [Frontend.closingCode, Frontend.both, Expr.eval, values, Host.State.closingCode,
    bne_eq, Bool.beq_eq_decide_eq]
  by_cases count : s.count = 44#7 <;> by_cases crc : s.requestCRC = 0#16 <;> simp_all

@[simp] theorem ownerTag_eval (i : Host.Input) (s : Host.State) :
    Frontend.ownerTag.eval (inputs i) (values s) = i.status.ownerTag := rfl

@[simp] theorem requestedBits_eval (i : Host.Input) (s : Host.State) :
    Frontend.requestedBits.eval (inputs i) (values s) = s.requestedBits := by
  simp [Frontend.requestedBits, Expr.eval, Host.State.requestedBits, Bool.beq_eq_decide_eq]

@[simp] theorem wanted_eval (i : Host.Input) (s : Host.State) :
    Frontend.wanted.eval (inputs i) (values s) = s.wanted i.status := by
  simp [Frontend.wanted, Frontend.room, Expr.eval, statusValues, Host.State.wanted,
    ← BitVec.setWidth_eq_extractLsb']
  rw [zero_extend s.requestedBits 9]
  simp [BitVec.toNat_setWidth, Nat.mod_eq_of_lt
    (Nat.lt_trans s.requestedBits.isLt (by decide : 128 < 65536))]

@[simp] theorem beatsNeeded_eval (i : Host.Input) (s : Host.State) :
    Frontend.beatsNeeded.eval (inputs i) (values s) = s.beatsNeeded i.status := by
  simp [Frontend.beatsNeeded, Expr.eval, Host.State.beatsNeeded, Bool.beq_eq_decide_eq]

private theorem fold_and_eval (i : Values Frontend.Input) (s : Values Frontend.Register)
    (items : List α) (expressions : α → Frontend.E 1) (predicate : α → Bool)
    (accumulator : Frontend.E 1) (initial : Bool)
    (initialValue : accumulator.eval i s = BitVec.ofBool initial)
    (each : ∀ item ∈ items, (expressions item).eval i s = BitVec.ofBool (predicate item)) :
    (items.foldl (fun acc item => Frontend.both acc (expressions item)) accumulator).eval i s =
      BitVec.ofBool (initial && items.all predicate) := by
  induction items generalizing accumulator initial with
  | nil => simpa using initialValue
  | cons item items induction =>
    have head := each item (by simp)
    have tail : ∀ item ∈ items, (expressions item).eval i s = BitVec.ofBool (predicate item) :=
      fun value member => each value (by simp [member])
    have next := induction (Frontend.both accumulator (expressions item)) (initial && predicate item)
      (by simp [Frontend.both, Expr.eval, initialValue, head]) tail
    simpa [Bool.and_assoc] using next

@[simp] theorem tailCanonical_eval (i : Host.Input) (s : Host.State) :
    Frontend.tailCanonical.eval (inputs i) (values s) = BitVec.ofBool (s.tailCanonical i.status) := by
  rw [Frontend.tailCanonical_eval_fold]
  have each : ∀ k : Fin 64,
      (Frontend.either (.inv (.ult Frontend.wanted (.lit (BitVec.ofNat 7 (64-k.val)))))
        (.zero (Frontend.payload k.val 1 (by omega)))).eval (inputs i) (values s) =
        BitVec.ofBool (!decide ((s.wanted i.status).toNat < 64-k.val) || s.payload k.val 1 == 0) := by
    intro k
    simp [Expr.eval, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : 64-k.val < 128),
      Bool.beq_eq_decide_eq]
    rfl
  simpa only [Host.State.tailCanonical, Bool.true_and] using
    fold_and_eval (inputs i) (values s) (List.finRange 64)
      (fun k => Frontend.either (.inv (.ult Frontend.wanted (.lit (BitVec.ofNat 7 (64-k.val)))))
        (.zero (Frontend.payload k.val 1 (by omega))))
      (fun k => !decide ((s.wanted i.status).toNat < 64-k.val) || s.payload k.val 1 == 0)
      (.lit 1) true rfl (fun k _ => each k)

@[simp] theorem bulkOwner_eval (i : Host.Input) (s : Host.State) :
    Frontend.bulkOwner.eval (inputs i) (values s) = BitVec.ofBool (s.bulkOwner i.status) := by
  simp [Frontend.bulkOwner, Frontend.both, Expr.eval, statusValues, Host.State.bulkOwner,
    Bool.beq_eq_decide_eq]
  all_goals rfl

@[simp] theorem bulkOffsets_eval (i : Host.Input) (s : Host.State) :
    Frontend.bulkOffsets.eval (inputs i) (values s) = BitVec.ofBool (s.bulkOffsets i.status) := by
  simp [Frontend.bulkOffsets, Frontend.both, Expr.eval, statusValues, Host.State.bulkOffsets,
    Bool.beq_eq_decide_eq]
  all_goals rfl

@[simp] theorem bulkAdmitted_eval (i : Host.Input) (s : Host.State) :
    Frontend.bulkAdmitted.eval (inputs i) (values s) = BitVec.ofBool (s.bulkAdmitted i.status) := by
  simp [Frontend.bulkAdmitted, Frontend.both, Expr.eval, statusValues, Host.State.bulkAdmitted,
    Bool.and_assoc, Bool.beq_eq_decide_eq]
  all_goals rfl

@[simp] theorem admittingBulk_eval (i : Host.Input) (s : Host.State) :
    Frontend.admittingBulk.eval (inputs i) (values s) = BitVec.ofBool (s.admittingBulk i.status) := by
  simp [Frontend.admittingBulk, Frontend.both, Expr.eval, Host.State.admittingBulk, Bool.and_assoc]

@[simp] theorem delivering_eval (i : Host.Input) (s : Host.State) :
    Frontend.delivering.eval (inputs i) (values s) = BitVec.ofBool s.delivering := by
  simp [Frontend.delivering, Frontend.both, Expr.eval, values, Host.State.delivering,
    Bool.and_assoc, Bool.beq_eq_decide_eq]
  all_goals rfl

@[simp] theorem clearingExport_eval (i : Host.Input) (s : Host.State) :
    Frontend.clearingExport.eval (inputs i) (values s) = BitVec.ofBool (s.clearingExport i.status) := by
  simp [Frontend.clearingExport, Frontend.both, Expr.eval, statusValues, Host.State.clearingExport,
    Bool.and_assoc, Bool.or_assoc]

@[simp] theorem stagedTX_eval (i : Host.Input) (s : Host.State) :
    Frontend.stagedTX.eval (inputs i) (values s) = BitVec.ofBool s.stagedTX := by
  simp [Frontend.stagedTX, Frontend.both, Expr.eval, values, Host.State.stagedTX,
    bne_eq, Bool.beq_eq_decide_eq]
  rfl

@[simp] theorem stagedRX_eval (i : Host.Input) (s : Host.State) :
    Frontend.stagedRX.eval (inputs i) (values s) = BitVec.ofBool s.stagedRX := by
  simp [Frontend.stagedRX, Frontend.both, Expr.eval, values, Host.State.stagedRX]

@[simp] theorem stagedBits_eval (i : Host.Input) (s : Host.State) :
    Frontend.stagedBits.eval (inputs i) (values s) = s.stagedBits := by
  simp [Frontend.stagedBits, Expr.eval, values, Host.State.stagedBits, ← BitVec.setWidth_eq_extractLsb']

@[simp] theorem stageRejected_eval (i : Host.Input) (s : Host.State) :
    Frontend.stageRejected.eval (inputs i) (values s) = BitVec.ofBool (s.stageRejected i.status) := by
  simp [Frontend.stageRejected, Frontend.both, Expr.eval, statusValues, Host.State.stageRejected, Bool.and_assoc]

@[simp] theorem stageDone_eval (i : Host.Input) (s : Host.State) :
    Frontend.stageDone.eval (inputs i) (values s) = BitVec.ofBool s.stageDone := by
  simp [Frontend.stageDone, Frontend.both, Expr.eval, values, Host.State.stageDone,
    Bool.beq_eq_decide_eq]
  all_goals rfl

@[simp] theorem finishingCRC_eval (i : Host.Input) (s : Host.State) :
    Frontend.finishingCRC.eval (inputs i) (values s) = BitVec.ofBool s.finishingCRC := by
  simp [Frontend.finishingCRC, Frontend.both, Expr.eval, values, Host.State.finishingCRC,
    Bool.beq_eq_decide_eq]
  all_goals rfl

@[simp] theorem nextCRC_eval (i : Host.Input) (s : Host.State) :
    Frontend.nextCRC.eval (inputs i) (values s) = s.nextCRC := by
  simp [Frontend.nextCRC, Host.State.nextCRC, Expr.eval, values]

@[simp] theorem completedFrame_eval (i : Host.Input) (s : Host.State) :
    Frontend.completedFrame.eval (inputs i) (values s) = s.completedFrame := by
  simp [Frontend.completedFrame, Host.State.completedFrame, Expr.eval, values]

@[simp] theorem responseFlags_eval (i : Host.Input) (s : Host.State) :
    Frontend.responseFlags.eval (inputs i) (values s) = s.responseFlags i.status := by
  simp [Frontend.responseFlags, Host.State.responseFlags, Expr.eval, values, statusValues,
    Bool.beq_eq_decide_eq]
  all_goals rfl

@[simp] theorem responseLogical_eval (i : Host.Input) (s : Host.State) :
    Frontend.responseLogical.eval (inputs i) (values s) = s.responseLogical i.status := by
  simp [Frontend.responseLogical, Host.State.responseLogical, Expr.eval, values, statusValues]

@[simp] private theorem extend_1_6 (x : BitVec 6) : 0#1 ++ x = x.setWidth 7 := zero_extend x 1
@[simp] private theorem extend_32_32 (x : BitVec 32) : 0#32 ++ x = x.setWidth 64 := zero_extend x 32

theorem step_correct (i : Host.Input) (s : Host.State) (register : Frontend.Register w) :
    Frontend.circuit.step (inputs i) (values s) register = values (Host.step i s) register := by
  cases reset : i.initialize <;> cases register <;>
    simp [Frontend.circuit, Circuit.step, Frontend.next, Frontend.nextRaw, Expr.eval,
      Frontend.both, inputs, values, Host.step, reset, statusValues, bne_eq,
      Bool.beq_eq_decide_eq, Bool.and_assoc, Bool.or_assoc]
  all_goals rfl

theorem coreInput_eval (i : Host.Input) (s : Host.State) (port : Core.Input w) :
    (Frontend.coreInput port).eval (inputs i) (values s) = commandValues (s.command i) port := by
  cases port <;> simp [Frontend.coreInput, Expr.eval, inputs, values,
    commandValues, Host.State.command, Bool.beq_eq_decide_eq]
  all_goals rfl

theorem miso_eval (i : Host.Input) (s : Host.State) :
    Frontend.miso.eval (inputs i) (values s) = s.miso i := by
  simp [Frontend.miso, Frontend.both, Expr.eval, Execution.readTree_correct, inputs, values,
    Host.State.miso, and_assoc]
  split
  · have within : s.count.toNat < 64 := by omega
    simp_all [Nat.mod_eq_of_lt within, Expr.eval, values]
  · rfl

def outputs (i : Host.Input) (s : Host.State) : Values Frontend.Output := fun port => match port with
  | .core port => commandValues (s.command i) port
  | .miso => s.miso i
  | .ready => BitVec.ofBool (!i.initialize && s.ready)

theorem observe_correct (i : Host.Input) (s : Host.State) (port : Frontend.Output w) :
    Frontend.circuit.observe (inputs i) (values s) port = outputs i s port := by
  cases port with
  | core port => exact coreInput_eval i s port
  | miso => exact miso_eval i s
  | ready => simp [Frontend.circuit, Circuit.observe, Frontend.output, Expr.eval, inputs, values, outputs]

@[simp] private theorem bit_roundtrip : ∀ x : BitVec 1, BitVec.ofBool (x.getLsbD 0) = x := by
  decide +kernel

def statusFromValues (t : Values Core.Output) : Host.Status :=
  { valid := (t .valid).getLsbD 0, busy := (t .busy).getLsbD 0
    retained := (t .retained).getLsbD 0, rejected := (t .rejected).getLsbD 0
    fault := (t .fault).getLsbD 0, waitingRX := (t .waitingRX).getLsbD 0
    waitingTX := (t .waitingTX).getLsbD 0, pending := (t .pending).getLsbD 0
    stalled := (t .stalled).getLsbD 0
    generation := t .generation, transfer := t .transfer, total := t .total
    txAccepted := t .txAccepted, txFree := t .txFree, rxQueued := t .rxQueued
    rxPopped := t .rxPopped, rxData := t .rxData, rxBits := t .rxBits
    phase := t .phase, pc := t .pc, remaining := t .remaining
    levels := t .levels, enabled := t .enabled, txQueued := t .txQueued
    txConsumed := t .txConsumed, rxProduced := t .rxProduced
    stage1 := t .stage1, stage2 := t .stage2 }

def inputFromValues (i : Values Frontend.Input) : Host.Input :=
  { «initialize» := (i .initialize).getLsbD 0
    sck := (i .sck).getLsbD 0, csn := (i .csn).getLsbD 0
    mosi := i .mosi, rawInputs := i .rawInputs
    status := statusFromValues (fun p => i (.status p)) }

def stateFromValues (s : Values Frontend.Register) : Host.State :=
  { sckPrev := (s .sckPrev).getLsbD 0, csnPrev := (s .csnPrev).getLsbD 0
    active := (s .active).getLsbD 0, reading := (s .reading).getLsbD 0
    count := s .count, request := s .request, requestCRC := s .requestCRC
    phase := s .phase, code := s .code, sequence := s .sequence
    cacheReply := (s .cacheReply).getLsbD 0, response := s .response
    ready := (s .ready).getLsbD 0, lastValid := (s .lastValid).getLsbD 0
    lastRequest := s .lastRequest, lastReply := s .lastReply
    txLeft := s .txLeft, txStaging := s .txStaging
    rxPending := (s .rxPending).getLsbD 0, workBulk := (s .workBulk).getLsbD 0
    exportData := s .exportData, exportStart := s .exportStart, exportBits := s .exportBits
    ackOffset := s .ackOffset, replyLogical := s .replyLogical, crcWork := s .crcWork
    crc := s .crc, crcCount := s .crcCount }

theorem status_roundtrip (t : Values Core.Output) : @statusValues (statusFromValues t) = @t := by
  funext w port
  cases port <;> simp [statusValues, statusFromValues]
  all_goals exact bit_roundtrip _

theorem input_roundtrip (i : Values Frontend.Input) : @inputs (inputFromValues i) = @i := by
  funext w port
  cases port <;> simp [inputs, inputFromValues, status_roundtrip]
  all_goals exact bit_roundtrip _

theorem state_roundtrip (s : Values Frontend.Register) : @values (stateFromValues s) = @s := by
  funext w register
  cases register <;> simp [values, stateFromValues]
  all_goals exact bit_roundtrip _

theorem step_values (i : Host.Input) (s : Host.State) :
    @Circuit.step _ _ _ Frontend.circuit (inputs i) (values s) = @values (Host.step i s) := by
  funext w register
  exact step_correct i s register

/-- Every arbitrary raw startup has a concrete finite source state, by projection. -/
theorem step_fromRaw (i : Values Frontend.Input) (s : Values Frontend.Register) :
    @Circuit.step _ _ _ Frontend.circuit i s =
      @values (Host.step (inputFromValues i) (stateFromValues s)) := by
  simpa only [input_roundtrip, state_roundtrip] using
    step_values (inputFromValues i) (stateFromValues s)

def rawRun (s : Values Frontend.Register) (incoming : List (Values Frontend.Input)) :
    Values Frontend.Register := incoming.foldl (α := Values Frontend.Register)
      (fun s i => @Circuit.step _ _ _ Frontend.circuit i s) s

theorem run_correct (s : Host.State) (incoming : List Host.Input) :
    @rawRun (values s) (incoming.map fun i => @inputs i) = @values (Host.run s incoming) := by
  induction incoming generalizing s with
  | nil => rfl
  | cons i incoming induction =>
    change @rawRun (@Circuit.step _ _ _ Frontend.circuit (inputs i) (values s))
      (incoming.map fun i => @inputs i) = @values (Host.run (Host.step i s) incoming)
    rw [step_values]
    exact induction (Host.step i s)

theorem run_fromRaw (s : Values Frontend.Register) (incoming : List (Values Frontend.Input)) :
    @rawRun s incoming = @values (Host.run (stateFromValues s) (incoming.map inputFromValues)) := by
  have represented := run_correct (stateFromValues s) (incoming.map inputFromValues)
  simpa only [state_roundtrip, List.map_map, Function.comp_def, input_roundtrip, List.map_id_fun', id] using represented

end Pinwheel.Hardware.Streaming.HostCorrespondence
