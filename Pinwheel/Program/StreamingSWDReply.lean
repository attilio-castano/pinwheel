import Std

/-! Chronological SWD read response bits and the host's DPIDR decoder. -/
namespace Pinwheel.Program.StreamingSWD

def okAck : List Bool := [true, false, false]

def wordBits (value : BitVec 32) : List Bool :=
  List.ofFn fun bit : Fin 32 => value.getLsbD bit.val

/-- Even parity transmits the XOR of the data bits. -/
def parity (bits : List Bool) : Bool := bits.foldl Bool.xor false

def replyBits (value : BitVec 32) : List Bool :=
  okAck ++ wordBits value ++ [parity (wordBits value)]

def badParityBits (value : BitVec 32) : List Bool :=
  okAck ++ wordBits value ++ [!parity (wordBits value)]

def decodeWord (bits : List Bool) : BitVec 32 :=
  (BitVec.ofBoolListLE bits).setWidth 32

/-- Decode the complete reply after the two released-wire turnarounds have
    been excluded by the clocked capture schedule. -/
def decodeReply (bits : List Bool) : Option (BitVec 32) :=
  match bits with
  | true :: false :: false :: body =>
    let data := body.take 32
    match body.drop 32 with
    | [receivedParity] =>
      if receivedParity = parity data then some (decodeWord data) else none
    | _ => none
  | _ => none

@[simp] theorem wordBits_length (value : BitVec 32) : (wordBits value).length = 32 := by
  simp [wordBits]

@[simp] theorem replyBits_length (value : BitVec 32) : (replyBits value).length = 36 := by
  simp [replyBits,okAck]

@[simp] theorem badParityBits_length (value : BitVec 32) : (badParityBits value).length = 36 := by
  simp [badParityBits,okAck]

theorem decode_wordBits (value : BitVec 32) : decodeWord (wordBits value) = value := by
  apply BitVec.eq_of_getLsbD_eq
  intro bit valid
  simp only [decodeWord,BitVec.getLsbD_setWidth,valid,decide_true,Bool.true_and,
    BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,wordBits,List.getElem?_ofFn,
    dif_pos True.intro,Option.getD_some]

theorem decode_reply (value : BitVec 32) : decodeReply (replyBits value) = some value := by
  unfold replyBits okAck
  simp only [List.cons_append,List.nil_append,decodeReply]
  rw [List.take_append_of_le_length (by simp),List.take_of_length_le (by simp),
    show (wordBits value ++ [parity (wordBits value)]).drop 32 = [parity (wordBits value)] by
      rw [← wordBits_length value]
      exact List.drop_append_length]
  simp [decode_wordBits]

theorem decode_badParity (value : BitVec 32) : decodeReply (badParityBits value) = none := by
  unfold badParityBits okAck
  simp only [List.cons_append,List.nil_append,decodeReply]
  rw [List.take_append_of_le_length (by simp),List.take_of_length_le (by simp),
    show (wordBits value ++ [!parity (wordBits value)]).drop 32 = [!parity (wordBits value)] by
      rw [← wordBits_length value]
      exact List.drop_append_length]
  cases parity (wordBits value) <;> rfl

end Pinwheel.Program.StreamingSWD
