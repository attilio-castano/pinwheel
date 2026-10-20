import Pinwheel.Hardware.Streaming.CoreEmit

/-! Four-lane sampled-pin host link. Stop-and-wait receipts are replayable;
exported RX custody survives rejected frames until a new admitted exchange
acknowledges its exact end. CRC computation uses four combinational steps and
48 bounded engine cycles per response, rather than an unrolled 192-bit network. -/
namespace Pinwheel.Hardware.Streaming.Frontend
open Pinwheel.Hardware

inductive Input : Nat → Type where
  | initialize : Input 1 | sck : Input 1 | csn : Input 1 | mosi : Input 4
  | rawInputs : Input 2
  | status : Core.Output w → Input w
inductive Output : Nat → Type where
  | core : Core.Input w → Output w
  | miso : Output 4 | ready : Output 1
inductive Register : Nat → Type where
  | sckPrev : Register 1 | csnPrev : Register 1
  | active : Register 1 | reading : Register 1 | count : Register 7
  | request : Register 176 | requestCRC : Register 16
  | phase : Register 3 | code : Register 4 | sequence : Register 16 | cacheReply : Register 1
  | response : Register 208 | ready : Register 1
  | lastValid : Register 1 | lastRequest : Register 176 | lastReply : Register 208
  | txLeft : Register 7 | txStaging : Register 64 | rxPending : Register 1 | workBulk : Register 1
  | exportData : Register 64 | exportStart : Register 16 | exportBits : Register 7 | ackOffset : Register 16
  | replyLogical : Register 192 | crcWork : Register 192 | crc : Register 16 | crcCount : Register 6

abbrev E := Expr Input Register
def both (x y : E 1) : E 1 := .band x y
def either (x y : E w) : E w := .inv (.band (.inv x) (.inv y))
def xor (x y : E w) : E w := either (.band x (.inv y)) (.band (.inv x) y)
def inc (x : E w) : E w := .sub x (.lit (BitVec.ofNat w (2^w-1)))
def add (x y : E w) : E w := .sub x (.sub (.lit 0) y)
def status (o : Core.Output w) : E w := .input (.status o)
def isPhase (p : BitVec 3) : E 1 := .equal (.reg .phase) (.lit p)
def payload (start len : Nat) (fits : start+len ≤ 128) : E len :=
  .slice (16+start) len (by omega) (.reg .request)
def opcode : E 4 := .slice 160 4 (by decide) (.reg .request)
def op (n : BitVec 4) : E 1 := .equal opcode (.lit n)
def requestSequence : E 16 := .slice 144 16 (by decide) (.reg .request)
def bulk : E 1 := either (op 8) (either (op 9) (op 10))
def supported : E 1 := either bulk (either (op 1) (either (op 2)
  (either (op 3) (either (op 4) (op 7)))))
def headerValid : E 1 := both supported
  (.equal (.slice 164 12 (by decide) (.reg .request)) (.lit 0xA72))

def crcBit (crc : E 16) (bit : E 1) : E 16 :=
  let feedback := xor (.slice 15 1 (by decide) crc) bit
  let shifted := Expr.concat (a := 15) (b := 1) (.slice 0 15 (by decide) crc) (.lit 0)
  .mux feedback (xor shifted (.lit 0x1021)) shifted
def crcNibble (crc : E 16) (nibble : E 4) : E 16 :=
  (List.range 4).foldl (fun acc k => crcBit acc
    (.slice (3-k) 1 (by omega) nibble)) crc

def startingFrame : E 1 := both (.inv (.input .initialize)) (both (.inv (.reg .active))
  (both (isPhase 0) (both (.reg .csnPrev) (.inv (.input .csn)))))
def closing : E 1 := both (.reg .active) (both (.inv (.reg .csnPrev)) (.input .csn))
def rising : E 1 := both (.inv (.reg .sckPrev)) (.input .sck)
def taking : E 1 := both (.reg .active) (both (.inv (.input .csn)) rising)
def receiving : E 1 := both taking (both (.inv (.reg .reading)) (.ult (.reg .count) (.lit 44)))
def closingRequest : E 1 := both closing (.inv (.reg .reading))
def closingReadExact : E 1 := both closing (both (.reg .reading)
  (.equal (.reg .count) (.lit 52)))
def wireValid : E 1 := both (.equal (.reg .count) (.lit 44))
  (both (.zero (.reg .requestCRC)) headerValid)
def duplicate : E 1 := both wireValid (both (.reg .lastValid)
  (.equal (.reg .request) (.reg .lastRequest)))
def sequenceNew : E 1 := .mux (.reg .lastValid)
  (both (.inv (.equal (.slice 144 16 (by decide) (.reg .lastRequest)) (.lit 65535)))
    (.equal requestSequence (inc (.slice 144 16 (by decide) (.reg .lastRequest)))))
  (.zero requestSequence)
def exportEnd : E 16 := add (.reg .exportStart) (.concat (.lit (0 : BitVec 9)) (.reg Register.exportBits))
def unacknowledged : E 1 := .inv (.equal exportEnd (.reg .ackOffset))
def reserved (bits : Nat) (h : bits ≤ 128) : E 1 := .zero (payload 0 bits (by omega))
def payloadCanonical : E 1 := .mux (op 1) (reserved 58 (by decide))
  (.mux (op 2) (reserved 115 (by decide))
  (.mux (op 3) (reserved 96 (by decide))
  (.mux (op 4) (reserved 96 (by decide))
  (.mux (op 7) (reserved 128 (by decide))
  (.mux (op 8) (reserved 64 (by decide))
  (.mux (op 9) (reserved 32 (by decide)) (.lit 1)))))))
def closingCode : E 4 := .mux (.inv (.equal (.reg .count) (.lit 44))) (.lit 1)
  (.mux (.inv (.zero (.reg .requestCRC))) (.lit 3)
  (.mux (.inv headerValid) (.lit 2)
  (.mux (.inv sequenceNew) (.lit 4)
  (.mux (.inv payloadCanonical) (.lit 4)
  (.mux (both (op 4) unacknowledged) (.lit 5) (.lit 0))))))

def ownerTag : E 32 := .concat (status .generation) (status .transfer)
def requestedBits : E 7 := .mux (op 10) (.lit 64) (.mux (op 9) (.lit 32) (.lit 0))
def room : E 16 := .sub (status .total) (status .txAccepted)
def wanted : E 7 := .mux (.ult room (.concat (.lit (0 : BitVec 9)) requestedBits))
  (.slice 0 7 (by decide) room) requestedBits
def beatsNeeded : E 4 := .mux (.zero wanted) (.lit 0)
  (.mux (.ult (.lit 32) wanted) (.lit 2) (.lit 1))
def tailCondition (k : Fin 64) : E 1 :=
  (either (.inv (.ult wanted (.lit (BitVec.ofNat 7 (64-k.val)))))
    (.zero (payload k.val 1 (by omega))))
def tailCanonical : E 1 := BalancedConjunction.sixtyFour tailCondition

theorem tailCanonical_eval_fold (i : Values Input) (r : Values Register) :
    tailCanonical.eval i r = ((List.finRange 64).foldl (fun acc k => both acc
      (either (.inv (.ult wanted (.lit (BitVec.ofNat 7 (64-k.val)))))
        (.zero (payload k.val 1 (by omega))))) (.lit 1)).eval i r := by
  exact BalancedConjunction.sixtyFour_eval i r tailCondition
def bulkOwner : E 1 := both (either (status .busy) (status .retained))
  (.equal (payload 96 32 (by decide)) ownerTag)
def bulkOffsets : E 1 := both (.equal (payload 80 16 (by decide)) (status .txAccepted))
  (.equal (payload 64 16 (by decide)) exportEnd)
def bulkAdmitted : E 1 := both bulkOwner (both bulkOffsets (both tailCanonical
  (both (either (.zero wanted) (status .busy))
    (.inv (.ult (status .txFree) beatsNeeded)))))
def admittingBulk : E 1 := both (isPhase 1) (both bulk bulkAdmitted)
def delivering : E 1 := both (isPhase 1) (both (.inv bulk) (.zero (.reg .code)))
def clearingExport : E 1 := both delivering (both (.inv (status .rejected))
  (either (op 3) (either (op 4) (op 7))))
def stagedTX : E 1 := both (isPhase 2) (.inv (.zero (.reg .txLeft)))
def stagedRX : E 1 := both (isPhase 2) (.reg .rxPending)
def stagedBits : E 6 := .mux (.ult (.lit 32) (.reg .txLeft)) (.lit 32)
  (.slice 0 6 (by decide) (.reg .txLeft))
def stageRejected : E 1 := both (isPhase 2) (both (either stagedTX stagedRX) (status .rejected))
def stageDone : E 1 := both (.zero (.reg .txLeft)) (.inv (.reg .rxPending))
def finishingCRC : E 1 := both (isPhase 4) (.equal (.reg .crcCount) (.lit 47))
def nextCRC : E 16 := crcNibble (.reg .crc) (.slice 188 4 (by decide) (.reg .crcWork))
def completedFrame : E 208 := .concat (.reg .replyLogical) nextCRC

def responseFlags : E 8 := .concat (.lit (0 : BitVec 1))
  (.concat (status .waitingRX) (.concat (status .waitingTX)
  (.concat (.equal (.reg .code) (.lit 5)) (.concat (status .fault)
  (.concat (status .retained) (.concat (status .busy) (status .valid)))))))
def responseLogical : E 192 :=
  let data : E 64 := .mux (.reg .workBulk) (.reg .exportData) (.lit 0)
  let rxStart : E 16 := .mux (.reg .workBulk) (.reg .exportStart) (status .rxPopped)
  let rxBits : E 7 := .mux (.reg .workBulk) (.reg .exportBits) (.lit 0)
  .concat (.concat (.lit (0x5A2 : BitVec 12)) (.reg .code))
  (.concat (.reg .sequence) (.concat data (.concat ownerTag
  (.concat (status .txAccepted) (.concat rxStart (.concat rxBits
  (.concat (status .txFree) (.concat (status .rxQueued)
  (.concat responseFlags (.lit (0 : BitVec 9)))))))))))

def nextRaw : {w : Nat} → Register w → E w
  | _, .sckPrev => .input .sck
  | _, .csnPrev => .input .csn
  | _, .active => .mux startingFrame (.lit 1) (.mux closing (.lit 0) (.reg .active))
  | _, .reading => .mux startingFrame (.reg .ready) (.reg .reading)
  | _, .count => .mux startingFrame (.lit 0) (.mux taking
      (.mux (.ult (.reg .count) (.lit 127)) (inc (.reg .count)) (.reg .count)) (.reg .count))
  | _, .request => .mux (both startingFrame (.inv (.reg .ready))) (.lit 0)
      (.mux receiving (Expr.concat (a := 172) (b := 4)
        (.slice 0 172 (by decide) (.reg .request : E 176)) (.input .mosi : E 4)) (.reg .request))
  | _, .requestCRC => .mux (both startingFrame (.inv (.reg .ready))) (.lit 65535)
      (.mux receiving (crcNibble (.reg .requestCRC) (.input .mosi)) (.reg .requestCRC))
  | _, .phase => .mux closingRequest (.mux duplicate (.lit 0)
      (.mux (.zero closingCode) (.lit 1) (.lit 3)))
      (.mux (isPhase 1) (.mux bulk (.mux bulkAdmitted (.lit 2) (.lit 3)) (.lit 3))
      (.mux (isPhase 2) (.mux (either stageDone stageRejected) (.lit 3) (.lit 2))
      (.mux (isPhase 3) (.lit 4) (.mux finishingCRC (.lit 0) (.reg .phase)))))
  | _, .code => .mux closingRequest closingCode
      (.mux (isPhase 1) (.mux bulk (.mux tailCanonical
        (.mux bulkAdmitted (.lit 0) (.lit 5)) (.lit 4))
        (.mux (status .rejected) (.lit 5) (.reg .code)))
      (.mux stageRejected (.lit 5) (.reg .code)))
  | _, .sequence => .mux closingRequest requestSequence (.reg .sequence)
  | _, .cacheReply => .mux closingRequest (both wireValid (both sequenceNew (.inv duplicate))) (.reg .cacheReply)
  | _, .response => .mux (both closingRequest duplicate) (.reg .lastReply)
      (.mux finishingCRC completedFrame (.reg .response))
  | _, .ready => .mux (either (both closingRequest duplicate) finishingCRC) (.lit 1)
      (.mux closingReadExact (.lit 0) (.reg .ready))
  | _, .lastValid => .mux (both finishingCRC (.reg .cacheReply)) (.lit 1) (.reg .lastValid)
  | _, .lastRequest => .mux (both finishingCRC (.reg .cacheReply)) (.reg .request) (.reg .lastRequest)
  | _, .lastReply => .mux (both finishingCRC (.reg .cacheReply)) completedFrame (.reg .lastReply)
  | _, .txLeft => .mux admittingBulk wanted
      (.mux stagedTX (.sub (.reg .txLeft) (.concat (.lit (0 : BitVec 1)) stagedBits)) (.reg .txLeft))
  | _, .txStaging => .mux admittingBulk (payload 0 64 (by decide))
      (.mux stagedTX (.concat (.slice 0 32 (by decide) (.reg .txStaging)) (.lit (0 : BitVec 32))) (.reg .txStaging))
  | _, .rxPending => .mux admittingBulk (.inv (.zero (status .rxQueued)))
      (.mux stagedRX (.lit 0) (.reg .rxPending))
  | _, .workBulk => .mux closingRequest (.lit 0) (.mux admittingBulk (.lit 1) (.reg .workBulk))
  | _, .exportData => .mux clearingExport (.lit 0)
      (.mux admittingBulk (.lit 0) (.mux stagedRX (.concat (.lit (0 : BitVec 32)) (status .rxData)) (.reg .exportData)))
  | _, .exportStart => .mux clearingExport (.lit 0)
      (.mux admittingBulk (status .rxPopped) (.reg .exportStart))
  | _, .exportBits => .mux clearingExport (.lit 0)
      (.mux admittingBulk (.lit 0) (.mux stagedRX (.concat (.lit (0 : BitVec 1)) (status .rxBits)) (.reg .exportBits)))
  | _, .ackOffset => .mux clearingExport (.lit 0)
      (.mux admittingBulk (payload 64 16 (by decide)) (.reg .ackOffset))
  | _, .replyLogical => .mux (isPhase 3) responseLogical (.reg .replyLogical)
  | _, .crcWork => .mux (isPhase 3) responseLogical (.mux (isPhase 4)
      (.concat (.slice 0 188 (by decide) (.reg .crcWork)) (.lit (0 : BitVec 4))) (.reg .crcWork))
  | _, .crc => .mux (isPhase 3) (.lit 65535) (.mux (isPhase 4) nextCRC (.reg .crc))
  | _, .crcCount => .mux (isPhase 3) (.lit 0) (.mux (isPhase 4) (inc (.reg .crcCount)) (.reg .crcCount))

def next : {w : Nat} → Register w → E w
  | _, .sckPrev => .input .sck
  | _, .csnPrev => .input .csn
  | _, r => .mux (.input .initialize) (.lit 0) (nextRaw r)

def coreInput : {w : Nat} → Core.Input w → E w
  | _, .initialize => .input .initialize
  | _, .command => .mux delivering (.mux (op 7) (.lit 15) opcode) (.lit 0)
  | _, .address => payload 122 6 (by decide)
  | _, .word => payload 58 64 (by decide)
  | _, .count => payload 121 7 (by decide)
  | _, .idleLevels => payload 118 3 (by decide)
  | _, .idleEnabled => payload 115 3 (by decide)
  | _, .startCount => payload 96 16 (by decide)
  | _, .expectedGeneration => payload 112 16 (by decide)
  | _, .expectedTransfer => payload 96 16 (by decide)
  | _, .txPush => stagedTX
  | _, .txData => .slice 32 32 (by decide) (.reg .txStaging)
  | _, .txBits => stagedBits
  | _, .rxPop => stagedRX
  | _, .rawInputs => .input .rawInputs

def miso : E 4 := .mux (both (.inv (.input .initialize))
  (both (.reg .active) (both (.reg .reading) (.ult (.reg .count) (.lit 52)))))
  (Execution.readTree 6 (fun k => if h : k.toNat < 52 then
    .slice ((51-k.toNat)*4) 4 (by omega) (.reg .response) else .lit 0)
    (.slice 0 6 (by decide) (.reg .count))) (.lit 0)
def output : {w : Nat} → Output w → E w
  | _, .core p => coreInput p
  | _, .miso => miso
  | _, .ready => .mux (.input .initialize) (.lit 0) (.reg .ready)
def circuit : Circuit Input Register Output := ⟨next,output⟩

end Pinwheel.Hardware.Streaming.Frontend
