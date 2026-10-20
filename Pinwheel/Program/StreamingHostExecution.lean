import Pinwheel.Program.StreamingOwnership

/-! A bounded stop-and-wait host-link machine. Frame assembly, validation,
staging, replay and exported ownership are source actions, independent of Expr. -/
namespace Pinwheel.Program.Streaming.Host

structure Status where
  valid : Bool := false
  busy : Bool := false
  retained : Bool := false
  rejected : Bool := false
  fault : Bool := false
  waitingRX : Bool := false
  waitingTX : Bool := false
  pending : Bool := false
  stalled : Bool := false
  generation : BitVec 16 := 0
  transfer : BitVec 16 := 0
  total : BitVec 16 := 0
  txAccepted : BitVec 16 := 0
  txFree : BitVec 4 := 0
  rxQueued : BitVec 4 := 0
  rxPopped : BitVec 16 := 0
  rxData : BitVec 32 := 0
  rxBits : BitVec 6 := 0
  phase : BitVec 3 := 0
  pc : BitVec 7 := 0
  remaining : BitVec 16 := 0
  levels : BitVec 3 := 0
  enabled : BitVec 3 := 0
  txQueued : BitVec 4 := 0
  txConsumed : BitVec 16 := 0
  rxProduced : BitVec 16 := 0
  stage1 : BitVec 2 := 0
  stage2 : BitVec 2 := 0
  deriving DecidableEq, Repr

structure Input where
  «initialize» : Bool := false
  sck : Bool := false
  csn : Bool := true
  mosi : BitVec 4 := 0
  rawInputs : BitVec 2 := 0
  status : Status := {}
  deriving DecidableEq, Repr

structure State where
  sckPrev : Bool := false
  csnPrev : Bool := false
  active : Bool := false
  reading : Bool := false
  count : BitVec 7 := 0
  request : BitVec 176 := 0
  requestCRC : BitVec 16 := 0
  phase : BitVec 3 := 0
  code : BitVec 4 := 0
  sequence : BitVec 16 := 0
  cacheReply : Bool := false
  response : BitVec 208 := 0
  ready : Bool := false
  lastValid : Bool := false
  lastRequest : BitVec 176 := 0
  lastReply : BitVec 208 := 0
  txLeft : BitVec 7 := 0
  txStaging : BitVec 64 := 0
  rxPending : Bool := false
  workBulk : Bool := false
  exportData : BitVec 64 := 0
  exportStart : BitVec 16 := 0
  exportBits : BitVec 7 := 0
  ackOffset : BitVec 16 := 0
  replyLogical : BitVec 192 := 0
  crcWork : BitVec 192 := 0
  crc : BitVec 16 := 0
  crcCount : BitVec 6 := 0
  deriving DecidableEq, Repr

def State.payload (s : State) (start len : Nat) : BitVec len := s.request.extractLsb' (16 + start) len
def State.opcode (s : State) : BitVec 4 := s.request.extractLsb' 160 4
def State.requestSequence (s : State) : BitVec 16 := s.request.extractLsb' 144 16
def State.bulk (s : State) : Bool := s.opcode == 8 || s.opcode == 9 || s.opcode == 10
def State.supported (s : State) : Bool :=
  s.bulk || s.opcode == 1 || s.opcode == 2 || s.opcode == 3 || s.opcode == 4 || s.opcode == 7
def State.headerValid (s : State) : Bool := s.supported && s.request.extractLsb' 164 12 == 0xA72

/-- Polynomial0x1021, most-significant bit first; no table or native computation is trusted. -/
def crcBit (crc : BitVec 16) (bit : Bool) : BitVec 16 :=
  let shifted := crc.extractLsb' 0 15 ++ 0#1
  if crc.getLsbD 15 != bit then shifted ^^^ 0x1021 else shifted

def crcNibble (crc : BitVec 16) (nibble : BitVec 4) : BitVec 16 :=
  (List.range 4).foldl (fun acc k => crcBit acc (nibble.getLsbD (3-k))) crc

def State.startingFrame (s : State) (i : Input) : Bool :=
  !i.initialize && !s.active && s.phase == 0 && s.csnPrev && !i.csn
def State.closing (s : State) (i : Input) : Bool := s.active && !s.csnPrev && i.csn
def State.taking (s : State) (i : Input) : Bool := s.active && !i.csn && !s.sckPrev && i.sck
def State.receiving (s : State) (i : Input) : Bool := s.taking i && !s.reading && decide (s.count.toNat < 44)
def State.closingRequest (s : State) (i : Input) : Bool := s.closing i && !s.reading
def State.closingReadExact (s : State) (i : Input) : Bool := s.closing i && s.reading && s.count == 52
def State.wireValid (s : State) : Bool := s.count == 44 && s.requestCRC == 0 && s.headerValid
def State.duplicate (s : State) : Bool := s.wireValid && s.lastValid && s.request == s.lastRequest
def State.sequenceNew (s : State) : Bool :=
  if s.lastValid then s.lastRequest.extractLsb' 144 16 != 65535 &&
    s.requestSequence == s.lastRequest.extractLsb' 144 16 + 1
  else s.requestSequence == 0
def State.exportEnd (s : State) : BitVec 16 := s.exportStart + s.exportBits.setWidth 16
def State.unacknowledged (s : State) : Bool := s.exportEnd != s.ackOffset
def State.payloadCanonical (s : State) : Bool :=
  if s.opcode == 1 then s.payload 0 58 == 0
  else if s.opcode == 2 then s.payload 0 115 == 0
  else if s.opcode == 3 then s.payload 0 96 == 0
  else if s.opcode == 4 then s.payload 0 96 == 0
  else if s.opcode == 7 then s.payload 0 128 == 0
  else if s.opcode == 8 then s.payload 0 64 == 0
  else if s.opcode == 9 then s.payload 0 32 == 0
  else true
def State.closingCode (s : State) : BitVec 4 :=
  if s.count != 44 then 1
  else if s.requestCRC != 0 then 3
  else if !s.headerValid then 2
  else if !s.sequenceNew then 4
  else if !s.payloadCanonical then 4
  else if s.opcode == 4 && s.unacknowledged then 5
  else 0

def Status.ownerTag (t : Status) : BitVec 32 := t.generation ++ t.transfer
def State.requestedBits (s : State) : BitVec 7 := if s.opcode == 10 then 64 else if s.opcode == 9 then 32 else 0
def State.wanted (s : State) (t : Status) : BitVec 7 :=
  let room := t.total - t.txAccepted
  if room.toNat < s.requestedBits.toNat then room.setWidth 7 else s.requestedBits
def State.beatsNeeded (s : State) (t : Status) : BitVec 4 :=
  if s.wanted t == 0 then 0 else if 32 < (s.wanted t).toNat then 2 else 1
def State.tailCanonical (s : State) (t : Status) : Bool :=
  (List.finRange 64).all fun k =>
    !decide ((s.wanted t).toNat < 64-k.val) || s.payload k.val 1 == 0
def State.bulkOwner (s : State) (t : Status) : Bool :=
  (t.busy || t.retained) && s.payload 96 32 == t.ownerTag
def State.bulkOffsets (s : State) (t : Status) : Bool :=
  s.payload 80 16 == t.txAccepted && s.payload 64 16 == s.exportEnd
def State.bulkAdmitted (s : State) (t : Status) : Bool :=
  s.bulkOwner t && s.bulkOffsets t && s.tailCanonical t &&
    (s.wanted t == 0 || t.busy) &&
    !decide (t.txFree.toNat < (s.beatsNeeded t).toNat)
def State.admittingBulk (s : State) (t : Status) : Bool := s.phase == 1 && s.bulk && s.bulkAdmitted t
def State.delivering (s : State) : Bool := s.phase == 1 && !s.bulk && s.code == 0
def State.clearingExport (s : State) (t : Status) : Bool :=
  s.delivering && !t.rejected && (s.opcode == 3 || s.opcode == 4 || s.opcode == 7)
def State.stagedTX (s : State) : Bool := s.phase == 2 && s.txLeft != 0
def State.stagedRX (s : State) : Bool := s.phase == 2 && s.rxPending
def State.stagedBits (s : State) : BitVec 6 := if 32 < s.txLeft.toNat then 32 else s.txLeft.setWidth 6
def State.stageRejected (s : State) (t : Status) : Bool :=
  s.phase == 2 && (s.stagedTX || s.stagedRX) && t.rejected
def State.stageDone (s : State) : Bool := s.txLeft == 0 && !s.rxPending
def State.finishingCRC (s : State) : Bool := s.phase == 4 && s.crcCount == 47
def State.nextCRC (s : State) : BitVec 16 := crcNibble s.crc (s.crcWork.extractLsb' 188 4)
def State.completedFrame (s : State) : BitVec 208 := s.replyLogical ++ s.nextCRC

def State.responseFlags (s : State) (t : Status) : BitVec 8 :=
  0#1 ++ (BitVec.ofBool t.waitingRX ++ (BitVec.ofBool t.waitingTX ++
    (BitVec.ofBool (s.code == 5) ++ (BitVec.ofBool t.fault ++
    (BitVec.ofBool t.retained ++ (BitVec.ofBool t.busy ++ BitVec.ofBool t.valid))))))

def State.responseLogical (s : State) (t : Status) : BitVec 192 :=
  let data := if s.workBulk then s.exportData else 0#64
  let rxStart := if s.workBulk then s.exportStart else t.rxPopped
  let rxBits := if s.workBulk then s.exportBits else 0#7
  (0x5A2#12 ++ s.code) ++ (s.sequence ++ (data ++ (t.ownerTag ++ (t.txAccepted ++ (rxStart ++
    (rxBits ++ (t.txFree ++ (t.rxQueued ++ (s.responseFlags t ++ 0#9)))))))))

/-- One physical sample edge, including edges during CRC work and host stalls. -/
def step (i : Input) (s : State) : State :=
  if i.initialize then {sckPrev := i.sck, csnPrev := i.csn}
  else
    { sckPrev := i.sck
      csnPrev := i.csn
      active := if s.startingFrame i then true else if s.closing i then false else s.active
      reading := if s.startingFrame i then s.ready else s.reading
      count := if s.startingFrame i then 0 else if s.taking i then
        (if s.count.toNat < 127 then s.count + 1 else s.count) else s.count
      request := if s.startingFrame i && !s.ready then 0 else if s.receiving i then
        s.request.extractLsb' 0 172 ++ i.mosi else s.request
      requestCRC := if s.startingFrame i && !s.ready then 65535 else if s.receiving i then
        crcNibble s.requestCRC i.mosi else s.requestCRC
      phase := if s.closingRequest i then (if s.duplicate then 0 else if s.closingCode == 0 then 1 else 3)
        else if s.phase == 1 then (if s.bulk then (if s.bulkAdmitted i.status then 2 else 3) else 3)
        else if s.phase == 2 then (if s.stageDone || s.stageRejected i.status then 3 else 2)
        else if s.phase == 3 then 4 else if s.finishingCRC then 0 else s.phase
      code := if s.closingRequest i then s.closingCode else if s.phase == 1 then
        (if s.bulk then (if s.tailCanonical i.status then (if s.bulkAdmitted i.status then 0 else 5) else 4)
          else if i.status.rejected then 5 else s.code)
        else if s.stageRejected i.status then 5 else s.code
      sequence := if s.closingRequest i then s.requestSequence else s.sequence
      cacheReply := if s.closingRequest i then s.wireValid && s.sequenceNew && !s.duplicate else s.cacheReply
      response := if s.closingRequest i && s.duplicate then s.lastReply
        else if s.finishingCRC then s.completedFrame else s.response
      ready := if (s.closingRequest i && s.duplicate) || s.finishingCRC then true
        else if s.closingReadExact i then false else s.ready
      lastValid := if s.finishingCRC && s.cacheReply then true else s.lastValid
      lastRequest := if s.finishingCRC && s.cacheReply then s.request else s.lastRequest
      lastReply := if s.finishingCRC && s.cacheReply then s.completedFrame else s.lastReply
      txLeft := if s.admittingBulk i.status then s.wanted i.status else if s.stagedTX then
        s.txLeft - (s.stagedBits.setWidth 7) else s.txLeft
      txStaging := if s.admittingBulk i.status then s.payload 0 64 else if s.stagedTX then
        s.txStaging.extractLsb' 0 32 ++ 0#32 else s.txStaging
      rxPending := if s.admittingBulk i.status then i.status.rxQueued != 0 else if s.stagedRX then false else s.rxPending
      workBulk := if s.closingRequest i then false else if s.admittingBulk i.status then true else s.workBulk
      exportData := if s.clearingExport i.status then 0 else if s.admittingBulk i.status then 0
        else if s.stagedRX then i.status.rxData.setWidth 64 else s.exportData
      exportStart := if s.clearingExport i.status then 0 else if s.admittingBulk i.status then i.status.rxPopped else s.exportStart
      exportBits := if s.clearingExport i.status then 0 else if s.admittingBulk i.status then 0
        else if s.stagedRX then i.status.rxBits.setWidth 7 else s.exportBits
      ackOffset := if s.clearingExport i.status then 0 else if s.admittingBulk i.status then s.payload 64 16 else s.ackOffset
      replyLogical := if s.phase == 3 then s.responseLogical i.status else s.replyLogical
      crcWork := if s.phase == 3 then s.responseLogical i.status else if s.phase == 4 then
        s.crcWork.extractLsb' 0 188 ++ 0#4 else s.crcWork
      crc := if s.phase == 3 then 65535 else if s.phase == 4 then s.nextCRC else s.crc
      crcCount := if s.phase == 3 then 0 else if s.phase == 4 then s.crcCount + 1 else s.crcCount }

structure Command where
  runtime : Streaming.Input := {}
  address : BitVec 6 := 0
  word : BitVec 64 := 0
  count : BitVec 7 := 0
  idle : Engine.Reactive.Pins := {}
  deriving DecidableEq, Repr

def State.command (s : State) (i : Input) : Command :=
  { runtime :=
      { «initialize» := i.initialize
        command := if s.delivering then (if s.opcode == 7 then 15 else s.opcode) else 0
        startCount := s.payload 96 16
        expectedGeneration := s.payload 112 16
        expectedTransfer := s.payload 96 16
        txPush := s.stagedTX
        rxPop := s.stagedRX
        txData := s.txStaging.extractLsb' 32 32
        txBits := s.stagedBits
        rawInputs := i.rawInputs }
    address := s.payload 122 6
    word := s.payload 58 64
    count := s.payload 121 7
    idle := ⟨s.payload 118 3, s.payload 115 3⟩ }

def State.miso (s : State) (i : Input) : BitVec 4 :=
  if !i.initialize && s.active && s.reading && decide (s.count.toNat < 52) then
    s.response.extractLsb' ((51-s.count.toNat)*4) 4 else 0

def run (s : State) (inputs : List Input) : State := inputs.foldl (fun s i => step i s) s

end Pinwheel.Program.Streaming.Host
