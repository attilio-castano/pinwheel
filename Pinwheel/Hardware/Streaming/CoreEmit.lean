import Pinwheel.Hardware.Streaming.Core

namespace Pinwheel.Hardware.Streaming.Core
open Pinwheel.Hardware

def inputs : Array (Sigma Input) :=
  #[⟨1, .initialize⟩, ⟨4, .command⟩, ⟨6, .address⟩, ⟨64, .word⟩, ⟨7, .count⟩, ⟨3, .idleLevels⟩, ⟨3, .idleEnabled⟩, ⟨16, .startCount⟩, ⟨16, .expectedGeneration⟩, ⟨16, .expectedTransfer⟩, ⟨1, .txPush⟩, ⟨32, .txData⟩, ⟨6, .txBits⟩, ⟨1, .rxPop⟩, ⟨2, .rawInputs⟩]
def outputs : Array (Sigma Output) :=
  #[⟨1, .valid⟩, ⟨1, .busy⟩, ⟨1, .retained⟩, ⟨1, .pending⟩, ⟨1, .rejected⟩, ⟨1, .stalled⟩, ⟨1, .fault⟩, ⟨1, .waitingTX⟩, ⟨1, .waitingRX⟩, ⟨16, .generation⟩, ⟨16, .transfer⟩, ⟨3, .phase⟩, ⟨7, .pc⟩, ⟨16, .remaining⟩, ⟨16, .total⟩, ⟨3, .levels⟩, ⟨3, .enabled⟩, ⟨4, .txFree⟩, ⟨4, .txQueued⟩, ⟨4, .rxQueued⟩, ⟨32, .rxData⟩, ⟨6, .rxBits⟩, ⟨16, .txAccepted⟩, ⟨16, .txConsumed⟩, ⟨16, .rxProduced⟩, ⟨16, .rxPopped⟩, ⟨2, .stage1⟩, ⟨2, .stage2⟩]
def registers (a : Nat) : Array (Sigma (Register a)) :=
  (List.finRange 64).toArray.map (fun k => ⟨64, .word (BitVec.ofNat 6 k.val)⟩) ++
  (List.finRange (2^a)).toArray.flatMap (fun k =>
    let j := BitVec.ofNat a k.val
    #[⟨32, .txWord j⟩, ⟨6, .txBits j⟩, ⟨32, .rxWord j⟩, ⟨6, .rxBits j⟩]) ++
  #[⟨64, .written⟩, ⟨1, .pending⟩, ⟨1, .valid⟩, ⟨7, .count⟩, ⟨3, .idleLevels⟩, ⟨3, .idleEnabled⟩, ⟨16, .generation⟩, ⟨16, .transfer⟩, ⟨3, .phase⟩, ⟨7, .pc⟩, ⟨64, .currentWord⟩, ⟨16, .total⟩, ⟨16, .remaining⟩, ⟨8, .countdown⟩, ⟨1, .cellBit⟩, ⟨3, .levels⟩, ⟨3, .enabled⟩, ⟨a, .txHead⟩, ⟨a, .txTail⟩, ⟨4, .txCount⟩, ⟨a, .rxHead⟩, ⟨a, .rxTail⟩, ⟨4, .rxCount⟩, ⟨32, .txShift⟩, ⟨6, .txValid⟩, ⟨32, .rxPartial⟩, ⟨6, .rxUsed⟩, ⟨16, .txAccepted⟩, ⟨16, .txConsumed⟩, ⟨16, .rxProduced⟩, ⟨16, .rxPopped⟩, ⟨2, .stage1⟩, ⟨2, .stage2⟩]
def inputLabel : {w : Nat} → Input w → String
  | _, .initialize => "initialize"
  | _, .command => "command"
  | _, .address => "address"
  | _, .word => "word"
  | _, .count => "count"
  | _, .idleLevels => "idle_levels"
  | _, .idleEnabled => "idle_enabled"
  | _, .startCount => "start_count"
  | _, .expectedGeneration => "expected_generation"
  | _, .expectedTransfer => "expected_transfer"
  | _, .txPush => "tx_push"
  | _, .txData => "tx_data"
  | _, .txBits => "tx_bits"
  | _, .rxPop => "rx_pop"
  | _, .rawInputs => "raw_inputs"
def outputLabel : {w : Nat} → Output w → String
  | _, .valid => "valid"
  | _, .busy => "busy"
  | _, .retained => "retained"
  | _, .pending => "pending"
  | _, .rejected => "rejected"
  | _, .stalled => "stalled"
  | _, .fault => "fault"
  | _, .waitingTX => "waiting_tx"
  | _, .waitingRX => "waiting_rx"
  | _, .generation => "generation"
  | _, .transfer => "transfer"
  | _, .phase => "phase"
  | _, .pc => "pc"
  | _, .remaining => "remaining"
  | _, .total => "total"
  | _, .levels => "levels"
  | _, .enabled => "enabled"
  | _, .txFree => "tx_free"
  | _, .txQueued => "tx_queued"
  | _, .rxQueued => "rx_queued"
  | _, .rxData => "rx_data"
  | _, .rxBits => "rx_bits"
  | _, .txAccepted => "tx_accepted"
  | _, .txConsumed => "tx_consumed"
  | _, .rxProduced => "rx_produced"
  | _, .rxPopped => "rx_popped"
  | _, .stage1 => "stage1"
  | _, .stage2 => "stage2"
def registerLabel : {w : Nat} → Register a w → String
  | _, .word k => s!"word{k.toNat}"
  | _, .txWord k => s!"tx_word{k.toNat}"
  | _, .txBits k => s!"tx_bits{k.toNat}"
  | _, .rxWord k => s!"rx_word{k.toNat}"
  | _, .rxBits k => s!"rx_bits{k.toNat}"
  | _, .written => "written"
  | _, .pending => "pending"
  | _, .valid => "valid"
  | _, .count => "count"
  | _, .idleLevels => "idle_levels"
  | _, .idleEnabled => "idle_enabled"
  | _, .generation => "generation"
  | _, .transfer => "transfer"
  | _, .phase => "phase"
  | _, .pc => "pc"
  | _, .currentWord => "current_word"
  | _, .total => "total"
  | _, .remaining => "remaining"
  | _, .countdown => "countdown"
  | _, .cellBit => "cell_bit"
  | _, .levels => "levels"
  | _, .enabled => "enabled"
  | _, .txHead => "tx_head"
  | _, .txTail => "tx_tail"
  | _, .txCount => "tx_count"
  | _, .rxHead => "rx_head"
  | _, .rxTail => "rx_tail"
  | _, .rxCount => "rx_count"
  | _, .txShift => "tx_shift"
  | _, .txValid => "tx_valid"
  | _, .rxPartial => "rx_partial"
  | _, .rxUsed => "rx_used"
  | _, .txAccepted => "tx_accepted"
  | _, .txConsumed => "tx_consumed"
  | _, .rxProduced => "rx_produced"
  | _, .rxPopped => "rx_popped"
  | _, .stage1 => "stage1"
  | _, .stage2 => "stage2"
def registerIndex : {w : Nat} → Register a w → Nat
  | _, .word k => k.toNat
  | _, .txWord k => 64 + 4*k.toNat
  | _, .txBits k => 65 + 4*k.toNat
  | _, .rxWord k => 66 + 4*k.toNat
  | _, .rxBits k => 67 + 4*k.toNat
  | _, .written => 64 + 4*(2^a) + 0
  | _, .pending => 64 + 4*(2^a) + 1
  | _, .valid => 64 + 4*(2^a) + 2
  | _, .count => 64 + 4*(2^a) + 3
  | _, .idleLevels => 64 + 4*(2^a) + 4
  | _, .idleEnabled => 64 + 4*(2^a) + 5
  | _, .generation => 64 + 4*(2^a) + 6
  | _, .transfer => 64 + 4*(2^a) + 7
  | _, .phase => 64 + 4*(2^a) + 8
  | _, .pc => 64 + 4*(2^a) + 9
  | _, .currentWord => 64 + 4*(2^a) + 10
  | _, .total => 64 + 4*(2^a) + 11
  | _, .remaining => 64 + 4*(2^a) + 12
  | _, .countdown => 64 + 4*(2^a) + 13
  | _, .cellBit => 64 + 4*(2^a) + 14
  | _, .levels => 64 + 4*(2^a) + 15
  | _, .enabled => 64 + 4*(2^a) + 16
  | _, .txHead => 64 + 4*(2^a) + 17
  | _, .txTail => 64 + 4*(2^a) + 18
  | _, .txCount => 64 + 4*(2^a) + 19
  | _, .rxHead => 64 + 4*(2^a) + 20
  | _, .rxTail => 64 + 4*(2^a) + 21
  | _, .rxCount => 64 + 4*(2^a) + 22
  | _, .txShift => 64 + 4*(2^a) + 23
  | _, .txValid => 64 + 4*(2^a) + 24
  | _, .rxPartial => 64 + 4*(2^a) + 25
  | _, .rxUsed => 64 + 4*(2^a) + 26
  | _, .txAccepted => 64 + 4*(2^a) + 27
  | _, .txConsumed => 64 + 4*(2^a) + 28
  | _, .rxProduced => 64 + 4*(2^a) + 29
  | _, .rxPopped => 64 + 4*(2^a) + 30
  | _, .stage1 => 64 + 4*(2^a) + 31
  | _, .stage2 => 64 + 4*(2^a) + 32
def moduleText (a : Nat) : Except String String := Buffered.MemoEmit.moduleText
  s!"pinwheel_streaming_core_d{2^a}" (circuit a) inputs (registers a) outputs
  inputLabel registerLabel outputLabel

end Pinwheel.Hardware.Streaming.Core

