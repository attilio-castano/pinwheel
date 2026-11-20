import Pinwheel.Program.StreamingReadySegmentExecution
import Pinwheel.Program.StreamingSWDData

/-! A single SWD DP RDBUFF read on an already configured point-to-point
    link with one-cycle turnaround and overrun detection disabled. The
    operation assumes a prior read in the peer's model. -/
namespace Pinwheel.Program.StreamingSWDBranching

open StreamingReady (Cell Pins)
open StreamingReadySegments

inductive Variant where
  | standard | invertedAck | shortTurnaround
  deriving DecidableEq, Repr

/-- RDBUFF is the read of DP address 0xc. Request bits appear in wire order. -/
def requestBits : List Bool := [true, false, true, true, true, true, false, true]

abbrev idlePins := StreamingSWD.idlePins

inductive Ack where
  | ok | wait | fault | invalid
  deriving DecidableEq, Repr

def classifyAck : List Bool → Ack
  | [true, false, false] => .ok
  | [false, true, false] => .wait
  | [false, false, true] => .fault
  | _ => .invalid

def ackBits (code : Fin 8) : List Bool :=
  List.ofFn fun bit : Fin 3 => code.val.testBit bit.val

inductive Outcome where
  | ok (word : BitVec 32) | wait | fault | badParity | invalidAck | invalidLength
  deriving DecidableEq, Repr

/-- A sampled FAULT reply is a completed transaction with a typed reply.
    The engine can release its capture just as it can after WAIT. -/
def decode (bits : List Bool) : Outcome :=
  match classifyAck (bits.take 3) with
  | .ok =>
    if bits.length != 36 then .invalidLength
    else (StreamingSWD.decodeReply bits).elim .badParity .ok
  | .wait => if bits.length == 3 then .wait else .invalidLength
  | .fault => if bits.length == 3 then .fault else .invalidLength
  | .invalid => if bits.length == 3 then .invalidAck else .invalidLength

theorem decode_ok (value : BitVec 32) : decode (StreamingSWD.replyBits value) = .ok value := by
  have firstBits : (StreamingSWD.replyBits value).take 3 = StreamingSWD.okAck := by
    simp [StreamingSWD.replyBits, StreamingSWD.okAck]
  simp [decode, firstBits, StreamingSWD.okAck, classifyAck, StreamingSWD.decode_reply]

theorem decode_bad_parity (value : BitVec 32) :
    decode (StreamingSWD.badParityBits value) = .badParity := by
  have firstBits : (StreamingSWD.badParityBits value).take 3 = StreamingSWD.okAck := by
    simp [StreamingSWD.badParityBits, StreamingSWD.okAck]
  simp [decode, firstBits, StreamingSWD.okAck, classifyAck, StreamingSWD.decode_badParity]

private def clockCells (d : Fin 256) (data : Option Bool) : Row :=
  .cell (.stream {
    lowDuration := d
    highDuration := d
    lowPins := StreamingSWD.pads false data
    highPins := StreamingSWD.pads true data } none)

private def clockIdle (d : Fin 256) (v : Variant) (kind : Ack) : List Row :=
  let fall := if v == .shortTurnaround && kind == .wait then some false else none
  [.cell (StreamingSWD.pulse d fall), .count 8, clockCells d (some false), .cell .halt]

private def suffix (d : Fin 256) (v : Variant) (kind : Ack) : List Row :=
  match kind with
  | .ok => [.count 33, .cell (StreamingSWD.receive d)] ++ clockIdle d v kind
  | .wait | .fault => clockIdle d v kind
  -- An unexpected ACK might have come from a corrupted OK. Keep SWDIO
  -- released during potential data, parity and turnaround. Line reset is a
  -- separate recovery operation after this image releases its capture.
  | .invalid => [.count 34, clockCells d none, .cell .halt]

private inductive AckTree where
  | leaf (kind : Ack)
  | fork (zero one : AckTree)

private def tree : AckTree :=
  .fork
    (.fork (.fork (.leaf .invalid) (.leaf .fault)) (.fork (.leaf .wait) (.leaf .invalid)))
    (.fork (.fork (.leaf .ok) (.leaf .invalid)) (.fork (.leaf .invalid) (.leaf .invalid)))

private def lowerAck (d : Fin 256) (v : Variant) (pc : Nat) (test : Bool) : AckTree → List Row
  | .leaf kind => suffix d v kind
  | .fork zero one =>
    let fallthrough := lowerAck d v (pc + 3) true zero
    let taken := pc + 3 + fallthrough.length
    [.count 1, .cell (StreamingSWD.receive d), .branch (BitVec.ofNat 6 taken) test] ++
      fallthrough ++ lowerAck d v taken true one

/-- Each of the three ACK bits controls a forward branch. Every path
    consumes the entire ACK before changing who drives SWDIO. -/
def rows (d : Fin 256) (v : Variant) : List Row :=
  (requestBits.map fun bit => .cell (StreamingSWD.pulse d (some bit))) ++
    [.cell (StreamingSWD.pulse d none)] ++ lowerAck d v 9 (v != .invertedAck) tree

private def path (kind : Ack) : PathEnd :=
  match kind with
  | .ok => ⟨.complete, 0, 36, 510, 0⟩
  | .wait | .fault => ⟨.complete, 0, 3, 211, 0⟩
  | .invalid => ⟨.complete, 0, 3, 435, 0⟩

set_option maxRecDepth 8192 in
def image (v : Variant) : Image (rows 3 v) 0 where
  outcomes := [.invalid, .fault, .wait, .invalid, .ok, .invalid, .invalid, .invalid].map path
  checked := by cases v <;> decide +kernel

theorem nominal_rows : (image .standard).words.length = 59 := rfl

open Execution in
private def sampled (bit : Bool) : Observation := .cell 0 [if bit then 2 else 0]

/-- The oracle uses chronological ACK values independently of branch labels
    and feeds one second-sampler observation per active stream cell. -/
def service (code : Fin 8) (word : BitVec 32) (badParity : Bool) : List Execution.Observation :=
  let data := StreamingSWD.wordBits word
  let body := data ++ [StreamingSWD.parity data != badParity]
  (ackBits code).map sampled ++
    match code.val with
    | 1 => body.map sampled ++ List.replicate 8 (sampled false)
    | 2 | 4 => List.replicate 8 (sampled false)
    | _ => (body ++ [true]).map sampled

def runCase (variant : Variant) (code : Fin 8) (word : BitVec 32) (badParity : Bool) :
    Option Execution.Result :=
  Execution.run (rows 3 variant) 0 [] (service code word badParity) idlePins

private def captureSpec (code : Fin 8) (word : BitVec 32) (badParity : Bool) : List Bool :=
  if code.val == 1 then
    if badParity then StreamingSWD.badParityBits word else StreamingSWD.replyBits word
  else ackBits code

private def outcomeSpec (code : Fin 8) (word : BitVec 32) (badParity : Bool) : Outcome :=
  match code.val with
  | 1 => if badParity then .badParity else .ok word
  | 2 => .wait
  | 4 => .fault
  | _ => .invalidAck

private def riseSpec (code : Fin 8) : List Pins :=
  (requestBits.map fun bit => StreamingSWD.pads true (some bit)) ++
    match code.val with
    | 1 => List.replicate 38 (StreamingSWD.pads true none) ++
        List.replicate 8 (StreamingSWD.pads true (some false))
    | 2 | 4 => List.replicate 5 (StreamingSWD.pads true none) ++
        List.replicate 8 (StreamingSWD.pads true (some false))
    | _ => List.replicate 38 (StreamingSWD.pads true none)

private def drives (result : Execution.Result) : List Pins :=
  result.events.filterMap fun event => match event with
  | .drive pins => some pins
  | _ => none

private def rises (pins : List Pins) : List Pins :=
  (StreamingSWD.risingCuts pins).map fun cut => pins[cut + 1]?.getD idlePins

private def releasedRises (pins : List Pins) : Nat :=
  (rises ((pins.dropWhile (·.enabled[1])).takeWhile (!·.enabled[1]))).length

/-- The checked source image obeys the framing, reply and pad-drive
    contract on a fully serviced trace. The released interval is checked
    as a contiguous observation sequence, including LOW drive changes. -/
def matchesCase (variant : Variant) (code : Fin 8) (word : BitVec 32) (badParity : Bool) : Bool :=
  (runCase variant code word badParity).any fun result =>
    let kind := classifyAck (ackBits code)
    let pins := drives result
    decide (result.terminal = .planned (path kind)) &&
      result.txBits.isEmpty && result.remainingObservations.isEmpty &&
      result.rxBits == captureSpec code word badParity &&
      decide (decode result.rxBits = outcomeSpec code word badParity) &&
      decide (rises pins = riseSpec code) &&
      releasedRises pins == (if kind == .wait || kind == .fault then 5 else 38)

set_option maxRecDepth 8192 in
theorem every_ack : (List.finRange 8).all (fun code => matchesCase .standard code 0x96a65ac3 false) = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem bad_parity_completes : matchesCase .standard 1 0x96a65ac3 true = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem inverted_ack_rejected : matchesCase .invertedAck 1 0x96a65ac3 false = false := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem short_turnaround_rejected : matchesCase .shortTurnaround 2 0x96a65ac3 false = false := by
  decide +kernel

end Pinwheel.Program.StreamingSWDBranching
