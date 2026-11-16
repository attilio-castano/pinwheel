import Pinwheel.Hardware.USB.Core
import Pinwheel.Program.StreamingReadyCompile
import Pinwheel.Program.StreamingReadyExecution

/-! The certificate names the same 17 words that the public-pin replay loads.
    The pulse-prefix check runs the existing engine through all 560 clocks
    and stops before the opt-in word is fetched. -/
namespace Pinwheel.Hardware.USB
open Pinwheel.USBPacketFeasibility Pinwheel.USBOnlineFeasibility
open Pinwheel.USBWaveformConstruction (padValue)
open Pinwheel.Program.StreamingReady

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

private def pulse (low high : Fin 256) (lo hi : BitVec 3) : Instruction :=
  .pulse {lowDuration := low, highDuration := high, lowPins := ⟨lo,3⟩, highPins := ⟨hi,3⟩}

def inPrefix : List Instruction :=
  [pulse 14 15 1 2, pulse 13 15 1 2, pulse 13 15 1 2, pulse 45 15 1 2,
   pulse 29 47 1 2, pulse 13 15 1 2, pulse 13 15 1 2, pulse 13 15 1 2,
   pulse 13 15 1 2, pulse 13 15 1 2, pulse 13 15 1 2, pulse 29 15 1 2,
   pulse 0 11 1 1, pulse 0 12 2 2, pulse 0 28 0 0, pulse 0 12 2 2]

def inImage : List (BitVec 64) := inPrefix.map encode ++ [word]

private def prefixProgram : Program :=
  {memory := Vector.ofFn (fun i => inPrefix[i.val]?.getD .halt), lengthMinusOne := 16}

private def start : State 1 := {phase := .fetch, total := 64, remaining := 64}

private def observePrefix (s : State 1) : Nat → List (BitVec 3 × BitVec 3) × State 1
  | 0 => ([],s)
  | n+1 =>
    let next := engine prefixProgram s
    let after := observePrefix next n
    ((next.pins.levels,next.pins.enabled)::after.1,after.2)

def inToken : List Bool := header 0x69 ++ serialBits 11 0 ++ serialBits 5 2

private def inPins : List (BitVec 3 × BitVec 3) :=
  let body := (emitNRZI false (insertStuff inToken 0)).map asWire
  (body ++ [Wire.se0,Wire.se0,Wire.j]).flatMap
    (fun line => List.replicate 16 (BitVec.ofNat 3 (padValue line),3))

theorem installed_in_prefix :
    let result := observePrefix start 560
    result.1 = inPins ∧ result.2.phase = .fetch ∧ result.2.pc = 16 ∧
      result.2.remaining = 64 ∧ result.2.rx.count.val = 0 ∧ inImage[16]? = some word := by
  decide +kernel

private def crc5Next (state : BitVec 5) (bit : Bool) : BitVec 5 :=
  (state >>> 1) ^^^ (if state.getLsbD 0 != bit then 0x14#5 else 0)

theorem in_token_crc :
    ((inToken.drop 16).foldl crc5Next 31) = 0x06#5 := by decide +kernel

theorem in_prefix_words_canonical : (inPrefix.map encode).all wordCanonical = true := by decide +kernel
theorem receive_word_reserved_in_legacy : wordCanonical word = false := by decide +kernel

end Pinwheel.Hardware.USB
