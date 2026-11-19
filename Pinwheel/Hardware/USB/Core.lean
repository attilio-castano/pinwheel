import Pinwheel.Hardware.StreamingReady.Core
import Pinwheel.Program.USB.LowSpeed

/-! The opt-in depth-two core adds one terminal receive instruction. The
    existing core owns upload, IN transmission, quad custody, and release.
    During the receive instruction, the same two RX words serve as invisible
    staging registers. Publishing their queue count is the last ACK edge. -/
namespace Pinwheel.Hardware.USB
open Pinwheel.Hardware
open Pinwheel.USBPacketFeasibility
open Pinwheel.USBWaveformConstruction (ackSymbols padValue)

abbrev Input := StreamingReady.Core.Input
abbrev Output := StreamingReady.Core.Output

inductive Register : Nat → Type where
  | base : StreamingReady.Core.Register 1 w → Register w
  | mode : Register 3
  | age : Register 12
  | timer : Register 9
  | level : Register 1
  | sample : Register 4
  | previous : Register 1
  | ones : Register 3
  | consumed : Register 7
  | header : Register 16
  | crc : Register 16

abbrev E := Expr Input Register

def lift (expr : StreamingReady.Core.E 1 w) : E w := expr.bind .input (fun r => .reg (.base r))
def both (a b : E 1) : E 1 := .band a b
def either (a b : E w) : E w := .inv (.band (.inv a) (.inv b))
def xor (a b : E w) : E w := either (.band a (.inv b)) (.band (.inv a) b)
def eq (a : E w) (b : BitVec w) : E 1 := .equal a (.lit b)
def lt (a : E w) (b : BitVec w) : E 1 := .ult a (.lit b)
def inc (a : E w) : E w := .sub a (.lit (BitVec.ofInt w (-1)))
def dec (a : E w) : E w := .sub a (.lit 1)

def isMode (mode : BitVec 3) : E 1 := eq (.reg .mode) mode
def waiting : E 1 := isMode 1
def receiving : E 1 := isMode 2
def marker : E 1 := isMode 3
def delaying : E 1 := isMode 4
def sending : E 1 := isMode 5
def active : E 1 := .inv (.zero (.reg .mode))
def word : BitVec 64 := 5

def entering : E 1 := lift (StreamingReady.Core.both StreamingReady.Core.fetching
  (StreamingReady.Core.both StreamingReady.Core.entryBounds (StreamingReady.Core.both (.equal StreamingReady.Core.entryWord (.lit word))
    (StreamingReady.Core.both (.equal (.reg .remaining) (.lit 64))
      (StreamingReady.Core.both (StreamingReady.Core.both (.zero (.reg .idleEnabled)) StreamingReady.Core.drained)
        (.zero (.reg .rxProduced)))))))

def wire : E 2 := .reg (.base .stage2)
def wireJ : E 1 := eq wire 2
def wireK : E 1 := eq wire 1
def wireSE0 : E 1 := .zero wire
def wireSE1 : E 1 := eq wire 3
def clocked : E 1 := either (both waiting wireK) (both receiving (either wireJ wireK))
def transition : E 1 := .inv (.equal (.reg .level) wireK)
def symbol : E 1 := both clocked (both (.inv transition) (.zero (.reg .sample)))
def decoded : E 1 := .equal wireK (.reg .previous)
def stuffed : E 1 := eq (.reg .ones) 6
def logicalBit : E 1 := both symbol (.inv stuffed)
def countLt (n : BitVec 7) : E 1 := lt (.reg .consumed) n
def dataBit (lo hi : BitVec 7) : E 1 := both logicalBit (both (.inv (countLt lo)) (countLt hi))

def timerLt (n : BitVec 9) : E 1 := lt (.reg .timer) n
def markerWidthOK : E 1 := both (.inv (timerLt 31)) (timerLt 34)
def dataHeader : BitVec 16 := wordFor 16 (header 0x4B)
def frameOK : E 1 := both (.inv stuffed)
  (both (eq (.reg .consumed) 96) (both (eq (.reg .header) dataHeader)
    (eq (.reg .crc) 0xB001)))
def late : E 1 := both (.inv (lt (.reg .age) 2047)) (.inv sending)
def failed : E 1 := either late (either
  (both waiting (both (.inv wireK) (either wireSE1 (eq (.reg .age) 127))))
  (either (both receiving (either wireSE1 (both symbol (both stuffed decoded))))
    (both marker (.mux wireSE0 (.inv (timerLt 33))
      (.inv (both wireJ (both markerWidthOK frameOK)))))))
def sent : E 1 := both sending (timerLt 2)

def nextMode : E 3 :=
  .mux (lift StreamingReady.Core.resetting) (.lit 0)
    (.mux entering (.lit 1)
      (.mux (either failed sent) (.lit 0)
        (.mux (both waiting wireK) (.lit 2)
          (.mux (both receiving wireSE0) (.lit 3)
            (.mux (both marker wireJ) (.lit 4)
              (.mux (both delaying (timerLt 2)) (.lit 5) (.reg .mode)))))))

def shiftPayload (part : BitVec 1) : E 32 :=
  .concat (.slice 0 31 (by decide) (.reg (.base (.rxWord part)))) decoded

def receivingBase : (r : StreamingReady.Core.Register 1 w) → E w
  | .phase => .mux entering (.lit 7) (.mux sent (.lit 5) (.mux failed (.lit 6) (.lit 7)))
  | .levels => .lit 0
  | .enabled => .lit 0
  | .stage1 => lift (StreamingReady.Core.next .stage1)
  | .stage2 => lift (StreamingReady.Core.next .stage2)
  | .rxWord slot =>
      .mux (if slot = 0 then dataBit 16 48 else dataBit 48 80)
        (shiftPayload slot) (.reg (.base (.rxWord slot)))
  | .rxBits slot => .mux sent (.lit 32) (.reg (.base (.rxBits slot)))
  | .rxCount => .mux sent (.lit 2) (.reg (.base .rxCount))
  | .rxHead => .mux sent (.lit 0) (.reg (.base .rxHead))
  | .rxTail => .mux sent (.lit 0) (.reg (.base .rxTail))
  | .rxProduced => .mux sent (.lit 64) (.reg (.base .rxProduced))
  | .remaining => .mux sent (.lit 0) (.reg (.base .remaining))
  | r => .reg (.base r)

def nextBase (r : StreamingReady.Core.Register 1 w) : E w :=
  .mux (both (.inv (lift StreamingReady.Core.resetting)) (either entering active))
    (receivingBase r) (lift (StreamingReady.Core.next r))

def clear (initial : BitVec w) (proceed : E w) : E w :=
  .mux (either (lift StreamingReady.Core.resetting) entering) (.lit initial) proceed

def crcShift : E 16 := .concat (.lit (0 : BitVec 1)) (.slice 1 15 (by decide) (.reg .crc))
def feedback : E 1 := .inv (.equal (.slice 0 1 (by decide) (.reg .crc)) decoded)

def next : Register w → E w
  | .base r => nextBase r
  | .mode => nextMode
  | .age => clear 0 (.mux active (inc (.reg .age)) (.reg .age))
  | .timer => clear 0
      (.mux (both receiving wireSE0) (.lit 1)
        (.mux (both marker wireJ) (.lit 46)
          (.mux (both marker wireSE0) (inc (.reg .timer))
            (.mux (both delaying (timerLt 2)) (.lit 304)
              (.mux (either delaying sending) (dec (.reg .timer)) (.reg .timer))))))
  | .level => clear 0 (.mux clocked wireK (.reg .level))
  | .sample => clear 0
      (.mux clocked (.mux transition (.lit 7) (.mux symbol (.lit 15) (dec (.reg .sample)))) (.reg .sample))
  | .previous => clear 0 (.mux symbol wireK (.reg .previous))
  | .ones => clear 0 (.mux symbol (.mux (both (.inv stuffed) decoded) (inc (.reg .ones)) (.lit 0)) (.reg .ones))
  | .consumed => clear 0 (.mux (both logicalBit (countLt 97)) (inc (.reg .consumed)) (.reg .consumed))
  | .header => clear 0 (.mux (both logicalBit (countLt 16))
      (.concat (.slice 0 15 (by decide) (.reg .header)) decoded) (.reg .header))
  | .crc => clear 0xFFFF (.mux (dataBit 16 96)
      (.mux feedback (xor crcShift (.lit 0xA001)) crcShift) (.reg .crc))

def ackLevels : E 3 :=
  let index : E 9 := .sub (.lit 304) (.reg .timer)
  (ackSymbols.zipIdx).foldr (fun (line, i) rest =>
    .mux (lt index (BitVec.ofNat 9 ((i+1)*16))) (.lit (BitVec.ofNat 3 (padValue line))) rest) (.lit 0)

def output : Output w → E w
  | .levels => .mux sending ackLevels (lift (StreamingReady.Core.output .levels))
  | .enabled => .mux sending (.lit 3) (lift (StreamingReady.Core.output .enabled))
  | o => lift (StreamingReady.Core.output o)

def circuit : Circuit Input Register Output := ⟨next, output⟩

end Pinwheel.Hardware.USB
