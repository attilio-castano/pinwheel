import Pinwheel.Hardware.Streaming.Core

/-! Generic sampled-ready streaming microcore. Guarded LOW expiry releases
HIGH pins before polling the old second sampler. No protocol identifiers,
message-sized storage, or new runtime register families occur. -/
namespace Pinwheel.Hardware.StreamingReady.Core
open Pinwheel.Hardware

abbrev Input := Pinwheel.Hardware.Streaming.Core.Input
abbrev Register := Pinwheel.Hardware.Streaming.Core.Register
abbrev Output := Pinwheel.Hardware.Streaming.Core.Output

abbrev E (a : Nat) := Expr Input (Register a)
def both (x y : E a 1) : E a 1 := .band x y
def either (x y : E a w) : E a w := .inv (.band (.inv x) (.inv y))
def inc (x : E a w) : E a w := .sub x (.lit (BitVec.ofNat w (2^w-1)))
def add (x y : E a w) : E a w := .sub x (.sub (.lit 0) y)
def cmd (n : BitVec 4) : E a 1 := .equal (.input .command) (.lit n)
def isPhase (n : BitVec 3) : E a 1 := .equal (.reg .phase) (.lit n)
def cold : E a 1 := .input .initialize
def warm : E a 1 := both (.inv cold) (cmd 15)
def resetting : E a 1 := either cold warm
def busy : E a 1 := either
  (both (.inv (.zero (.reg .phase))) (.ult (.reg .phase) (.lit 5))) (isPhase 7)
def retained : E a 1 := either (isPhase 5) (isPhase 6)
def owned : E a 1 := either busy retained
def free : E a 1 := both (.inv resetting) (.zero (.reg .phase))
def identity : E a 1 := both
  (.equal (.input .expectedGeneration) (.reg .generation))
  (.equal (.input .expectedTransfer) (.reg .transfer))
def hostOwner : E a 1 := both (.inv resetting) (both owned identity)
def space (r : Register a 16) : E a 1 := .inv (.equal (.reg r) (.lit 65535))
def writing : E a 1 := both free (cmd 1)
def pack : {n : Nat} → (Fin n → E a 1) → E a n
  | 0, _ => .lit 0
  | 1, f => f 0
  | n+2, f => Expr.concat (a := n+1) (b := 1) (pack (fun k => f k.succ)) (f 0)
def covered : E a 1 := Streaming.Core.covered
def countValid : E a 1 := both (.inv (.zero (.input .count)))
  (.inv (.ult (.lit 64) (.input .count)))
def committing : E a 1 := both free (both (cmd 2)
  (both (.reg .pending) (both countValid (both covered (space .generation)))))
def starting : E a 1 := both free (both (cmd 3)
  (both (.reg .valid) (both (space .transfer)
    (.equal (.input .expectedGeneration) (.reg .generation)))))
def drained : E a 1 := both (.zero (.reg .txCount)) (both (.zero (.reg .rxCount))
  (both (.zero (.reg .txValid)) (.zero (.reg .rxUsed))))
def releasing : E a 1 := both hostOwner (both (cmd 4) (both retained drained))
def depth (a : Nat) : E a 4 := .lit (BitVec.ofNat 4 (2^a))
def txRoom : E a 1 := .ult (.reg .txCount) (depth a)
def rxRoom : E a 1 := .ult (.reg .rxCount) (depth a)
def txAvailable : E a 1 := either (.inv (.zero (.reg .txValid))) (.inv (.zero (.reg .txCount)))
def txBits16 : E a 16 := .concat (.lit (0 : BitVec 10)) (.input Streaming.Core.Input.txBits)
/-- Staging admitted while busy may finish under the same retained owner. -/
def pushing : E a 1 := both hostOwner (both (.input .txPush)
  (both txRoom (both (.inv (.zero (.input .txBits)))
    (both (.inv (.ult (.lit 32) (.input .txBits)))
      (.inv (.ult (.sub (.reg .total) (.reg .txAccepted)) txBits16))))))
def popping : E a 1 := both hostOwner (both (.input .rxPop) (.inv (.zero (.reg .rxCount))))
def rejected : E a 1 := both (.inv resetting) (either
  (both (.inv (cmd 0)) (.inv (either writing (either committing (either starting releasing)))))
  (either (both (.input .txPush) (.inv pushing)) (both (.input .rxPop) (.inv popping))))

def field (start len : Nat) (h : start+len ≤ 64) : E a len :=
  .slice start len h (.reg .currentWord)
def stream : E a 1 := .equal (field 0 3 (by decide)) (.lit 1)
def transmit : E a 1 := both stream (field 34 1 (by decide))
def receive : E a 1 := both stream (field 35 1 (by decide))
def lastCell : E a 1 := both stream (.equal (.reg .remaining) (.lit 1))
def credit : E a 1 := both (either (.inv transmit) txAvailable) (either (.inv receive) rxRoom)
def reserving : E a 1 := both (.inv resetting) (both (isPhase 2) credit)
def takingTX : E a 1 := both reserving transmit
def loadingTX : E a 1 := both takingTX (.zero (.reg .txValid))
def txHeadWord : E a 32 := Execution.readTree a (fun k => .reg (.txWord k)) (.reg .txHead)
def txHeadBits : E a 6 := Execution.readTree a (fun k => .reg (.txBits k)) (.reg .txHead)
def txSource : E a 32 := .mux (.zero (.reg .txValid)) txHeadWord (.reg .txShift)
def txSourceBits : E a 6 := .mux (.zero (.reg .txValid)) txHeadBits (.reg .txValid)
def nextBit : E a 1 := .slice 31 1 (by decide) txSource
def lowEnd : E a 1 := both (.inv resetting) (both (isPhase 3) (.zero (.reg .countdown)))
def highGuard : E a 1 := both stream (field 62 1 (by decide))
def guardMask : E a 2 := field 50 2 (by decide)
def guardExpected : E a 2 := field 52 2 (by decide)
def guardBudget : E a 8 := field 54 8 (by decide)
def guardCountdown : E a 8 := .mux (.zero guardBudget) (.lit 0) (.sub guardBudget (.lit 1))
def waitReady : E a 1 := .equal (.band (.reg .stage2) guardMask) guardExpected
def waitSuccess : E a 1 := both (.inv resetting) (both (isPhase 7) waitReady)
def waitFault : E a 1 := both (.inv resetting) (both (isPhase 7)
  (both (.inv waitReady) (both (.inv (.zero guardBudget)) (.zero (.reg .countdown)))))
def waitDecrement : E a 1 := both (.inv resetting) (both (isPhase 7)
  (both (.inv waitReady) (both (.inv (.zero guardBudget)) (.inv (.zero (.reg .countdown))))))
def capture : E a 1 := either (both lowEnd (.inv highGuard)) (both waitSuccess stream)
def standaloneSuccess : E a 1 := both waitSuccess (.inv stream)
def guardedLowEnd : E a 1 := both lowEnd highGuard
def capturingRX : E a 1 := both capture receive
def inputBit : E a 1 := .mux (field 33 1 (by decide))
  (.slice 1 1 (by decide) (.reg .stage2)) (.slice 0 1 (by decide) (.reg .stage2))
def assembled : E a 32 := .concat (.slice 0 31 (by decide) (.reg .rxPartial)) inputBit
def normalEmit : E a 1 := both capturingRX (either
  (.equal (.reg .rxUsed) (.lit 31)) lastCell)
def timeoutFlush : E a 1 := both waitFault (.inv (.zero (.reg .rxUsed)))
def emittingRX : E a 1 := either normalEmit timeoutFlush
def emittedData : E a 32 := .mux timeoutFlush (.reg .rxPartial) assembled
def emittedBits : E a 6 := .mux timeoutFlush (.reg .rxUsed) (inc (.reg .rxUsed))
def rxHeadWord : E a 32 := Execution.readTree a (fun k => .reg (.rxWord k)) (.reg .rxHead)
def rxHeadBits : E a 6 := Execution.readTree a (fun k => .reg (.rxBits k)) (.reg .rxHead)
def highEnd : E a 1 := both (.inv resetting) (both (isPhase 4) (.zero (.reg .countdown)))
def repeating : E a 1 := both stream (.ult (.lit 1) (.reg .remaining))
def advancing : E a 1 := both highEnd (.inv repeating)
def fetching : E a 1 := both (.inv resetting) (isPhase 1)
def entryWord : E a 64 := Execution.readTree 6 (fun k => .reg (.word k))
  (.slice 0 6 (by decide) (.reg .pc))
def entryField (start len : Nat) (h : start+len ≤ 64) : E a len := .slice start len h entryWord
def entryKind : E a 3 := entryField 0 3 (by decide)
def entryPulse : E a 1 := .zero entryKind
def entryStream : E a 1 := .equal entryKind (.lit 1)
def entryHalt : E a 1 := .equal entryWord (.lit 2)
def entryFault : E a 1 := .equal entryWord (.lit 3)
def entryWait : E a 1 := .equal entryKind (.lit 4)
def entryGuardMask : E a 2 := entryField 50 2 (by decide)
def entryGuardExpected : E a 2 := entryField 52 2 (by decide)
def entryGuardBudget : E a 8 := entryField 54 8 (by decide)
def entryGuardCountdown : E a 8 :=
  .mux (.zero entryGuardBudget) (.lit 0) (.sub entryGuardBudget (.lit 1))
def entryGuardCanonical : E a 1 := .zero (.band entryGuardExpected (.inv entryGuardMask))
def entryCanonical : E a 1 := .mux entryPulse (.zero (entryField 31 33 (by decide)))
  (.mux entryStream (both (.zero (entryField 63 1 (by decide)))
    (both (.mux (entryField 62 1 (by decide)) entryGuardCanonical
      (.zero (entryField 50 12 (by decide))))
      (either (.inv (entryField 34 1 (by decide)))
        (.ult (entryField 31 2 (by decide)) (.lit 3)))))
  (.mux entryWait (both entryGuardCanonical
    (both (.zero (entryField 3 16 (by decide)))
      (both (.zero (entryField 25 25 (by decide))) (.zero (entryField 62 2 (by decide))))))
    (either entryHalt entryFault)))
def entryBounds : E a 1 := .ult (.reg .pc) (.reg .count)
def entryBad : E a 1 := either (.inv entryBounds) (.inv entryCanonical)
def entryTerminal : E a 1 := either entryHalt entryFault
def entrySkip : E a 1 := both entryStream (.zero (.reg .remaining))
def enteringCell : E a 1 := both fetching (both (.inv entryBad)
  (both (.inv entryTerminal) (.inv entrySkip)))
def entryLast : E a 1 := both entryStream (.equal (.reg .remaining) (.lit 1))

def basePins (high enabled : Bool) : E a 3 :=
  let start := if high then (if enabled then 28 else 25) else (if enabled then 22 else 19)
  let extra := if high then (if enabled then 47 else 39) else (if enabled then 44 else 36)
  either (field start 3 (by dsimp [start]; split <;> split <;> omega))
    (.mux lastCell (field extra 3 (by dsimp [extra]; split <;> split <;> omega)) (.lit 0))
def entryLow (enabled : Bool) : E a 3 :=
  either (entryField (if enabled then 22 else 19) 3 (by split <;> omega))
    (.mux entryLast (entryField (if enabled then 44 else 36) 3 (by split <;> omega)) (.lit 0))
def driven (high enabled : Bool) (b : E a 1) : E a 3 := pack fun k =>
  let selected := both transmit (.equal (field 31 2 (by decide)) (.lit (BitVec.ofNat 2 k.val)))
  let mode := field 43 1 (by decide)
  let bit := .mux (field 42 1 (by decide)) (.inv b) b
  let value := if enabled then .mux mode (.inv bit) (.lit 1)
    else .mux mode (.lit 0) bit
  .mux selected value (.slice k.val 1 (by omega) (basePins high enabled))
def nextPins (enabled : Bool) : E a 3 :=
  .mux (either starting releasing) (if enabled then .reg .idleEnabled else .reg .idleLevels)
  (.mux (either waitFault (both fetching (either entryBad entryTerminal)))
    (if enabled then .reg .idleEnabled else .reg .idleLevels)
  (.mux enteringCell (entryLow enabled)
  (.mux reserving (driven false enabled nextBit)
  (.mux lowEnd (driven true enabled (.reg .cellBit))
  (.mux highEnd (basePins false enabled)
    (if enabled then .reg .enabled else .reg .levels))))))

def queueCount (old : E a 4) (put take : E a 1) : E a 4 :=
  .mux put (.mux take old (inc old)) (.mux take (.sub old (.lit 1)) old)
def nextRaw : {w : Nat} → Register a w → E a w
  | _, .word k => .mux (both writing (.equal (.input .address) (.lit k))) (.input .word) (.reg (.word k))
  | _, .txWord k => .mux (both pushing (.equal (.reg .txTail) (.lit k))) (.input .txData) (.reg (.txWord k))
  | _, .txBits k => .mux (both pushing (.equal (.reg .txTail) (.lit k))) (.input .txBits) (.reg (.txBits k))
  | _, .rxWord k => .mux (both emittingRX (.equal (.reg .rxTail) (.lit k))) emittedData (.reg (.rxWord k))
  | _, .rxBits k => .mux (both emittingRX (.equal (.reg .rxTail) (.lit k))) emittedBits (.reg (.rxBits k))
  | _, .written => .mux writing (pack fun k => either
      (.slice k.val 1 (by omega) (.reg .written))
      (.equal (.input .address) (.lit (BitVec.ofNat 6 k.val)))) (.reg .written)
  | _, .pending => .mux writing (.lit 1) (.mux committing (.lit 0) (.reg .pending))
  | _, .valid => .mux writing (.lit 0) (.mux committing (.lit 1) (.reg .valid))
  | _, .count => .mux committing (.input .count) (.reg .count)
  | _, .idleLevels => .mux committing (.input .idleLevels) (.reg .idleLevels)
  | _, .idleEnabled => .mux committing (.input .idleEnabled) (.reg .idleEnabled)
  | _, .generation => .mux committing (inc (.reg .generation)) (.reg .generation)
  | _, .transfer => .mux starting (inc (.reg .transfer)) (.reg .transfer)
  | _, .phase => .mux releasing (.lit 0) (.mux starting (.lit 1)
      (.mux fetching (.mux entryBad (.lit 6) (.mux entryTerminal
        (.mux entryFault (.lit 6) (.lit 5))
        (.mux entrySkip (.lit 1) (.mux entryWait (.lit 7) (.lit 2)))))
      (.mux reserving (.lit 3) (.mux guardedLowEnd (.lit 7) (.mux capture (.lit 4)
      (.mux standaloneSuccess (.lit 1) (.mux waitFault (.lit 6)
      (.mux highEnd (.mux repeating (.lit 2) (.lit 1)) (.reg .phase)))))))))
  | _, .pc => .mux starting (.lit 0)
      (.mux (either standaloneSuccess (either advancing (both fetching (both (.inv entryBad) entrySkip))))
        (inc (.reg .pc)) (.reg .pc))
  | _, .currentWord => .mux enteringCell entryWord (.reg .currentWord)
  | _, .total => .mux starting (.input .startCount) (.reg .total)
  | _, .remaining => .mux starting (.input .startCount)
      (.mux (both highEnd stream) (.sub (.reg .remaining) (.lit 1)) (.reg .remaining))
  | _, .countdown => .mux (both enteringCell entryWait) entryGuardCountdown
      (.mux guardedLowEnd guardCountdown
      (.mux reserving (field 3 8 (by decide))
      (.mux capture (field 11 8 (by decide))
      (.mux standaloneSuccess (.lit 0)
      (.mux (either waitDecrement
        (both (either (isPhase 3) (isPhase 4)) (.inv (.zero (.reg .countdown)))))
        (.sub (.reg .countdown) (.lit 1)) (.reg .countdown))))))
  | _, .cellBit => .mux reserving (.mux transmit nextBit (.lit 0)) (.reg .cellBit)
  | _, .levels => nextPins false
  | _, .enabled => nextPins true
  | _, .txHead => .mux starting (.lit 0) (.mux loadingTX (inc (.reg .txHead)) (.reg .txHead))
  | _, .txTail => .mux starting (.lit 0) (.mux pushing (inc (.reg .txTail)) (.reg .txTail))
  | _, .txCount => .mux starting (.lit 0) (queueCount (.reg .txCount) pushing loadingTX)
  | _, .rxHead => .mux starting (.lit 0) (.mux popping (inc (.reg .rxHead)) (.reg .rxHead))
  | _, .rxTail => .mux starting (.lit 0) (.mux emittingRX (inc (.reg .rxTail)) (.reg .rxTail))
  | _, .rxCount => .mux starting (.lit 0) (queueCount (.reg .rxCount) emittingRX popping)
  | _, .txShift => .mux starting (.lit 0) (.mux takingTX
      (.concat (.slice 0 31 (by decide) txSource) (.lit (0 : BitVec 1))) (.reg .txShift))
  | _, .txValid => .mux starting (.lit 0)
      (.mux takingTX (.sub txSourceBits (.lit 1)) (.reg .txValid))
  | _, .rxPartial => .mux (either starting waitFault) (.lit 0) (.mux capturingRX
      (.mux emittingRX (.lit 0) assembled) (.reg .rxPartial))
  | _, .rxUsed => .mux (either starting waitFault) (.lit 0) (.mux capturingRX
      (.mux emittingRX (.lit 0) (inc (.reg .rxUsed))) (.reg .rxUsed))
  | _, .txAccepted => .mux starting (.lit 0)
      (.mux pushing (add (.reg .txAccepted) txBits16) (.reg .txAccepted))
  | _, .txConsumed => .mux starting (.lit 0) (.mux takingTX (inc (.reg .txConsumed)) (.reg .txConsumed))
  | _, .rxProduced => .mux starting (.lit 0) (.mux capturingRX (inc (.reg .rxProduced)) (.reg .rxProduced))
  | _, .rxPopped => .mux starting (.lit 0) (.mux popping
      (add (.reg .rxPopped) (.concat (.lit (0 : BitVec 10)) rxHeadBits)) (.reg .rxPopped))
  | _, .stage1 => .input .rawInputs
  | _, .stage2 => .reg .stage1

def clearedRuntime : E a 1 := either resetting (either starting releasing)
def next : {w : Nat} → Register a w → E a w
  | _, .generation => .mux cold (.lit 0) (nextRaw .generation)
  | _, .transfer => .mux cold (.lit 0) (nextRaw .transfer)
  | _, .word k => .mux cold (.lit 0) (nextRaw (.word k))
  | _, .txWord k => .mux clearedRuntime (.lit 0) (nextRaw (.txWord k))
  | _, .txBits k => .mux clearedRuntime (.lit 32) (nextRaw (.txBits k))
  | _, .rxWord k => .mux clearedRuntime (.lit 0) (nextRaw (.rxWord k))
  | _, .rxBits k => .mux clearedRuntime (.lit 32) (nextRaw (.rxBits k))
  | _, .currentWord => .mux clearedRuntime (.lit 2) (nextRaw .currentWord)
  | _, .countdown => .mux clearedRuntime (.lit 0) (nextRaw .countdown)
  | _, .cellBit => .mux clearedRuntime (.lit 0) (nextRaw .cellBit)
  | _, .idleLevels => .mux cold (.lit 0) (nextRaw .idleLevels)
  | _, .idleEnabled => .mux cold (.lit 0) (nextRaw .idleEnabled)
  | _, .levels => .mux resetting (.mux cold (.lit 0) (.reg .idleLevels)) (nextRaw .levels)
  | _, .enabled => .mux resetting (.mux cold (.lit 0) (.reg .idleEnabled)) (nextRaw .enabled)
  | _, .pc => .mux (either resetting releasing) (.lit 0) (nextRaw .pc)
  | _, .total => .mux (either resetting releasing) (.lit 0) (nextRaw .total)
  | _, .remaining => .mux (either resetting releasing) (.lit 0) (nextRaw .remaining)
  | _, .txHead => .mux (either resetting releasing) (.lit 0) (nextRaw .txHead)
  | _, .txTail => .mux (either resetting releasing) (.lit 0) (nextRaw .txTail)
  | _, .txCount => .mux (either resetting releasing) (.lit 0) (nextRaw .txCount)
  | _, .rxHead => .mux (either resetting releasing) (.lit 0) (nextRaw .rxHead)
  | _, .rxTail => .mux (either resetting releasing) (.lit 0) (nextRaw .rxTail)
  | _, .rxCount => .mux (either resetting releasing) (.lit 0) (nextRaw .rxCount)
  | _, .txShift => .mux (either resetting releasing) (.lit 0) (nextRaw .txShift)
  | _, .txValid => .mux (either resetting releasing) (.lit 0) (nextRaw .txValid)
  | _, .rxPartial => .mux (either resetting releasing) (.lit 0) (nextRaw .rxPartial)
  | _, .rxUsed => .mux (either resetting releasing) (.lit 0) (nextRaw .rxUsed)
  | _, .txAccepted => .mux (either resetting releasing) (.lit 0) (nextRaw .txAccepted)
  | _, .txConsumed => .mux (either resetting releasing) (.lit 0) (nextRaw .txConsumed)
  | _, .rxProduced => .mux (either resetting releasing) (.lit 0) (nextRaw .rxProduced)
  | _, .rxPopped => .mux (either resetting releasing) (.lit 0) (nextRaw .rxPopped)
  | _, r => .mux resetting (.lit 0) (nextRaw r)

def output : {w : Nat} → Output w → E a w
  | _, .valid => .reg .valid | _, .busy => busy | _, .retained => retained
  | _, .pending => .reg .pending | _, .rejected => rejected
  | _, .stalled => either (both (isPhase 2) (.inv credit)) (both (isPhase 7) (.inv waitReady))
  | _, .fault => isPhase 6
  | _, .waitingTX => both (isPhase 2) (both transmit (.inv txAvailable))
  | _, .waitingRX => both (isPhase 2) (both receive (.inv rxRoom))
  | _, .generation => .reg .generation | _, .transfer => .reg .transfer
  | _, .phase => .reg .phase | _, .pc => .reg .pc | _, .remaining => .reg .remaining
  | _, .total => .reg .total | _, .levels => .reg .levels | _, .enabled => .reg .enabled
  | _, .txFree => .sub (depth a) (.reg .txCount) | _, .txQueued => .reg .txCount
  | _, .rxQueued => .reg .rxCount
  | _, .rxData => .mux (.zero (.reg .rxCount)) (.lit 0) rxHeadWord
  | _, .rxBits => .mux (.zero (.reg .rxCount)) (.lit 0) rxHeadBits
  | _, .txAccepted => .reg .txAccepted | _, .txConsumed => .reg .txConsumed
  | _, .rxProduced => .reg .rxProduced | _, .rxPopped => .reg .rxPopped
  | _, .stage1 => .reg .stage1 | _, .stage2 => .reg .stage2
def circuit (a : Nat) : Circuit Input (Register a) Output := ⟨next, output⟩

end Pinwheel.Hardware.StreamingReady.Core
