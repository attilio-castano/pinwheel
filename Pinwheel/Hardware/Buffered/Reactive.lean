import Pinwheel.Hardware.Execution.Memory
import Pinwheel.Hardware.Buffered.ReactiveEmit

/-! Opt-in programmable counted reactive buffered circuit. There is no protocol dispatch:
the reloadable words control timed output, one-bit TX consumption and entry RX.
This target deliberately exposes a parallel test interface and a 64x144 flip-flop
program bank; it does not replace the paired SRAM/package implementation. -/
namespace Pinwheel.Hardware.Buffered.Reactive
open Pinwheel.Hardware

inductive Input : Nat → Type where
  | initialize : Input 1
  | command : Input 3
  | address : Input 6
  | word : Input 64
  | branch : Input 56
  | control : Input 24
  | virtualSpan : Input 11
  | count : Input 7
  | idleLevels : Input 3
  | idleEnabled : Input 3
  | txData : Input 32
  | txLength : Input 6
  | rxCapacity : Input 6
  | expectedGeneration : Input 16
  | expectedTransfer : Input 16
  | readIndex : Input 5
  | rawInputs : Input 2

inductive Register : Nat → Type where
  | word : BitVec 6 → Register 144
  | written : Register 64
  | pending : Register 1
  | valid : Register 1
  | count : Register 7
  | idleLevels : Register 3
  | idleEnabled : Register 3
  | generation : Register 16
  | transfer : Register 16
  | phase : Register 3
  | retained : Register 1
  | pc : Register 7
  | virtualPC : Register 10
  | virtualSpan : Register 11
  | currentControl : Register 22
  | outer : Register 3
  | inner : Register 3
  | remaining : Register 8
  | waitLeft : Register 8
  | scratch : Register 16
  | cachedDuration : Register 8
  | cachedBudget : Register 8
  | cachedCheck : Register 4
  | cachedWait : Register 2
  | cachedTerminal : Register 6
  | cachedBranch : Register 54
  | levels : Register 3
  | enabled : Register 3
  | txData : Register 32
  | txLength : Register 6
  | txConsumed : Register 6
  | rxData : Register 32
  | rxLength : Register 6
  | rxCapacity : Register 6
  | stage1 : Register 2
  | stage2 : Register 2

inductive Output : Nat → Type where
  | valid : Output 1 | busy : Output 1 | retained : Output 1
  | pending : Output 1 | rejected : Output 1
  | mode : Output 2 | pc : Output 8 | remaining : Output 8
  | levels : Output 3 | enabled : Output 3
  | txConsumed : Output 6 | rxLength : Output 6 | rxData : Output 32
  | readValid : Output 1 | readBit : Output 1
  | generation : Output 16 | transfer : Output 16 | exhausted : Output 1
  | stage1 : Output 2 | stage2 : Output 2
  | virtualPC : Output 10 | env0 : Output 3 | env1 : Output 3
  | phase : Output 3 | waitLeft : Output 8 | scratch : Output 16

abbrev E := Expr Input Register
def both (a b : E 1) : E 1 := .band a b
def either (a b : E w) : E w := .inv (.band (.inv a) (.inv b))
def cmd (k : BitVec 3) : E 1 := .equal (.input .command) (.lit k)
def increment (e : E w) : E w := .sub e (.lit (BitVec.ofNat w (2^w-1)))
def isPhase (p : BitVec 3) : E 1 := .equal (.reg .phase) (.lit p)
def busy : E 1 := both (.inv (.zero (.reg .phase))) (.ult (.reg .phase) (.lit 5))
def cold : E 1 := .input .initialize
def warm : E 1 := both (.inv cold) (cmd 7)
def resetting : E 1 := either cold warm
def free : E 1 := both (.inv resetting) (both (.inv busy) (.inv (.reg .retained)))
def space (r : Register 16) : E 1 := .inv (.equal (.reg r) (.lit 65535))
def writing : E 1 := both free (cmd 1)
def pack : {n : Nat} → (Fin n → E 1) → E n
  | 0, _ => .lit 0
  | 1, f => f 0
  | n+2, f => Expr.concat (a := n+1) (b := 1) (pack (fun k => f k.succ)) (f 0)
def covered : E 1 := (List.finRange 64).foldl (fun acc k =>
  both acc (either (.inv (.ult (.lit (BitVec.ofNat 7 k.val)) (.input .count)))
    (.slice k.val 1 (by omega) (.reg .written)))) (.lit 1)
def countValid : E 1 := both (.inv (.zero (.input .count)))
  (.inv (.ult (.lit 64) (.input .count)))
def spanValid : E 1 := both (.inv (.zero (.input .virtualSpan)))
  (.inv (.ult (.lit 1024) (.input .virtualSpan)))
def committing : E 1 := .mux (both free (cmd 2))
  (both (.reg .pending) (both countValid (both spanValid (both covered (space .generation))))) (.lit 0)
def starting : E 1 := both free (both (cmd 3)
  (both (.reg .valid) (both (space .transfer)
    (both (.equal (.input .expectedGeneration) (.reg .generation))
      (both (.inv (.ult (.lit 32) (.input .txLength)))
        (.inv (.ult (.lit 32) (.input .rxCapacity))))))))
def releasing : E 1 := both (.inv resetting) (both (cmd 4)
  (both (.reg .retained) (both (.equal (.input .expectedGeneration) (.reg .generation))
    (.equal (.input .expectedTransfer) (.reg .transfer)))))
def rejected : E 1 := both (.inv resetting) (both (.inv (cmd 0))
  (.inv (either writing (either committing (either starting releasing)))))
def inputBit (selector : E 1) : E 1 := .mux selector
  (.slice 1 1 (by decide) (.reg .stage2)) (.slice 0 1 (by decide) (.reg .stage2))
def checkedReady : E 1 := .equal
  (.band (.reg .stage2) (.slice 0 2 (by decide) (.reg .cachedCheck)))
  (.band (.slice 2 2 (by decide) (.reg .cachedCheck)) (.slice 0 2 (by decide) (.reg .cachedCheck)))
def waitReady : E 1 := .equal (inputBit (.slice 0 1 (by decide) (.reg .cachedWait)))
  (.slice 1 1 (by decide) (.reg .cachedWait))
def terminalEdge : E 1 := both (isPhase 3) (both checkedReady (.zero (.reg .remaining)))
def dispatch : E 1 := either (both (isPhase 1) (.zero (.reg .remaining)))
  (either (both (isPhase 2) waitReady)
    (either terminalEdge (both (isPhase 4) (both checkedReady (.zero (.reg .remaining))))))
def heldFault : E 1 := both (isPhase 3) (.inv checkedReady)
def heldTimeout : E 1 := either (both (isPhase 2) (both (.inv waitReady) (.zero (.reg .remaining))))
  (both (isPhase 4) (both (.inv checkedReady) (.zero (.reg .waitLeft))))
def entering : E 1 := both (.inv resetting) (either starting dispatch)
def captureBits (bits : E 6) (old : E 16) : E 16 := pack fun k => .mux
  (both (.slice 0 1 (by decide) bits) (.equal (.slice 2 4 (by decide) bits) (.lit (BitVec.ofNat 4 k.val))))
  (inputBit (.slice 1 1 (by decide) bits)) (.slice k.val 1 (by omega) old)
def exitScratch : E 16 := .mux terminalEdge (captureBits (.reg .cachedTerminal) (.reg .scratch)) (.reg .scratch)
def branchSample : E 4 := .slice 2 4 (by decide) (.reg .cachedBranch)
/-- Forward only the selected terminal capture instead of selecting a bit from
an expanded sixteen-bit capture bank. This preserves the same-edge read and
keeps the emitted expression traversal bounded. -/
def branchBit : E 1 := .mux
  (both terminalEdge (both (.slice 0 1 (by decide) (.reg .cachedTerminal))
    (.equal (.slice 2 4 (by decide) (.reg .cachedTerminal)) branchSample)))
  (inputBit (.slice 1 1 (by decide) (.reg .cachedTerminal)))
  (Execution.readTree 4 (fun k => .slice k.toNat 1 (by omega) (.reg .scratch)) branchSample)
def finish : E 2 := .slice 0 2 (by decide) (.reg .cachedBranch)
def endpoint : E 24 := .mux (.equal finish (.lit 1)) (.slice 6 24 (by decide) (.reg .cachedBranch))
  (.mux branchBit (.slice 6 24 (by decide) (.reg .cachedBranch)) (.slice 30 24 (by decide) (.reg .cachedBranch)))
def absoluteDispatch : E 1 := both terminalEdge
  (both (.inv (.zero finish)) (.inv (.slice 0 1 (by decide) endpoint)))
def controlDepth (c : E 24) : E 2 := .slice 0 2 (by decide) c
def outerStart (c : E 24) : E 6 := .slice 2 6 (by decide) c
def outerBound (c : E 24) : E 3 := .slice 8 3 (by decide) c
def innerStart (c : E 24) : E 6 := .slice 11 6 (by decide) c
def innerBound (c : E 24) : E 3 := .slice 17 3 (by decide) c
def outerEnd (c : E 24) : E 1 := .slice 20 1 (by decide) c
def innerEnd (c : E 24) : E 1 := .slice 21 1 (by decide) c
def currentControl : E 24 := Expr.concat (a := 2) (b := 22) (.lit 0) (.reg .currentControl)
def innerAgain : E 1 := both (.equal (controlDepth currentControl) (.lit 2))
  (both (innerEnd currentControl) (.ult (.reg .inner) (innerBound currentControl)))
def outerAgain : E 1 := both (.inv innerAgain)
  (both (outerEnd currentControl) (.ult (.reg .outer) (outerBound currentControl)))
def sequentialOuter : E 3 := .mux starting (.lit 0)
  (.mux outerAgain (increment (.reg .outer))
    (.mux (both (outerEnd currentControl) (.inv innerAgain)) (.lit 0) (.reg .outer)))
def sequentialInner : E 3 := .mux starting (.lit 0)
  (.mux innerAgain (increment (.reg .inner))
    (.mux (innerEnd currentControl) (.lit 0) (.reg .inner)))
def sequentialPC : E 7 := .mux starting (.lit 0)
  (.mux innerAgain (.concat (.lit (0 : BitVec 1)) (innerStart currentControl))
    (.mux outerAgain (.concat (.lit (0 : BitVec 1)) (outerStart currentControl))
      (increment (.reg .pc))))
def entryOuter : E 3 := .mux absoluteDispatch (.slice 18 3 (by decide) endpoint) sequentialOuter
def entryInner : E 3 := .mux absoluteDispatch (.slice 21 3 (by decide) endpoint) sequentialInner
def entryPC : E 7 := .mux absoluteDispatch (.slice 11 7 (by decide) endpoint) sequentialPC
def entryVirtual : E 11 := .mux starting (.lit 0)
  (.mux absoluteDispatch (.concat (.lit (0 : BitVec 1)) (.slice 1 10 (by decide) endpoint))
    (increment (Expr.concat (a := 1) (b := 10) (.lit 0) (.reg .virtualPC))))
def entryRecord : E 144 := .mux entering
  (Execution.readTree 6 (fun k => .reg (.word k)) (.slice 0 6 (by decide) entryPC)) (.lit 0)
def entryWord : E 64 := .slice 0 64 (by decide) entryRecord
def entryControl : E 24 := .slice 64 24 (by decide) entryRecord
def entryBranch : E 56 := .slice 88 56 (by decide) entryRecord
def kind : E 3 := .slice 0 3 (by decide) entryWord
def isKind (n : BitVec 3) : E 1 := .equal kind (.lit n)
def entryTerminal : E 1 := either (isKind 3) (isKind 4)
def entryCapture : E 6 := .slice 29 6 (by decide) entryWord
def terminalCapture : E 6 := .slice 35 6 (by decide) entryWord
def entryCount : E 7 := .reg .count
def inBounds : E 1 := both (.ult entryPC entryCount) (.ult entryVirtual (.reg .virtualSpan))
def captureCanonical (c : E 6) : E 1 := either (.slice 0 1 (by decide) c) (.zero c)
def endpointCanonical (e : E 24) : E 1 := .mux (.slice 0 1 (by decide) e)
  (.equal e (.lit 1))
  (both (.inv (.ult (.lit 64) (.slice 11 7 (by decide) e)))
    (either (.inv (.equal (.slice 11 7 (by decide) e) (.lit 64))) (.zero (.slice 18 6 (by decide) e))))
def branchCanonical : E 1 :=
  let f := .slice 0 2 (by decide) entryBranch
  let yes := .slice 6 24 (by decide) entryBranch
  let no := .slice 30 24 (by decide) entryBranch
  .mux (isKind 6)
    (both (.zero (.slice 54 2 (by decide) entryBranch))
      (.mux (.zero f) (.zero entryBranch)
        (.mux (.equal f (.lit 1))
          (both (.zero (.slice 2 4 (by decide) entryBranch))
            (both (endpointCanonical yes) (both (.zero (.slice 0 1 (by decide) yes)) (.zero no))))
          (both (.equal f (.lit 2)) (both (endpointCanonical yes) (endpointCanonical no))))))
    (.zero entryBranch)
def nextNormalizes : E 1 := .inv (both (isKind 6)
  (both (.equal (.slice 0 2 (by decide) entryBranch) (.lit 2))
    (both (.equal entryVirtual (.lit 1023))
      (either (.slice 6 1 (by decide) entryBranch) (.slice 30 1 (by decide) entryBranch)))))
def canonical : E 1 :=
  let common := both (.zero (.slice 56 8 (by decide) entryWord))
    (both (.inv (.equal (.slice 22 2 (by decide) entryWord) (.lit 3)))
      (both (captureCanonical entryCapture) (captureCanonical terminalCapture)))
  let noShift := .zero (.slice 20 2 (by decide) entryWord)
  let noShiftFlags := .zero (.slice 24 2 (by decide) entryWord)
  let noPreserve := both (.zero (.slice 17 3 (by decide) entryWord)) (.zero (.slice 26 3 (by decide) entryWord))
  let noReactive := both (.zero (.slice 35 20 (by decide) entryWord)) (.zero (.slice 55 1 (by decide) entryWord))
  let noCapture := both (.zero entryCapture) (.zero terminalCapture)
  .mux entryTerminal
    (either (.equal entryWord (.lit 3))
      (either (.equal entryWord (.lit 4)) (.equal entryWord (.lit (BitVec.ofNat 64 (4+2^55))))))
    (both common (both (.zero (.slice 55 1 (by decide) entryWord))
      (.mux (isKind 0) (both noPreserve (both noShift (both noShiftFlags noReactive)))
        (.mux (isKind 1) (both noPreserve
          (both (.inv (.equal (.slice 20 2 (by decide) entryWord) (.lit 3))) noReactive))
          (.mux (isKind 2) (both noShift (both noShiftFlags noReactive))
            (both noShift (both noShiftFlags
              (.mux (isKind 5)
                (both noCapture (both (.zero (.slice 9 8 (by decide) entryWord))
                  (.zero (.slice 41 4 (by decide) entryWord))))
                (.mux (isKind 6)
                  (both (.zero (.slice 45 10 (by decide) entryWord)) (.lit 1))
                  (both noCapture (.zero (.slice 45 2 (by decide) entryWord))))))))))))
def controlCanonical : E 1 :=
  let depth := controlDepth entryControl
  let common := both (.zero (.slice 22 2 (by decide) entryControl))
    (both (.inv (.ult (.slice 0 6 (by decide) entryPC) (outerStart entryControl)))
      (.inv (.ult (outerBound entryControl) entryOuter)))
  .mux (.zero depth) (both (.zero entryControl) (both (.zero entryOuter) (.zero entryInner)))
    (.mux (.equal depth (.lit 1))
      (both common (both (.zero (.slice 11 9 (by decide) entryControl))
        (both (.zero (innerEnd entryControl)) (.zero entryInner))))
      (.mux (.equal depth (.lit 2))
        (both common (both (.inv (.ult (.slice 0 6 (by decide) entryPC) (innerStart entryControl)))
          (both (.inv (.ult (innerStart entryControl) (outerStart entryControl)))
            (both (.inv (.ult (innerBound entryControl) entryInner))
              (either (.inv (outerEnd entryControl)) (innerEnd entryControl)))))) (.lit 0)))
def legalEntry : E 1 := both inBounds (both canonical (both controlCanonical (both branchCanonical nextNormalizes)))
def runEntry : E 1 := both entering (both legalEntry (.inv entryTerminal))
def entryTx : E 32 := .mux starting (.input .txData) (.reg .txData)
def entryTxLength : E 6 := .mux starting (.input .txLength) (.reg .txLength)
def entryConsumed : E 6 := .mux starting (.lit 0) (.reg .txConsumed)
def entryRxLength : E 6 := .mux starting (.lit 0) (.reg .rxLength)
def entryCapacity : E 6 := .mux starting (.input .rxCapacity) (.reg .rxCapacity)
def underflow : E 1 := both runEntry (both (isKind 1)
  (.inv (.ult entryConsumed entryTxLength)))
def consuming : E 1 := both runEntry (both (isKind 1) (.inv underflow))
def wantsRx : E 1 := .inv (.zero (.slice 22 2 (by decide) entryWord))
def overflow : E 1 := both runEntry (both (.inv underflow)
  (both wantsRx (.inv (.ult entryRxLength entryCapacity))))
def appending : E 1 := both runEntry (both (.inv underflow)
  (both wantsRx (.inv overflow)))
def entryFailed : E 1 := both entering
  (either (.inv legalEntry) (either (isKind 4) (either underflow overflow)))
def entryComplete : E 1 := both entering (both legalEntry (isKind 3))
def entryTimeout : E 1 := both entering (both legalEntry (both (isKind 4) (.slice 55 1 (by decide) entryWord)))
def stopping : E 1 := both (.inv resetting)
  (either heldFault (either heldTimeout (either entryFailed entryComplete)))
def entryPhase : E 3 := .mux (isKind 5) (.lit 2) (.mux (isKind 6) (.lit 3) (.mux (isKind 7) (.lit 4) (.lit 1)))
def entryScratch : E 16 := .mux runEntry
  (captureBits entryCapture (.mux starting (.lit 0) exitScratch)) (.mux starting (.lit 0) exitScratch)
def sampled : E 1 := .mux (.equal (.slice 22 2 (by decide) entryWord) (.lit 2))
  (.slice 1 1 (by decide) (.reg .stage2)) (.slice 0 1 (by decide) (.reg .stage2))
def appended : E 32 := pack fun k => .mux
  (.equal entryRxLength (.lit (BitVec.ofNat 6 k.val))) sampled
  (.slice k.val 1 (by omega) (.mux starting (.lit (0 : BitVec 32)) (.reg .rxData)))
def preserve (base old mask : E 3) : E 3 := either (.band base (.inv mask)) (.band old mask)
def shiftValue : E 1 := .mux (.slice 25 1 (by decide) entryWord)
  (.inv (.slice 0 1 (by decide) entryTx)) (.slice 0 1 (by decide) entryTx)
def shifted (base : E 3) : E 3 := pack fun k => .mux
  (.equal (.slice 20 2 (by decide) entryWord) (.lit (BitVec.ofNat 2 k.val))) shiftValue (.slice k.val 1 (by omega) base)
def entryLevels : E 3 :=
  let base := .slice 3 3 (by decide) entryWord
  .mux (isKind 1) (.mux (.slice 24 1 (by decide) entryWord) base (shifted base))
    (preserve base (.reg .levels) (.slice 17 3 (by decide) entryWord))
def entryEnabled : E 3 :=
  let base := .slice 6 3 (by decide) entryWord
  .mux (isKind 1) (.mux (.slice 24 1 (by decide) entryWord) (shifted base) base)
    (preserve base (.reg .enabled) (.slice 26 3 (by decide) entryWord))
def clearOwner : E 1 := either resetting releasing
def next : {w : Nat} → Register w → E w
  | _, .word k => .mux (both committing
      (.inv (.ult (.lit (BitVec.ofNat 7 k.toNat)) (.input .count)))) (.lit 0)
    (.mux (both writing (.equal (.input .address) (.lit k)))
      (Expr.concat (a := 56) (b := 88) (.input .branch)
        (Expr.concat (a := 24) (b := 64) (.input .control) (.input .word))) (.reg (.word k)))
  | _, .written => .mux resetting (.lit 0) (.mux writing
      (pack fun k => .mux (.equal (.input .address) (.lit (BitVec.ofNat 6 k.val))) (.lit 1)
        (.mux (.reg .pending) (.slice k.val 1 (by omega) (.reg .written)) (.lit 0))) (.reg .written))
  | _, .pending => .mux resetting (.lit 0)
      (.mux committing (.lit 0) (.mux writing (.lit 1) (.reg .pending)))
  | _, .valid => .mux (either resetting writing) (.lit 0)
      (.mux committing (.lit 1) (.reg .valid))
  | _, .count => .mux resetting (.lit 0) (.mux committing (.input .count) (.reg .count))
  | _, .idleLevels => .mux cold (.lit 0) (.mux committing (.input .idleLevels) (.reg .idleLevels))
  | _, .idleEnabled => .mux cold (.lit 0) (.mux committing (.input .idleEnabled) (.reg .idleEnabled))
  | _, .generation => .mux cold (.lit 0)
      (.mux (either committing (both warm (space .generation))) (increment (.reg .generation)) (.reg .generation))
  | _, .transfer => .mux cold (.lit 0) (.mux starting (increment (.reg .transfer)) (.reg .transfer))
  | _, .phase => .mux clearOwner (.lit 0)
      (.mux stopping (.mux (either heldTimeout entryTimeout) (.lit 6) (.mux entryComplete (.lit 5) (.lit 7)))
        (.mux entering entryPhase (.reg .phase)))
  | _, .retained => .mux clearOwner (.lit 0) (.mux stopping (.lit 1) (.reg .retained))
  | _, .pc => .mux (either clearOwner stopping) (.lit 0) (.mux entering entryPC (.reg .pc))
  | _, .virtualPC => .mux (either clearOwner stopping) (.lit 0)
      (.mux entering (.slice 0 10 (by decide) entryVirtual) (.reg .virtualPC))
  | _, .virtualSpan => .mux resetting (.lit 0)
      (.mux committing (.input .virtualSpan) (.reg .virtualSpan))
  | _, .currentControl => .mux (either clearOwner stopping) (.lit 0)
      (.mux entering (.slice 0 22 (by decide) entryControl) (.reg .currentControl))
  | _, .outer => .mux (either clearOwner stopping) (.lit 0)
      (.mux entering entryOuter (.reg .outer))
  | _, .inner => .mux (either clearOwner stopping) (.lit 0)
      (.mux entering entryInner (.reg .inner))
  | _, .remaining => .mux (either clearOwner stopping) (.lit 0)
      (.mux entering (.mux (isKind 5) (.slice 47 8 (by decide) entryWord) (.slice 9 8 (by decide) entryWord))
        (.mux busy
          (.mux (both (isPhase 4) (.inv checkedReady)) (.reg .cachedDuration)
            (.sub (.reg .remaining) (.lit 1))) (.reg .remaining)))
  | _, .waitLeft => .mux (either clearOwner stopping) (.lit 0)
      (.mux entering (.mux (isKind 7) (.slice 47 8 (by decide) entryWord) (.lit 0))
        (.mux (isPhase 4) (.mux checkedReady (.reg .cachedBudget) (.sub (.reg .waitLeft) (.lit 1))) (.reg .waitLeft)))
  | _, .scratch => .mux clearOwner (.lit 0)
      (.mux entering entryScratch exitScratch)
  | _, .cachedDuration => .mux (either clearOwner stopping) (.lit 0)
      (.mux entering (.slice 9 8 (by decide) entryWord) (.reg .cachedDuration))
  | _, .cachedBudget => .mux (either clearOwner stopping) (.lit 0)
      (.mux entering (.slice 47 8 (by decide) entryWord) (.reg .cachedBudget))
  | _, .cachedCheck => .mux (either clearOwner stopping) (.lit 0)
      (.mux entering (.slice 41 4 (by decide) entryWord) (.reg .cachedCheck))
  | _, .cachedWait => .mux (either clearOwner stopping) (.lit 0)
      (.mux entering (.slice 45 2 (by decide) entryWord) (.reg .cachedWait))
  | _, .cachedTerminal => .mux (either clearOwner stopping) (.lit 0)
      (.mux entering terminalCapture (.reg .cachedTerminal))
  | _, .cachedBranch => .mux (either clearOwner stopping) (.lit 0)
      (.mux entering (.slice 0 54 (by decide) entryBranch) (.reg .cachedBranch))
  | _, .levels => .mux cold (.lit 0) (.mux committing (.input .idleLevels)
      (.mux (either clearOwner stopping) (.reg .idleLevels)
        (.mux runEntry entryLevels (.reg .levels))))
  | _, .enabled => .mux cold (.lit 0) (.mux committing (.input .idleEnabled)
      (.mux (either clearOwner stopping) (.reg .idleEnabled)
        (.mux runEntry entryEnabled (.reg .enabled))))
  | _, .txData => .mux clearOwner (.lit 0) (.mux consuming
      (.concat (.lit (0 : BitVec 1)) (.slice 1 31 (by decide) entryTx))
      (.mux starting (.input .txData) (.reg .txData)))
  | _, .txLength => .mux clearOwner (.lit 0) (.mux starting (.input .txLength) (.reg .txLength))
  | _, .txConsumed => .mux clearOwner (.lit 0) (.mux consuming (increment entryConsumed)
      (.mux starting (.lit 0) (.reg .txConsumed)))
  | _, .rxData => .mux clearOwner (.lit 0) (.mux appending appended
      (.mux starting (.lit 0) (.reg .rxData)))
  | _, .rxLength => .mux clearOwner (.lit 0) (.mux appending (increment entryRxLength)
      (.mux starting (.lit 0) (.reg .rxLength)))
  | _, .rxCapacity => .mux clearOwner (.lit 0) (.mux starting (.input .rxCapacity) (.reg .rxCapacity))
  | _, .stage1 => .mux resetting (.lit 0) (.input .rawInputs)
  | _, .stage2 => .mux resetting (.lit 0) (.reg .stage1)
def readValid : E 1 := both (.reg .retained)
  (.ult (.concat (.lit (0 : BitVec 1)) (.input .readIndex)) (.reg .rxLength))
def circuit : Circuit Input Register Output where
  next := next
  output := fun o => match o with
    | .valid => .reg .valid | .busy => busy | .retained => .reg .retained
    | .pending => .reg .pending | .rejected => rejected
    | .mode => .mux busy (.lit 1) (.mux (isPhase 5) (.lit 2) (.mux (either (isPhase 6) (isPhase 7)) (.lit 3) (.lit 0))) | .pc => Expr.concat (a := 1) (b := 7) (.lit 0) (.reg .pc) | .remaining => .reg .remaining
    | .levels => .reg .levels | .enabled => .reg .enabled
    | .txConsumed => .reg .txConsumed | .rxLength => .reg .rxLength | .rxData => .reg .rxData
    | .readValid => readValid
    | .readBit => .mux readValid (Execution.readTree 5
        (fun k => .slice k.toNat 1 (by omega) (.reg .rxData)) (.input .readIndex)) (.lit 0)
    | .generation => .reg .generation | .transfer => .reg .transfer
    | .exhausted => either (.inv (space .generation)) (.inv (space .transfer))
    | .stage1 => .reg .stage1 | .stage2 => .reg .stage2
    | .phase => .reg .phase | .waitLeft => .reg .waitLeft | .scratch => .reg .scratch
    | .virtualPC => .reg .virtualPC
    | .env0 => .mux (.equal (controlDepth currentControl) (.lit 2)) (.reg .inner)
        (.mux (.equal (controlDepth currentControl) (.lit 1)) (.reg .outer) (.lit 0))
    | .env1 => .mux (.equal (controlDepth currentControl) (.lit 2)) (.reg .outer) (.lit 0)

def inputs : Array (Sigma Input) :=
  #[⟨1,.initialize⟩,⟨3,.command⟩,⟨6,.address⟩,⟨64,.word⟩,⟨24,.control⟩,⟨56,.branch⟩,⟨7,.count⟩,⟨11,.virtualSpan⟩,
    ⟨3,.idleLevels⟩,⟨3,.idleEnabled⟩,⟨32,.txData⟩,⟨6,.txLength⟩,⟨6,.rxCapacity⟩,
    ⟨16,.expectedGeneration⟩,⟨16,.expectedTransfer⟩,⟨5,.readIndex⟩,⟨2,.rawInputs⟩]
def registers : Array (Sigma Register) :=
  Array.ofFn (fun k : Fin 64 => ⟨144,.word (BitVec.ofFin k)⟩) ++
  #[⟨64,.written⟩,⟨1,.pending⟩,⟨1,.valid⟩,⟨7,.count⟩,⟨3,.idleLevels⟩,⟨3,.idleEnabled⟩,
    ⟨16,.generation⟩,⟨16,.transfer⟩,⟨3,.phase⟩,⟨1,.retained⟩,⟨7,.pc⟩,⟨10,.virtualPC⟩,⟨11,.virtualSpan⟩,⟨22,.currentControl⟩,⟨3,.outer⟩,⟨3,.inner⟩,⟨8,.remaining⟩,
    ⟨3,.levels⟩,⟨3,.enabled⟩,⟨32,.txData⟩,⟨6,.txLength⟩,⟨6,.txConsumed⟩,
    ⟨32,.rxData⟩,⟨6,.rxLength⟩,⟨6,.rxCapacity⟩,⟨2,.stage1⟩,⟨2,.stage2⟩,
    ⟨8,.waitLeft⟩,⟨16,.scratch⟩,⟨8,.cachedDuration⟩,⟨8,.cachedBudget⟩,⟨4,.cachedCheck⟩,
    ⟨2,.cachedWait⟩,⟨6,.cachedTerminal⟩,⟨54,.cachedBranch⟩]
/-- Dense snapshot index for executable interpretation; it adds no circuit state. -/
def registerIndex : {w : Nat} → Register w → Nat
  | _,.word k => k.toNat
  | _,.written => 64 | _,.pending => 65 | _,.valid => 66 | _,.count => 67
  | _,.idleLevels => 68 | _,.idleEnabled => 69 | _,.generation => 70 | _,.transfer => 71
  | _,.phase => 72 | _,.retained => 73 | _,.pc => 74 | _,.virtualPC => 75
  | _,.virtualSpan => 76 | _,.currentControl => 77 | _,.outer => 78 | _,.inner => 79
  | _,.remaining => 80 | _,.levels => 81 | _,.enabled => 82 | _,.txData => 83
  | _,.txLength => 84 | _,.txConsumed => 85 | _,.rxData => 86 | _,.rxLength => 87
  | _,.rxCapacity => 88 | _,.stage1 => 89 | _,.stage2 => 90
  | _,.waitLeft => 91 | _,.scratch => 92 | _,.cachedDuration => 93 | _,.cachedBudget => 94
  | _,.cachedCheck => 95 | _,.cachedWait => 96 | _,.cachedTerminal => 97 | _,.cachedBranch => 98
def outputs : Array (Sigma Output) :=
  #[⟨1,.valid⟩,⟨1,.busy⟩,⟨1,.retained⟩,⟨1,.pending⟩,⟨1,.rejected⟩,
    ⟨2,.mode⟩,⟨8,.pc⟩,⟨8,.remaining⟩,⟨3,.levels⟩,⟨3,.enabled⟩,
    ⟨6,.txConsumed⟩,⟨6,.rxLength⟩,⟨32,.rxData⟩,⟨1,.readValid⟩,⟨1,.readBit⟩,
    ⟨16,.generation⟩,⟨16,.transfer⟩,⟨1,.exhausted⟩,⟨2,.stage1⟩,⟨2,.stage2⟩,⟨10,.virtualPC⟩,⟨3,.env0⟩,⟨3,.env1⟩,⟨3,.phase⟩,⟨8,.waitLeft⟩,⟨16,.scratch⟩]
def inputLabel : {w : Nat} → Input w → String
  | _,.initialize => "initialize" | _,.command => "command" | _,.address => "address"
  | _,.word => "word" | _,.control => "control" | _,.branch => "branch" | _,.virtualSpan => "virtual_span" | _,.count => "count" | _,.idleLevels => "idle_levels"
  | _,.idleEnabled => "idle_enabled" | _,.txData => "tx_data" | _,.txLength => "tx_length"
  | _,.rxCapacity => "rx_capacity" | _,.expectedGeneration => "expected_generation"
  | _,.expectedTransfer => "expected_transfer" | _,.readIndex => "read_index" | _,.rawInputs => "raw_inputs"
def registerLabel : {w : Nat} → Register w → String
  | _,.word k => s!"word{k.toNat}" | _,.written => "written" | _,.pending => "pending"
  | _,.valid => "valid" | _,.count => "count" | _,.idleLevels => "idle_levels"
  | _,.idleEnabled => "idle_enabled" | _,.generation => "generation" | _,.transfer => "transfer"
  | _,.phase => "phase" | _,.retained => "retained" | _,.pc => "pc"
  | _,.virtualPC => "virtual_pc" | _,.virtualSpan => "virtual_span" | _,.currentControl => "current_control"
  | _,.outer => "outer" | _,.inner => "inner" | _,.remaining => "remaining"
  | _,.levels => "levels" | _,.enabled => "enabled" | _,.txData => "tx_data"
  | _,.txLength => "tx_length" | _,.txConsumed => "tx_consumed" | _,.rxData => "rx_data"
  | _,.rxLength => "rx_length" | _,.rxCapacity => "rx_capacity" | _,.stage1 => "stage1" | _,.stage2 => "stage2"
  | _,.waitLeft => "wait_left" | _,.scratch => "scratch" | _,.cachedDuration => "cached_duration"
  | _,.cachedBudget => "cached_budget" | _,.cachedCheck => "cached_check" | _,.cachedWait => "cached_wait"
  | _,.cachedTerminal => "cached_terminal" | _,.cachedBranch => "cached_branch"
def outputLabel : {w : Nat} → Output w → String
  | _,.valid => "valid" | _,.busy => "busy" | _,.retained => "retained" | _,.pending => "pending"
  | _,.rejected => "rejected" | _,.mode => "mode" | _,.pc => "pc" | _,.remaining => "remaining"
  | _,.levels => "levels" | _,.enabled => "enabled" | _,.txConsumed => "tx_consumed"
  | _,.rxLength => "rx_length" | _,.rxData => "rx_data" | _,.readValid => "read_valid"
  | _,.readBit => "read_bit" | _,.generation => "generation" | _,.transfer => "transfer"
  | _,.exhausted => "exhausted" | _,.stage1 => "stage1" | _,.stage2 => "stage2"
  | _,.virtualPC => "virtual_pc" | _,.env0 => "env0" | _,.env1 => "env1"
  | _,.phase => "phase" | _,.waitLeft => "wait_left" | _,.scratch => "scratch"
def moduleText : Except String String := MemoEmit.moduleText "pinwheel_buffered_reactive"
  circuit inputs registers outputs inputLabel registerLabel outputLabel

end Pinwheel.Hardware.Buffered.Reactive
