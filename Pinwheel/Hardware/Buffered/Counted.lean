import Pinwheel.Hardware.Execution.Memory
import Pinwheel.Hardware.Emit

/-! Opt-in programmable counted timed buffered circuit. There is no protocol dispatch:
the reloadable words control timed output, one-bit TX consumption and entry RX.
This target deliberately exposes a parallel test interface and a 64x56 flip-flop
program bank; it does not replace the paired SRAM/package implementation. -/
namespace Pinwheel.Hardware.Buffered.Counted
open Pinwheel.Hardware

inductive Input : Nat → Type where
  | initialize : Input 1
  | command : Input 3
  | address : Input 6
  | word : Input 32
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
  | word : BitVec 6 → Register 56
  | written : Register 64
  | pending : Register 1
  | valid : Register 1
  | count : Register 7
  | idleLevels : Register 3
  | idleEnabled : Register 3
  | generation : Register 16
  | transfer : Register 16
  | mode : Register 2
  | retained : Register 1
  | pc : Register 7
  | virtualPC : Register 10
  | virtualSpan : Register 11
  | currentControl : Register 22
  | outer : Register 3
  | inner : Register 3
  | remaining : Register 8
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

abbrev E := Expr Input Register
def both (a b : E 1) : E 1 := .band a b
def either (a b : E w) : E w := .inv (.band (.inv a) (.inv b))
def cmd (k : BitVec 3) : E 1 := .equal (.input .command) (.lit k)
def increment (e : E w) : E w := .sub e (.lit (BitVec.ofNat w (2^w-1)))
def busy : E 1 := .equal (.reg .mode) (.lit 1)
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
def dispatch : E 1 := both busy (.zero (.reg .remaining))
def entering : E 1 := both (.inv resetting) (either starting dispatch)
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
def entryOuter : E 3 := .mux starting (.lit 0)
  (.mux outerAgain (increment (.reg .outer))
    (.mux (both (outerEnd currentControl) (.inv innerAgain)) (.lit 0) (.reg .outer)))
def entryInner : E 3 := .mux starting (.lit 0)
  (.mux innerAgain (increment (.reg .inner))
    (.mux (innerEnd currentControl) (.lit 0) (.reg .inner)))
def entryPC : E 7 := .mux starting (.lit 0)
  (.mux innerAgain (.concat (.lit (0 : BitVec 1)) (innerStart currentControl))
    (.mux outerAgain (.concat (.lit (0 : BitVec 1)) (outerStart currentControl))
      (increment (.reg .pc))))
def entryVirtual : E 11 := .mux starting (.lit 0)
  (increment (Expr.concat (a := 1) (b := 10) (.lit 0) (.reg .virtualPC)))
def entryRecord : E 56 := .mux entering
  (Execution.readTree 6 (fun k => .reg (.word k)) (.slice 0 6 (by decide) entryPC)) (.lit 0)
def entryWord : E 32 := .slice 0 32 (by decide) entryRecord
def entryControl : E 24 := .slice 32 24 (by decide) entryRecord
def kind : E 3 := .slice 0 3 (by decide) entryWord
def isKind (n : BitVec 3) : E 1 := .equal kind (.lit n)
def entryCount : E 7 := .reg .count
def inBounds : E 1 := both (.ult entryPC entryCount) (.ult entryVirtual (.reg .virtualSpan))
def canonical : E 1 :=
  let common := both (.zero (.slice 24 8 (by decide) entryWord))
    (.inv (.equal (.slice 22 2 (by decide) entryWord) (.lit 3)))
  .mux (isKind 0) (both common (.zero (.slice 17 5 (by decide) entryWord)))
    (.mux (isKind 1) (both common (both (.zero (.slice 17 3 (by decide) entryWord))
        (.inv (.equal (.slice 20 2 (by decide) entryWord) (.lit 3)))))
      (.mux (isKind 2) (both common (.zero (.slice 20 2 (by decide) entryWord)))
        (either (.equal entryWord (.lit 3)) (.equal entryWord (.lit 4)))))
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
def terminalControl : E 1 := .mux (.ult kind (.lit 3)) (.lit 1) (.zero entryControl)
def legalEntry : E 1 := both inBounds (both canonical (both controlCanonical terminalControl))
def runEntry : E 1 := both entering (both legalEntry (.ult kind (.lit 3)))
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
def stopping : E 1 := either entryFailed entryComplete
def sampled : E 1 := .mux (.equal (.slice 22 2 (by decide) entryWord) (.lit 2))
  (.slice 1 1 (by decide) (.reg .stage2)) (.slice 0 1 (by decide) (.reg .stage2))
def appended : E 32 := pack fun k => .mux
  (.equal entryRxLength (.lit (BitVec.ofNat 6 k.val))) sampled
  (.slice k.val 1 (by omega) (.mux starting (.lit (0 : BitVec 32)) (.reg .rxData)))
def entryLevels : E 3 :=
  let levels := .slice 3 3 (by decide) entryWord
  .mux (isKind 1) (pack fun k => .mux
      (.equal (.slice 20 2 (by decide) entryWord) (.lit (BitVec.ofNat 2 k.val)))
      (.slice 0 1 (by decide) entryTx) (.slice k.val 1 (by omega) levels))
    (.mux (isKind 2) (either
      (.band levels (.inv (.slice 17 3 (by decide) entryWord)))
      (.band (.reg .levels) (.slice 17 3 (by decide) entryWord))) levels)
def clearOwner : E 1 := either resetting releasing
def next : {w : Nat} → Register w → E w
  | _, .word k => .mux (both committing
      (.inv (.ult (.lit (BitVec.ofNat 7 k.toNat)) (.input .count)))) (.lit 0)
    (.mux (both writing (.equal (.input .address) (.lit k)))
      (Expr.concat (a := 24) (b := 32) (.input .control) (.input .word)) (.reg (.word k)))
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
  | _, .mode => .mux clearOwner (.lit 0)
      (.mux entering (.mux entryFailed (.lit 3) (.mux entryComplete (.lit 2) (.lit 1))) (.reg .mode))
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
  | _, .remaining => .mux clearOwner (.lit 0) (.mux entering
      (.mux stopping (.lit 0) (.slice 9 8 (by decide) entryWord))
      (.mux busy (.sub (.reg .remaining) (.lit 1)) (.reg .remaining)))
  | _, .levels => .mux cold (.lit 0) (.mux committing (.input .idleLevels)
      (.mux (either clearOwner stopping) (.reg .idleLevels)
        (.mux runEntry entryLevels (.reg .levels))))
  | _, .enabled => .mux cold (.lit 0) (.mux committing (.input .idleEnabled)
      (.mux (either clearOwner stopping) (.reg .idleEnabled)
        (.mux runEntry (.slice 6 3 (by decide) entryWord) (.reg .enabled))))
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
    | .mode => .reg .mode | .pc => Expr.concat (a := 1) (b := 7) (.lit 0) (.reg .pc) | .remaining => .reg .remaining
    | .levels => .reg .levels | .enabled => .reg .enabled
    | .txConsumed => .reg .txConsumed | .rxLength => .reg .rxLength | .rxData => .reg .rxData
    | .readValid => readValid
    | .readBit => .mux readValid (Execution.readTree 5
        (fun k => .slice k.toNat 1 (by omega) (.reg .rxData)) (.input .readIndex)) (.lit 0)
    | .generation => .reg .generation | .transfer => .reg .transfer
    | .exhausted => either (.inv (space .generation)) (.inv (space .transfer))
    | .stage1 => .reg .stage1 | .stage2 => .reg .stage2
    | .virtualPC => .reg .virtualPC
    | .env0 => .mux (.equal (controlDepth currentControl) (.lit 2)) (.reg .inner)
        (.mux (.equal (controlDepth currentControl) (.lit 1)) (.reg .outer) (.lit 0))
    | .env1 => .mux (.equal (controlDepth currentControl) (.lit 2)) (.reg .outer) (.lit 0)

def inputs : Array (Sigma Input) :=
  #[⟨1,.initialize⟩,⟨3,.command⟩,⟨6,.address⟩,⟨32,.word⟩,⟨24,.control⟩,⟨7,.count⟩,⟨11,.virtualSpan⟩,
    ⟨3,.idleLevels⟩,⟨3,.idleEnabled⟩,⟨32,.txData⟩,⟨6,.txLength⟩,⟨6,.rxCapacity⟩,
    ⟨16,.expectedGeneration⟩,⟨16,.expectedTransfer⟩,⟨5,.readIndex⟩,⟨2,.rawInputs⟩]
def registers : Array (Sigma Register) :=
  Array.ofFn (fun k : Fin 64 => ⟨56,.word (BitVec.ofFin k)⟩) ++
  #[⟨64,.written⟩,⟨1,.pending⟩,⟨1,.valid⟩,⟨7,.count⟩,⟨3,.idleLevels⟩,⟨3,.idleEnabled⟩,
    ⟨16,.generation⟩,⟨16,.transfer⟩,⟨2,.mode⟩,⟨1,.retained⟩,⟨7,.pc⟩,⟨10,.virtualPC⟩,⟨11,.virtualSpan⟩,⟨22,.currentControl⟩,⟨3,.outer⟩,⟨3,.inner⟩,⟨8,.remaining⟩,
    ⟨3,.levels⟩,⟨3,.enabled⟩,⟨32,.txData⟩,⟨6,.txLength⟩,⟨6,.txConsumed⟩,
    ⟨32,.rxData⟩,⟨6,.rxLength⟩,⟨6,.rxCapacity⟩,⟨2,.stage1⟩,⟨2,.stage2⟩]
/-- Dense snapshot index for executable interpretation; it adds no circuit state. -/
def registerIndex : {w : Nat} → Register w → Nat
  | _,.word k => k.toNat
  | _,.written => 64 | _,.pending => 65 | _,.valid => 66 | _,.count => 67
  | _,.idleLevels => 68 | _,.idleEnabled => 69 | _,.generation => 70 | _,.transfer => 71
  | _,.mode => 72 | _,.retained => 73 | _,.pc => 74 | _,.virtualPC => 75
  | _,.virtualSpan => 76 | _,.currentControl => 77 | _,.outer => 78 | _,.inner => 79
  | _,.remaining => 80 | _,.levels => 81 | _,.enabled => 82 | _,.txData => 83
  | _,.txLength => 84 | _,.txConsumed => 85 | _,.rxData => 86 | _,.rxLength => 87
  | _,.rxCapacity => 88 | _,.stage1 => 89 | _,.stage2 => 90
def outputs : Array (Sigma Output) :=
  #[⟨1,.valid⟩,⟨1,.busy⟩,⟨1,.retained⟩,⟨1,.pending⟩,⟨1,.rejected⟩,
    ⟨2,.mode⟩,⟨8,.pc⟩,⟨8,.remaining⟩,⟨3,.levels⟩,⟨3,.enabled⟩,
    ⟨6,.txConsumed⟩,⟨6,.rxLength⟩,⟨32,.rxData⟩,⟨1,.readValid⟩,⟨1,.readBit⟩,
    ⟨16,.generation⟩,⟨16,.transfer⟩,⟨1,.exhausted⟩,⟨2,.stage1⟩,⟨2,.stage2⟩,⟨10,.virtualPC⟩,⟨3,.env0⟩,⟨3,.env1⟩]
def inputLabel : {w : Nat} → Input w → String
  | _,.initialize => "initialize" | _,.command => "command" | _,.address => "address"
  | _,.word => "word" | _,.control => "control" | _,.virtualSpan => "virtual_span" | _,.count => "count" | _,.idleLevels => "idle_levels"
  | _,.idleEnabled => "idle_enabled" | _,.txData => "tx_data" | _,.txLength => "tx_length"
  | _,.rxCapacity => "rx_capacity" | _,.expectedGeneration => "expected_generation"
  | _,.expectedTransfer => "expected_transfer" | _,.readIndex => "read_index" | _,.rawInputs => "raw_inputs"
def registerLabel : {w : Nat} → Register w → String
  | _,.word k => s!"word{k.toNat}" | _,.written => "written" | _,.pending => "pending"
  | _,.valid => "valid" | _,.count => "count" | _,.idleLevels => "idle_levels"
  | _,.idleEnabled => "idle_enabled" | _,.generation => "generation" | _,.transfer => "transfer"
  | _,.mode => "mode" | _,.retained => "retained" | _,.pc => "pc"
  | _,.virtualPC => "virtual_pc" | _,.virtualSpan => "virtual_span" | _,.currentControl => "current_control"
  | _,.outer => "outer" | _,.inner => "inner" | _,.remaining => "remaining"
  | _,.levels => "levels" | _,.enabled => "enabled" | _,.txData => "tx_data"
  | _,.txLength => "tx_length" | _,.txConsumed => "tx_consumed" | _,.rxData => "rx_data"
  | _,.rxLength => "rx_length" | _,.rxCapacity => "rx_capacity" | _,.stage1 => "stage1" | _,.stage2 => "stage2"
def outputLabel : {w : Nat} → Output w → String
  | _,.valid => "valid" | _,.busy => "busy" | _,.retained => "retained" | _,.pending => "pending"
  | _,.rejected => "rejected" | _,.mode => "mode" | _,.pc => "pc" | _,.remaining => "remaining"
  | _,.levels => "levels" | _,.enabled => "enabled" | _,.txConsumed => "tx_consumed"
  | _,.rxLength => "rx_length" | _,.rxData => "rx_data" | _,.readValid => "read_valid"
  | _,.readBit => "read_bit" | _,.generation => "generation" | _,.transfer => "transfer"
  | _,.exhausted => "exhausted" | _,.stage1 => "stage1" | _,.stage2 => "stage2"
  | _,.virtualPC => "virtual_pc" | _,.env0 => "env0" | _,.env1 => "env1"
def moduleText : Except String String := Emit.moduleText "pinwheel_buffered_counted"
  circuit inputs registers outputs inputLabel registerLabel outputLabel

end Pinwheel.Hardware.Buffered.Counted
