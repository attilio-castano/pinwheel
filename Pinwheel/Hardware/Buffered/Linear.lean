import Pinwheel.Hardware.Execution.Memory
import Pinwheel.Hardware.Emit

/-! Opt-in programmable linear buffered circuit. There is no protocol dispatch:
the reloadable words control timed output, one-bit TX consumption and entry RX.
This target deliberately exposes a parallel test interface and a 128x32 flip-flop
program bank; it does not replace the paired SRAM/package implementation. -/
namespace Pinwheel.Hardware.Buffered.Linear
open Pinwheel.Hardware

inductive Input : Nat → Type where
  | initialize : Input 1
  | command : Input 3
  | address : Input 7
  | word : Input 32
  | count : Input 8
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
  | word : BitVec 7 → Register 32
  | written : Register 128
  | pending : Register 1
  | valid : Register 1
  | count : Register 8
  | idleLevels : Register 3
  | idleEnabled : Register 3
  | generation : Register 16
  | transfer : Register 16
  | mode : Register 2
  | retained : Register 1
  | pc : Register 8
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
def covered : E 1 := (List.finRange 128).foldl (fun acc k =>
  both acc (either (.inv (.ult (.lit (BitVec.ofNat 8 k.val)) (.input .count)))
    (.slice k.val 1 (by omega) (.reg .written)))) (.lit 1)
def countValid : E 1 := both (.inv (.zero (.input .count)))
  (.inv (.ult (.lit 128) (.input .count)))
def committing : E 1 := .mux (both free (cmd 2))
  (both (.reg .pending) (both countValid (both covered (space .generation)))) (.lit 0)
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
def entryPC : E 8 := .mux starting (.lit 0) (increment (.reg .pc))
def entryWord : E 32 := .mux entering
  (Execution.readTree 7 (fun k => .reg (.word k)) (.slice 0 7 (by decide) entryPC)) (.lit 0)
def kind : E 3 := .slice 0 3 (by decide) entryWord
def isKind (n : BitVec 3) : E 1 := .equal kind (.lit n)
def entryCount : E 8 := .reg .count
def inBounds : E 1 := .ult entryPC entryCount
def canonical : E 1 :=
  let common := both (.zero (.slice 24 8 (by decide) entryWord))
    (.inv (.equal (.slice 22 2 (by decide) entryWord) (.lit 3)))
  .mux (isKind 0) (both common (.zero (.slice 17 5 (by decide) entryWord)))
    (.mux (isKind 1) (both common (both (.zero (.slice 17 3 (by decide) entryWord))
        (.inv (.equal (.slice 20 2 (by decide) entryWord) (.lit 3)))))
      (.mux (isKind 2) (both common (.zero (.slice 20 2 (by decide) entryWord)))
        (either (.equal entryWord (.lit 3)) (.equal entryWord (.lit 4)))))
def legalEntry : E 1 := both inBounds canonical
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
      (.inv (.ult (.lit (BitVec.ofNat 8 k.toNat)) (.input .count)))) (.lit 0)
    (.mux (both writing (.equal (.input .address) (.lit k))) (.input .word) (.reg (.word k)))
  | _, .written => .mux resetting (.lit 0) (.mux writing
      (pack fun k => .mux (.equal (.input .address) (.lit (BitVec.ofNat 7 k.val))) (.lit 1)
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
    | .mode => .reg .mode | .pc => .reg .pc | .remaining => .reg .remaining
    | .levels => .reg .levels | .enabled => .reg .enabled
    | .txConsumed => .reg .txConsumed | .rxLength => .reg .rxLength | .rxData => .reg .rxData
    | .readValid => readValid
    | .readBit => .mux readValid (Execution.readTree 5
        (fun k => .slice k.toNat 1 (by omega) (.reg .rxData)) (.input .readIndex)) (.lit 0)
    | .generation => .reg .generation | .transfer => .reg .transfer
    | .exhausted => either (.inv (space .generation)) (.inv (space .transfer))
    | .stage1 => .reg .stage1 | .stage2 => .reg .stage2

def inputs : Array (Sigma Input) :=
  #[⟨1,.initialize⟩,⟨3,.command⟩,⟨7,.address⟩,⟨32,.word⟩,⟨8,.count⟩,
    ⟨3,.idleLevels⟩,⟨3,.idleEnabled⟩,⟨32,.txData⟩,⟨6,.txLength⟩,⟨6,.rxCapacity⟩,
    ⟨16,.expectedGeneration⟩,⟨16,.expectedTransfer⟩,⟨5,.readIndex⟩,⟨2,.rawInputs⟩]
def registers : Array (Sigma Register) :=
  Array.ofFn (fun k : Fin 128 => ⟨32,.word (BitVec.ofFin k)⟩) ++
  #[⟨128,.written⟩,⟨1,.pending⟩,⟨1,.valid⟩,⟨8,.count⟩,⟨3,.idleLevels⟩,⟨3,.idleEnabled⟩,
    ⟨16,.generation⟩,⟨16,.transfer⟩,⟨2,.mode⟩,⟨1,.retained⟩,⟨8,.pc⟩,⟨8,.remaining⟩,
    ⟨3,.levels⟩,⟨3,.enabled⟩,⟨32,.txData⟩,⟨6,.txLength⟩,⟨6,.txConsumed⟩,
    ⟨32,.rxData⟩,⟨6,.rxLength⟩,⟨6,.rxCapacity⟩,⟨2,.stage1⟩,⟨2,.stage2⟩]
def outputs : Array (Sigma Output) :=
  #[⟨1,.valid⟩,⟨1,.busy⟩,⟨1,.retained⟩,⟨1,.pending⟩,⟨1,.rejected⟩,
    ⟨2,.mode⟩,⟨8,.pc⟩,⟨8,.remaining⟩,⟨3,.levels⟩,⟨3,.enabled⟩,
    ⟨6,.txConsumed⟩,⟨6,.rxLength⟩,⟨32,.rxData⟩,⟨1,.readValid⟩,⟨1,.readBit⟩,
    ⟨16,.generation⟩,⟨16,.transfer⟩,⟨1,.exhausted⟩,⟨2,.stage1⟩,⟨2,.stage2⟩]
def inputLabel : {w : Nat} → Input w → String
  | _,.initialize => "initialize" | _,.command => "command" | _,.address => "address"
  | _,.word => "word" | _,.count => "count" | _,.idleLevels => "idle_levels"
  | _,.idleEnabled => "idle_enabled" | _,.txData => "tx_data" | _,.txLength => "tx_length"
  | _,.rxCapacity => "rx_capacity" | _,.expectedGeneration => "expected_generation"
  | _,.expectedTransfer => "expected_transfer" | _,.readIndex => "read_index" | _,.rawInputs => "raw_inputs"
def registerLabel : {w : Nat} → Register w → String
  | _,.word k => s!"word{k.toNat}" | _,.written => "written" | _,.pending => "pending"
  | _,.valid => "valid" | _,.count => "count" | _,.idleLevels => "idle_levels"
  | _,.idleEnabled => "idle_enabled" | _,.generation => "generation" | _,.transfer => "transfer"
  | _,.mode => "mode" | _,.retained => "retained" | _,.pc => "pc" | _,.remaining => "remaining"
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
def moduleText : Except String String := Emit.moduleText "pinwheel_buffered_linear"
  circuit inputs registers outputs inputLabel registerLabel outputLabel

end Pinwheel.Hardware.Buffered.Linear
