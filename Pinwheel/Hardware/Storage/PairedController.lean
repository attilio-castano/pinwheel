import Pinwheel.Hardware.Storage.SramAssembly

/-! Opt-in paired-successor controller. All control/parameter state is emitted
from this typed circuit; the one 512x64 synchronous array remains external.
The existing sampler, serial receiver and result observer are reused unchanged.
The Python execution model and saved-netlist checks are independent evidence;
no complete compiler or package refinement theorem is asserted here. -/
namespace Pinwheel.Hardware.Storage.PairedController
open Pinwheel.Hardware Pinwheel.Hardware.Storage Pinwheel.Hardware.Loader
open Pinwheel.Hardware.Storage.SramController (Reads Out Port bypass)

inductive Register : Nat → Type where
  | parameter : Bool → BitVec 5 → Register 20
  | boot : Bool → Register 32
  | idle : Bool → Register 6
  | active : Register 1 | valid : Register 1 | pending : Register 1 | cursor : Register 9
  | current : Register 32 | cached : Register 20
  | mode : Register 3 | remaining : Register 8 | waitLeft : Register 8
  | levels : Register 3 | enabled : Register 3 | samples : Register 16 | payload : Register 8

abbrev Input := Reads Machine.Input
inductive Computation where
  | incoming | data | init | reset | resetting | busy | accepting | inactive | exited | branch | commit | start | bootWord | successor | entered | validating | parameterBank | parameterIndex0 | parameterIndex1 | parameter0 | parameter1 | good | push | rejected | selected | idleWord | checkBits | guarded | ready | timeout | fault | dispatch | entering | enteringRun | ending | stopping | entrySamples | captured | entryPayload | shifted | entryLevels | nextMode | nextWord | nextBusy | writing
  deriving DecidableEq, BEq
inductive GraphInput : Nat → Type where
  | base : Machine.Input w → GraphInput w
  | q : Bool → GraphInput 64
  | node : Computation → GraphInput 64
abbrev E := Expr GraphInput Register
abbrev Bank := {w : Nat} → Register w → E w
def both (a b : E 1) : E 1 := .band a b
def either (a b : E w) : E w := .inv (.band (.inv a) (.inv b))
def cmd (n : BitVec 3) : E 1 := .equal (.input (.base .command)) (.lit n)
def incoming : E 2 := .slice 0 2 (by decide) (.input (.node .incoming))
def incomingExpr : E 2 := .input (.base .incoming)
def data : E 64 := .slice 0 64 (by decide) (.input (.node .data))
def dataExpr : E 64 := .input (.base .data)
def init : E 1 := .slice 0 1 (by decide) (.input (.node .init))
def initExpr : E 1 := .input (.base .init)
def reset : E 1 := .slice 0 1 (by decide) (.input (.node .reset))
def resetExpr : E 1 := either (.input (.base .reset)) (cmd 7)
def resetting : E 1 := .slice 0 1 (by decide) (.input (.node .resetting))
def resettingExpr : E 1 := either init reset
def busy : E 1 := .slice 0 1 (by decide) (.input (.node .busy))
def busyExpr : E 1 := both (.inv (.zero (.reg .mode))) (.ult (.reg .mode) (.lit 5))
def accepting : E 1 := .slice 0 1 (by decide) (.input (.node .accepting))
def acceptingExpr : E 1 := .inv (either resetting busy)
def inactive : E 1 := .slice 0 1 (by decide) (.input (.node .inactive))
def inactiveExpr : E 1 := .inv (.reg .active)
def isMode (n : BitVec 3) : E 1 := .equal (.reg .mode) (.lit n)
def atCursor (n : BitVec 9) : E 1 := .equal (.reg .cursor) (.lit n)
def below (n : BitVec 9) : E 1 := .ult (.reg .cursor) (.lit n)
def kind (word : E 32) : E 3 := .slice 0 3 (by decide) word
def duration (word : E 32) : E 8 := .slice 9 8 (by decide) word
def index (word : E 32) : E 5 := .slice 17 5 (by decide) word
def row (word : E 32) : E 8 := .slice 22 8 (by decide) word
def isKind (word : E 32) (n : BitVec 3) : E 1 := .equal (kind word) (.lit n)
def terminal (word : E 32) : E 1 := either (isKind word 4) (isKind word 7)
def bit (selector : E 1) : E 1 :=
  .mux selector (.slice 1 1 (by decide) incoming) (.slice 0 1 (by decide) incoming)
def pack : {n : Nat} → (Fin n → E 1) → E n
  | 0, _ => .lit 0
  | 1, f => f 0
  | n+2, f => Expr.concat (a := n+1) (b := 1) (pack (fun k => f k.succ)) (f 0)
def capture (descriptor : E 6) (old : E 16) : E 16 := pack fun k =>
  .mux (both (.slice 0 1 (by decide) descriptor)
      (.equal (.slice 2 4 (by decide) descriptor) (.lit (BitVec.ofNat 4 k.val))))
    (bit (.slice 1 1 (by decide) descriptor)) (.slice k.val 1 (by omega) old)
def exited : E 16 := .slice 0 16 (by decide) (.input (.node .exited))
def exitedExpr : E 16 := .mux (isMode 3)
  (capture (.slice 6 6 (by decide) (.reg .cached)) (.reg .samples)) (.reg .samples)
def branch : E 1 := .slice 0 1 (by decide) (.input (.node .branch))
def branchExpr : E 1 := both (isMode 3)
  (Execution.readTree 4 (fun k => .slice k.toNat 1 (by omega) exited)
    (.slice 16 4 (by decide) (.reg .cached)))
def commit : E 1 := .slice 0 1 (by decide) (.input (.node .commit))
def commitExpr : E 1 := both accepting (both (cmd 3) (both (.reg .pending) (atCursor 290)))
def start : E 1 := .slice 0 1 (by decide) (.input (.node .start))
def startExpr : E 1 := both accepting (both (cmd 5) (.reg .valid))
def bootWord : E 32 := .slice 0 32 (by decide) (.input (.node .bootWord))
def bootWordExpr : E 32 := .mux (.reg .active) (.reg (.boot true)) (.reg (.boot false))
def successor : E 32 := .slice 0 32 (by decide) (.input (.node .successor))
def successorExpr : E 32 := .mux branch (.slice 32 32 (by decide) (.input (.q false)))
  (.slice 0 32 (by decide) (.input (.q false)))
def entered : E 32 := .slice 0 32 (by decide) (.input (.node .entered))
def enteredExpr : E 32 := .mux busy successor bootWord

/-- One table read is shared by entry and low-half/boot validation. The second
is needed for high-half validation. Address/bank selection never depends on the
validation result, so there is no combinational admission/read loop. -/
def validating : E 1 := .slice 0 1 (by decide) (.input (.node .validating))
def validatingExpr : E 1 := both accepting (both (cmd 2) (both (.reg .pending)
  (both (.inv (below 32)) (below 289))))
def parameterBank : E 1 := .slice 0 1 (by decide) (.input (.node .parameterBank))
def parameterBankExpr : E 1 := .mux validating inactive (.reg .active)
def parameterIndex0 : E 5 := .slice 0 5 (by decide) (.input (.node .parameterIndex0))
def parameterIndex0Expr : E 5 := index (.mux validating (.slice 0 32 (by decide) data) entered)
def parameterIndex1 : E 5 := .slice 0 5 (by decide) (.input (.node .parameterIndex1))
def parameterIndex1Expr : E 5 := .slice 49 5 (by decide) data
def lookup (address : E 5) : E 20 := .mux parameterBank
  (Execution.readTree 5 (fun k => .reg (.parameter true k)) address)
  (Execution.readTree 5 (fun k => .reg (.parameter false k)) address)
def parameter0 : E 20 := .slice 0 20 (by decide) (.input (.node .parameter0))
def parameter0Expr : E 20 := lookup parameterIndex0
def parameter1 : E 20 := .slice 0 20 (by decide) (.input (.node .parameter1))
def parameter1Expr : E 20 := lookup parameterIndex1
def captureValid (d : E 6) : E 1 := either (.slice 0 1 (by decide) d) (.zero d)
def allowed (p : E 20) (mask : BitVec 20) : E 1 := .zero (.band p (.lit (~~~mask)))
def tokenValid (word : E 32) (p : E 20) : E 1 :=
  both (.zero (.slice 30 2 (by decide) word))
    (.mux (terminal word) (either (.equal word (.lit 4)) (.equal word (.lit 7)))
      (.mux (isKind word 0) (both (allowed p 63) (captureValid (.slice 0 6 (by decide) p)))
        (.mux (isKind word 1) (allowed p 0x3000)
          (.mux (isKind word 2) (both (captureValid (.slice 0 6 (by decide) p))
              (captureValid (.slice 6 6 (by decide) p)))
            (.mux (isKind word 3) (allowed p 0xf0ff)
              (.mux (isKind word 5) (both (allowed p 7)
                  (.inv (.equal (.slice 0 2 (by decide) p) (.lit 3))))
                (both (allowed p 511) (captureValid (.slice 0 6 (by decide) p)))))))))
def good : E 1 := .slice 0 1 (by decide) (.input (.node .good))
def goodExpr : E 1 := .mux (below 32) (.zero (.slice 20 44 (by decide) data))
  (.mux (below 288) (both (tokenValid (.slice 0 32 (by decide) data) parameter0)
      (tokenValid (.slice 32 32 (by decide) data) parameter1))
    (.mux (atCursor 288) (both (.zero (.slice 32 32 (by decide) data))
        (tokenValid (.slice 0 32 (by decide) data) parameter0))
      (both (atCursor 289) (.zero (.slice 6 58 (by decide) data)))))
def push : E 1 := .slice 0 1 (by decide) (.input (.node .push))
def pushExpr : E 1 := both accepting (both (cmd 2) (both (.reg .pending) (both (below 290) good)))
def rejected : E 1 := .slice 0 1 (by decide) (.input (.node .rejected))
def rejectedExpr : E 1 := both (.inv resetting) (both (.inv (cmd 0))
  (.inv (both accepting (either (either (cmd 0) (cmd 1))
    (either (cmd 4) (either push (either commit start)))))))
def selected : E 1 := .slice 0 1 (by decide) (.input (.node .selected))
def selectedExpr : E 1 := .mux commit inactive (.reg .active)
def idleWord : E 6 := .slice 0 6 (by decide) (.input (.node .idleWord))
def idleWordExpr : E 6 := .mux (both (.inv init) (either (.reg .valid) commit))
  (.mux selected (.reg (.idle true)) (.reg (.idle false))) (.lit 0)
def checkBits : E 4 := .slice 0 4 (by decide) (.input (.node .checkBits))
def checkBitsExpr : E 4 := .slice 12 4 (by decide) (.reg .cached)
def guarded : E 1 := .slice 0 1 (by decide) (.input (.node .guarded))
def guardedExpr : E 1 := .equal (.band incoming (.slice 0 2 (by decide) checkBits))
  (.band (.slice 2 2 (by decide) checkBits) (.slice 0 2 (by decide) checkBits))
def ready : E 1 := .slice 0 1 (by decide) (.input (.node .ready))
def readyExpr : E 1 := .equal (bit (.slice 0 1 (by decide) checkBits))
  (.slice 1 1 (by decide) checkBits)
def timeout : E 1 := .slice 0 1 (by decide) (.input (.node .timeout))
def timeoutExpr : E 1 := either (both (isMode 2) (both (.inv ready) (.zero (.reg .remaining))))
  (both (isMode 4) (both (.inv guarded) (.zero (.reg .waitLeft))))
def fault : E 1 := .slice 0 1 (by decide) (.input (.node .fault))
def faultExpr : E 1 := both (isMode 3) (.inv guarded)
def dispatch : E 1 := .slice 0 1 (by decide) (.input (.node .dispatch))
def dispatchExpr : E 1 := both busy (both (.inv (either fault timeout))
  (.mux (isMode 2) ready (both (.zero (.reg .remaining))
    (.mux (isMode 4) guarded (.lit 1)))))
def entering : E 1 := .slice 0 1 (by decide) (.input (.node .entering))
def enteringExpr : E 1 := both (.inv resetting) (either start dispatch)
def enteringRun : E 1 := .slice 0 1 (by decide) (.input (.node .enteringRun))
def enteringRunExpr : E 1 := both entering (.inv (terminal entered))
def ending : E 1 := .slice 0 1 (by decide) (.input (.node .ending))
def endingExpr : E 1 := both (.inv resetting) (both busy (either timeout fault))
def stopping : E 1 := .slice 0 1 (by decide) (.input (.node .stopping))
def stoppingExpr : E 1 := either resetting (either commit
  (either ending (both entering (terminal entered))))
def entrySamples : E 16 := .slice 0 16 (by decide) (.input (.node .entrySamples))
def entrySamplesExpr : E 16 := .mux start (.lit 0) exited
def captured : E 16 := .slice 0 16 (by decide) (.input (.node .captured))
def capturedExpr : E 16 := .mux (either (isKind entered 0) (either (isKind entered 2) (isKind entered 6)))
  (capture (.slice 0 6 (by decide) parameter0) entrySamples) entrySamples
def entryPayload : E 8 := .slice 0 8 (by decide) (.input (.node .entryPayload))
def entryPayloadExpr : E 8 := .mux start (.slice 0 8 (by decide) data) (.reg .payload)
def shifted : E 8 := .slice 0 8 (by decide) (.input (.node .shifted))
def shiftedExpr : E 8 := .mux (.slice 2 1 (by decide) parameter0)
  (.concat (.slice 0 7 (by decide) entryPayload) (.lit (0#1)))
  (.concat (.lit (0#1)) (.slice 1 7 (by decide) entryPayload))
def entryLevels : E 3 := .slice 0 3 (by decide) (.input (.node .entryLevels))
def entryLevelsExpr : E 3 :=
  let levels := .slice 3 3 (by decide) entered
  let preserve := .slice 6 3 (by decide) parameter0
  .mux (isKind entered 6) (either (.band levels (.inv preserve)) (.band (.reg .levels) preserve))
    (.mux (isKind entered 5) (pack fun k =>
      .mux (.equal (.slice 0 2 (by decide) parameter0) (.lit (BitVec.ofNat 2 k.val)))
        (.mux (.slice 2 1 (by decide) parameter0)
          (.slice 7 1 (by decide) entryPayload) (.slice 0 1 (by decide) entryPayload))
        (.slice k.val 1 (by omega) levels)) levels)
def nextMode : E 3 := .slice 0 3 (by decide) (.input (.node .nextMode))
def nextModeExpr : E 3 := .mux (either resetting commit) (.lit 0)
  (.mux ending (.mux fault (.lit 7) (.lit 6))
    (.mux entering (.mux (isKind entered 4) (.lit 5)
      (.mux (isKind entered 7) (.lit 7)
        (.mux (.ult (kind entered) (.lit 4)) (.sub (kind entered) (.lit 7)) (.lit 1)))) (.reg .mode)))
def nextWord : E 32 := .slice 0 32 (by decide) (.input (.node .nextWord))
def nextWordExpr : E 32 := .mux entering entered (.reg .current)
def nextBusy : E 1 := .slice 0 1 (by decide) (.input (.node .nextBusy))
def nextBusyExpr : E 1 := both (.inv (.zero nextMode)) (.ult nextMode (.lit 5))
def writing : E 1 := .slice 0 1 (by decide) (.input (.node .writing))
def writingExpr : E 1 := both push (both (.inv (below 32)) (below 288))
def request : {w : Nat} → Port w → E w
  | _, .address _ => .mux writing
      (.concat inactive (.slice 0 8 (by decide) (.sub (.reg .cursor) (.lit 32))))
      (.concat (.reg .active) (row nextWord))
  | _, .data => data
  | _, .write => writing
  | _, .read => both (.inv writing) nextBusy

def next : Bank
  | _, .parameter b k => .mux (both push (both (below 32)
      (both (.equal inactive (.lit (BitVec.ofBool b)))
        (.equal (.reg .cursor) (.lit (BitVec.ofNat 9 k.toNat))))))
      (.slice 0 20 (by decide) data) (.reg (.parameter b k))
  | _, .boot b => .mux (both push (both (atCursor 288) (.equal inactive (.lit (BitVec.ofBool b)))))
      (.slice 0 32 (by decide) data) (.reg (.boot b))
  | _, .idle b => .mux (both push (both (atCursor 289) (.equal inactive (.lit (BitVec.ofBool b)))))
      (.slice 0 6 (by decide) data) (.reg (.idle b))
  | _, .active => .mux init (.lit 0) selected
  | _, .valid => .mux init (.lit 0) (either commit (.reg .valid))
  | _, .pending => .mux resetting (.lit 0)
      (.mux accepting (.mux (cmd 1) (.lit 1) (.mux (either (cmd 4) commit) (.lit 0) (.reg .pending))) (.reg .pending))
  | _, .cursor => .mux (either resetting (both accepting (either (cmd 1) (either (cmd 4) commit)))) (.lit 0)
      (.mux push (.sub (.reg .cursor) (.lit 511)) (.reg .cursor))
  | _, .current => nextWord
  | _, .cached => .mux enteringRun parameter0 (.reg .cached)
  | _, .mode => nextMode
  | _, .remaining => .mux stopping (.lit 0) (.mux enteringRun (duration entered)
      (.mux busy (.mux (both (isMode 4) (.inv guarded)) (duration (.reg .current))
        (.sub (.reg .remaining) (.lit 1))) (.reg .remaining)))
  | _, .waitLeft => .mux stopping (.lit 0)
      (.mux enteringRun (.mux (isKind entered 3) (.slice 0 8 (by decide) parameter0) (.lit 0))
        (.mux (both busy (isMode 4)) (.mux guarded (.slice 0 8 (by decide) (.reg .cached))
          (.sub (.reg .waitLeft) (.lit 1))) (.reg .waitLeft)))
  | _, .levels => .mux stopping (.slice 0 3 (by decide) idleWord)
      (.mux enteringRun entryLevels (.reg .levels))
  | _, .enabled => .mux stopping (.slice 3 3 (by decide) idleWord)
      (.mux enteringRun (.slice 6 3 (by decide) entered) (.reg .enabled))
  | _, .samples => .mux (either resetting commit) (.lit 0)
      (.mux entering (.mux enteringRun captured entrySamples) (.reg .samples))
  | _, .payload => .mux resetting (.lit 0)
      (.mux enteringRun (.mux (isKind entered 5) shifted entryPayload)
        (.mux start entryPayload (.reg .payload)))

def body : Circuit GraphInput Register (Out Machine.Output) := {
  next := next
  output := fun {w} o => match w, o with
    | _, .port p => request p
    | _, .base (.control (.state r)) => match r with
      | .active => .reg .active | .valid => .reg .valid | .pending => .reg .pending | .cursor => .reg .cursor
    | _, .base (.control .push) => push | _, .base (.control .commit) => commit
    | _, .base (.control .start) => start | _, .base (.control .rejected) => rejected
    | _, .base (.core .busy) => busy
    | _, .base (.core .readA) => .mux busy (row (.reg .current)) (.lit 0)
    | _, .base (.core .readB) => row nextWord
    | _, .base (.core (.state r)) => match r with
      | .mode => .reg .mode | .pc => .mux busy (row (.reg .current)) (.lit 0)
      | .remaining => .reg .remaining | .waitLeft => .reg .waitLeft
      | .levels => .reg .levels | .enabled => .reg .enabled
      | .sample k => .slice k.val 1 (by omega) (.reg .samples) }

def registers : Array (Sigma Register) :=
  (#[false,true]).flatMap (fun b => (Array.ofFn fun k : Fin 32 =>
    ⟨20, Register.parameter b (BitVec.ofFin k)⟩) ++ #[⟨32,.boot b⟩,⟨6,.idle b⟩]) ++
  #[⟨1,.active⟩,⟨1,.valid⟩,⟨1,.pending⟩,⟨9,.cursor⟩,⟨32,.current⟩,⟨20,.cached⟩,
    ⟨3,.mode⟩,⟨8,.remaining⟩,⟨8,.waitLeft⟩,⟨3,.levels⟩,⟨3,.enabled⟩,⟨16,.samples⟩,⟨8,.payload⟩]
def label : {w : Nat} → Register w → String
  | _, .parameter b k => s!"parameter_b{if b then 1 else 0}_w{k.toNat}"
  | _, .boot b => s!"boot_b{if b then 1 else 0}" | _, .idle b => s!"idle_b{if b then 1 else 0}"
  | _, .active => "active" | _, .valid => "valid" | _, .pending => "pending" | _, .cursor => "cursor"
  | _, .current => "current" | _, .cached => "cached" | _, .mode => "mode"
  | _, .remaining => "remaining" | _, .waitLeft => "wait_left" | _, .levels => "levels"
  | _, .enabled => "enabled" | _, .samples => "samples" | _, .payload => "payload"
abbrev FullRegister := Extended (Chip.Register Register) HostResult.Register
def fullRegisters : Array (Sigma FullRegister) :=
  registers.map (fun ⟨w,r⟩ => ⟨w,.inner (.inner (.inner (.inner r)))⟩) ++
  Backend.Policy.serialRegisters.map (fun ⟨w,r⟩ => ⟨w,.inner (.inner (.inner (.extra r)))⟩) ++
  Backend.Policy.sampledRegisterList.map (fun ⟨w,r⟩ => ⟨w,.inner (.inner (.extra r))⟩) ++
  HostResult.registers.map (fun ⟨w,r⟩ => ⟨w,.extra r⟩)
def fullLabel : {w : Nat} → FullRegister w → String
  | _, .inner (.inner (.inner (.inner r))) => label r
  | _, .inner (.inner (.inner (.extra r))) => Backend.Policy.serialLabel r
  | _, .inner (.inner (.extra r)) => Backend.Policy.sampledRegisterLabel r
  | _, .inner (.extra r) => nomatch r
  | _, .extra r => HostResult.label r
def inputs (is : Array (Sigma I)) : Array (Sigma (Reads I)) :=
  is.map (fun ⟨w,p⟩ => ⟨w,.base p⟩) ++ #[⟨64,.q false⟩]
def outputs (os : Array (Sigma O)) : Array (Sigma (Out O)) :=
  os.map (fun ⟨w,p⟩ => ⟨w,.base p⟩) ++ #[⟨9,.port (.address false)⟩,
    ⟨64,.port .data⟩,⟨1,.port .write⟩,⟨1,.port .read⟩]
/-- Named 64-bit wires carry zero-extended values only; they add no state.
The lowerer rejects duplicate, forward and missing references before emitting.
Explicit sharing keeps the standard emitter from retraversing expanded trees. -/
def bindings : List (Computation × E 64) := [
  (.incoming, .concat (.lit (0 : BitVec 62)) incomingExpr),
  (.data, dataExpr),
  (.init, .concat (.lit (0 : BitVec 63)) initExpr),
  (.reset, .concat (.lit (0 : BitVec 63)) resetExpr),
  (.resetting, .concat (.lit (0 : BitVec 63)) resettingExpr),
  (.busy, .concat (.lit (0 : BitVec 63)) busyExpr),
  (.accepting, .concat (.lit (0 : BitVec 63)) acceptingExpr),
  (.inactive, .concat (.lit (0 : BitVec 63)) inactiveExpr),
  (.exited, .concat (.lit (0 : BitVec 48)) exitedExpr),
  (.branch, .concat (.lit (0 : BitVec 63)) branchExpr),
  (.commit, .concat (.lit (0 : BitVec 63)) commitExpr),
  (.start, .concat (.lit (0 : BitVec 63)) startExpr),
  (.bootWord, .concat (.lit (0 : BitVec 32)) bootWordExpr),
  (.successor, .concat (.lit (0 : BitVec 32)) successorExpr),
  (.entered, .concat (.lit (0 : BitVec 32)) enteredExpr),
  (.validating, .concat (.lit (0 : BitVec 63)) validatingExpr),
  (.parameterBank, .concat (.lit (0 : BitVec 63)) parameterBankExpr),
  (.parameterIndex0, .concat (.lit (0 : BitVec 59)) parameterIndex0Expr),
  (.parameterIndex1, .concat (.lit (0 : BitVec 59)) parameterIndex1Expr),
  (.parameter0, .concat (.lit (0 : BitVec 44)) parameter0Expr),
  (.parameter1, .concat (.lit (0 : BitVec 44)) parameter1Expr),
  (.good, .concat (.lit (0 : BitVec 63)) goodExpr),
  (.push, .concat (.lit (0 : BitVec 63)) pushExpr),
  (.rejected, .concat (.lit (0 : BitVec 63)) rejectedExpr),
  (.selected, .concat (.lit (0 : BitVec 63)) selectedExpr),
  (.idleWord, .concat (.lit (0 : BitVec 58)) idleWordExpr),
  (.checkBits, .concat (.lit (0 : BitVec 60)) checkBitsExpr),
  (.guarded, .concat (.lit (0 : BitVec 63)) guardedExpr),
  (.ready, .concat (.lit (0 : BitVec 63)) readyExpr),
  (.timeout, .concat (.lit (0 : BitVec 63)) timeoutExpr),
  (.fault, .concat (.lit (0 : BitVec 63)) faultExpr),
  (.dispatch, .concat (.lit (0 : BitVec 63)) dispatchExpr),
  (.entering, .concat (.lit (0 : BitVec 63)) enteringExpr),
  (.enteringRun, .concat (.lit (0 : BitVec 63)) enteringRunExpr),
  (.ending, .concat (.lit (0 : BitVec 63)) endingExpr),
  (.stopping, .concat (.lit (0 : BitVec 63)) stoppingExpr),
  (.entrySamples, .concat (.lit (0 : BitVec 48)) entrySamplesExpr),
  (.captured, .concat (.lit (0 : BitVec 48)) capturedExpr),
  (.entryPayload, .concat (.lit (0 : BitVec 56)) entryPayloadExpr),
  (.shifted, .concat (.lit (0 : BitVec 56)) shiftedExpr),
  (.entryLevels, .concat (.lit (0 : BitVec 61)) entryLevelsExpr),
  (.nextMode, .concat (.lit (0 : BitVec 61)) nextModeExpr),
  (.nextWord, .concat (.lit (0 : BitVec 32)) nextWordExpr),
  (.nextBusy, .concat (.lit (0 : BitVec 63)) nextBusyExpr),
  (.writing, .concat (.lit (0 : BitVec 63)) writingExpr)]

def references : E w → List Computation
  | .input (.node n) => [n]
  | .input _ | .reg _ | .lit _ => []
  | .inv e | .slice _ _ _ e | .zero e => references e
  | .concat a b | .band a b | .sub a b | .equal a b | .ult a b => references a ++ references b
  | .mux c a b => references c ++ references a ++ references b

def lower (base : {w : Nat} → Input w → Expr I Register w)
    (env : Computation → Expr I Register 64) (e : E w) : Expr I Register w :=
  e.bind (fun p => match p with
    | .base q => base (.base q) | .q b => base (.q b) | .node n => env n) (.reg)

def lift (e : Expr I Register w) : Expr (WithWire I 64) Register w :=
  e.bind (fun p => .input (.input p)) (.reg)

def construct : {I : Nat → Type} →
    ({w : Nat} → Input w → Expr I Register w) →
    (Computation → Expr I Register 64) → List Computation →
    List (Computation × E 64) → Except String (Netlist Register (Out Machine.Output) I)
  | _, base, env, seen, [] => do
    let used := (registers.toList.flatMap fun ⟨_,r⟩ => references (body.next r)) ++
      ((outputs Machine.outputs).toList.flatMap fun ⟨_,o⟩ => references (body.output o))
    unless used.all seen.contains do throw "Unbound paired body computation"
    return .finish { next := fun r => lower base env (body.next r)
                     output := fun o => lower base env (body.output o) }
  | _, base, env, seen, (name,e)::rest => do
    if seen.contains name then throw "Duplicate paired computation"
    unless (references e).all seen.contains do throw "Forward or missing paired computation"
    let tail ← construct (fun p => lift (base p))
      (fun n => if n == name then .input .wire else lift (env n)) (name::seen) rest
    return .letWire (lower base env e) tail

def core : Except String (Netlist Register (Out Machine.Output) Input) :=
  construct (.input) (fun _ => .lit 0) [] bindings

def coreText : Except String String := match core with
  | .error e => .error e
  | .ok n => Netlist.moduleText "pinwheel_paired_core_controller" n
    (inputs Machine.inputs) registers (outputs Machine.outputs)
    (SramAssembly.inputLabel Machine.inputLabel) label (SramAssembly.outputLabel Machine.outputLabel)

def chipText : Except String String := match core with
  | .error e => .error e
  | .ok n =>
    let chip := SramAssembly.observer.wrap ((bypass Chip.pinMap).wrap
      ((bypass Feeder.sampler).wrap ((bypass Serial.receiver).wrap n)))
    Netlist.moduleText "pinwheel_paired_controller" chip
    (inputs Backend.Policy.chipInputs) fullRegisters (outputs Backend.Policy.chipOutputs)
    (SramAssembly.inputLabel Backend.Policy.chipInputLabel) fullLabel
    (SramAssembly.outputLabel Backend.Policy.chipOutputLabel)

end Pinwheel.Hardware.Storage.PairedController
