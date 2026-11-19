import Pinwheel.Hardware.StreamingReady.Core

/-! A bounded forward sequencer over the sampled-ready core. Ordinary words
    still use the existing pin phases, guards, credit, and ownership logic.
    The selected instruction word is the only difference between the two
    instruction readers. -/
namespace Pinwheel.Hardware.StreamingReady.SegmentCore
open Pinwheel.Hardware

inductive Register (a : Nat) : Nat → Type where
  | base : Core.Register a w → Register a w
  | lastCapture : Register a 1
  | captureValid : Register a 1
  | txClosed : Register a 1
  | fetched : Register a 64

abbrev E (a : Nat) := Expr Core.Input (Register a)

def project (s : Values (Register a)) : Values (Core.Register a) := fun reg => s (.base reg)

def lift (expr : Core.E a w) : E a w := expr.bind .input (fun reg => .reg (.base reg))

def both (left right : E a 1) : E a 1 := .band left right
def either (left right : E a 1) : E a 1 := .inv (.band (.inv left) (.inv right))

def field (offset width : Nat) (within : offset + width ≤ 64) : E a width :=
  .slice offset width within (.reg .fetched)

def fetching : E a 1 := both (lift Core.fetching) (lift Core.entryBounds)
def kind : E a 3 := field 0 3 (by decide)
def count : E a 16 := field 3 16 (by decide)
def target : E a 7 := .concat (.lit (0 : BitVec 1)) (field 3 6 (by decide))
def branchOn : E a 1 := field 9 1 (by decide)

def setCount : E a 1 := both fetching (both (.equal kind (.lit 5))
  (both (.zero (field 19 45 (by decide))) (.inv (.zero count))))

def branch : E a 1 := both fetching (both (.equal kind (.lit 6))
  (both (.zero (field 10 54 (by decide)))
    (both (.reg .captureValid)
      (both (.ult (.reg (.base .pc)) target) (.ult target (.reg (.base .count)))))))

/-- Early completion discards accepted TX remaining in storage and the
    shifter. The host still sees the accepted and consumed bit counters and
    must drain RX using the same owner. -/
def discard : E a 1 := both fetching (.equal (.reg .fetched) (.lit 7))

def denyTX : E a 1 := either (.reg .txClosed) discard

def runtimeInput : {w : Nat} → Core.Input w → E a w
  | _, .txPush => both (.inv denyTX) (.input .txPush)
  | _, input => .input input

def decodedRegister : {w : Nat} → Core.Register a w → E a w
  | _, .word _ => .reg .fetched
  | _, reg => .reg (.base reg)

def usesEntryWord : Core.Register a w → Bool
  | .pc | .phase | .currentWord | .countdown | .levels | .enabled => true
  | _ => false

def originalNext (reg : Core.Register a w) : E a w :=
  (Core.next reg).bind runtimeInput (fun r =>
    if usesEntryWord reg then decodedRegister r else .reg (.base r))

def control : E a 1 := either setCount branch

def nextBase : {w : Nat} → Core.Register a w → E a w
  | _, .phase => .mux discard (.lit 5) (.mux control (.lit 1) (originalNext .phase))
  | _, .pc => .mux branch
      (.mux (.equal (.reg .lastCapture) branchOn) target (lift (Core.inc (.reg .pc))))
      (.mux setCount (lift (Core.inc (.reg .pc))) (originalNext .pc))
  | _, .remaining => .mux setCount count (originalNext .remaining)
  | _, .levels => .mux control (.reg (.base .levels)) (originalNext .levels)
  | _, .enabled => .mux control (.reg (.base .enabled)) (originalNext .enabled)
  | _, .txHead => .mux discard (.lit 0) (originalNext .txHead)
  | _, .txTail => .mux discard (.lit 0) (originalNext .txTail)
  | _, .txCount => .mux discard (.lit 0) (originalNext .txCount)
  | _, .txShift => .mux discard (.lit 0) (originalNext .txShift)
  | _, .txValid => .mux discard (.lit 0) (originalNext .txValid)
  | _, reg => originalNext reg

def next : {w : Nat} → Register a w → E a w
  | _, .base reg => nextBase reg
  | _, .lastCapture => .mux (lift Core.clearedRuntime) (.lit 0)
      (.mux (lift Core.capturingRX) (lift Core.inputBit) (.reg .lastCapture))
  | _, .captureValid => .mux (either (lift Core.clearedRuntime) control) (.lit 0)
      (.mux (lift Core.capturingRX) (.lit 1) (.reg .captureValid))
  | _, .txClosed => .mux (lift Core.clearedRuntime) (.lit 0) (either discard (.reg .txClosed))
  | _, .fetched => .lit 0

def output : {w : Nat} → Core.Output w → E a w
  | _, .rejected => either (lift (Core.output .rejected))
      (both (lift (.inv Core.resetting)) (both (.input .txPush) denyTX))
  | _, port => lift (Core.output port)

def bindWord (selected : E a 64) (expr : E a w) : E a w :=
  expr.bind .input fun
    | .fetched => selected
    | reg => .reg reg

def withFetch (s : Values (Register a)) (selected : BitVec 64) : Values (Register a)
  | _, .fetched => selected
  | _, reg => s reg

theorem bindWord_eval (selected : E a 64) (expr : E a w) (i : Values Core.Input)
    (s : Values (Register a)) :
    (bindWord selected expr).eval i s = expr.eval i (withFetch s (selected.eval i s)) := by
  rw [bindWord, Expr.eval_bind]
  congr 1
  funext w reg
  cases reg <;> rfl
  done

def word (registered : Bool) : E a 64 :=
  if registered then .reg .fetched else lift Core.entryWord

def address (registered : Bool) : E a 6 :=
  .slice 0 6 (by decide) (bindWord (word registered) (nextBase .pc))

def load (address : E a 6) : E a 64 :=
  .mux (lift Core.cold) (.lit 0)
    (.mux (both (lift Core.writing) (.equal (.input .address) address)) (.input .word)
      (Execution.readTree 6 (fun k => .reg (.base (.word k))) address))

def circuit (a : Nat) (registered : Bool) : Circuit Core.Input (Register a) Core.Output where
  next := fun reg => match reg with
    | .fetched => if registered then load (address registered) else .lit 0
    | reg => bindWord (word registered) (next reg)
  output := fun port => bindWord (word registered) (output port)

end Pinwheel.Hardware.StreamingReady.SegmentCore
