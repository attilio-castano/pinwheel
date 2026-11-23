import Lean
import Pinwheel.Hardware.Processor.RV32I.ALU

open Lean Elab Command
open Pinwheel.Hardware
open Pinwheel.Hardware.Processor.RV32I (RegisterOp ImmediateOp ShiftOp)

namespace HardwareWordALUTests

inductive Input (w n : Nat) : Nat → Type where
  | selector : Input w n 4
  | left : Input w n w
  | amount : Input w n n

inductive Register (w : Nat) : Nat → Type where
  | right : Register w w

def pins (w n selector left amount : Nat) : Values (Input w n) := fun p => match p with
  | .selector => BitVec.ofNat 4 selector
  | .left => BitVec.ofNat w left
  | .amount => BitVec.ofNat n amount

def state (w right : Nat) : Values (Register w) := fun p => match p with
  | .right => BitVec.ofNat w right

abbrev E (w n b : Nat) := Expr (Input w n) (Register w) b
def selector (w n : Nat) : E w n 4 := .input .selector
def left (w n : Nat) : E w n w := .input .left
def right (w n : Nat) : E w n w := .reg .right
def amount (w n : Nat) : E w n n := .input .amount

/-- Independent Nat/Int oracle, with explicit control numbers and integer bit
extraction. It calls neither the ALU model/decoder nor the WordOps functions. -/
def signed (w x : Nat) : Int := if 0 < w ∧ 2^(w-1) ≤ x then (x : Int)-(2^w : Nat) else x
def wrap (w : Nat) (x : Int) : Nat := (x % (2^w : Nat)).toNat
def bitwise (w x y : Nat) (f : Bool → Bool → Bool) : Nat :=
  (List.range w).foldl (fun result k =>
    if f (x / 2^k % 2 == 1) (y / 2^k % 2 == 1) then result+2^k else result) 0

def reference (w control x y k : Nat) : Nat × Nat :=
  let result := match control with
    | 0 => (x+y)%2^w
    | 1 => wrap w ((x : Int)-y)
    | 2 => bitwise w x y (· && ·)
    | 3 => bitwise w x y (· || ·)
    | 4 => bitwise w x y (· != ·)
    | 5 => (if signed w x < signed w y then 1 else 0)%2^w
    | 6 => (if x < y then 1 else 0)%2^w
    | 7 => (x*2^k)%2^w
    | 8 => x/2^k
    | 9 => wrap w (signed w x / (2^k : Nat))
    | _ => 0
  (result, if control < 10 then 1 else 0)

def require (actual expected : Nat × Nat) (label : String) : IO Unit := do
  unless actual = expected do throw (IO.userError s!"{label}: expected {expected}, got {actual}")

def check (w n control rawX rawY rawAmount : Nat) : IO Unit := do
  let i : Values (Input w n) := pins w n control rawX rawAmount
  let r : Values (Register w) := state w rawY
  let actual := ((WordALU.value (selector w n) (left w n) (right w n) (amount w n)).eval i r |>.toNat,
    (WordALU.valid (selector w n)).eval i r |>.toNat)
  require actual (reference w (control%16) (rawX%2^w) (rawY%2^w) (rawAmount%2^n))
    s!"generic w{w}/n{n}/control{control}/x{rawX}/y{rawY}/amount{rawAmount}"

def boundaries (w : Nat) : List Nat := [0, 1, 2, 3, 2^(w-1)-1, 2^(w-1), 2^w-1,
  0x55555555, 0xaaaaaaaa, 0x80000001, 0xdeadbeef, 0xffffffff]

def genericCampaign : IO Nat := do
  let mut checks := 0
  for w in [:5] do
    for n in [:4] do
      for x in [:2^w] do
        for y in [:2^w] do
          for k in [:2^n] do
            for control in [:16] do
              check w n control x y k
              checks := checks+1
  for w in [0, 1, 8, 17, 32, 64] do
    for n in [0, 1, 5, 6, 8] do
      for x in boundaries w do
        for k in [0, 1, w-1, w, w+1, 31, 32, 63, 64, 255] do
          for control in [:16] do
            check w n control x (0xffffffff-x) k
            checks := checks+1
  let mut seed := 0x416c7557
  for cycle in [:512] do
    seed := (1664525*seed+1013904223)%2^32
    let x := seed
    seed := (1664525*seed+1013904223)%2^32
    for control in [:16] do
      check 32 8 control x seed (cycle%256)
      checks := checks+1
  return checks

/-- Independent adapter maps: these do not call production operation maps. -/
def registerCode : RegisterOp → Nat
  | .add => 0 | .sub => 1 | .bitAnd => 2 | .bitOr => 3 | .bitXor => 4
  | .slt => 5 | .sltu => 6 | .sll => 7 | .srl => 8 | .sra => 9
def immediateCode : ImmediateOp → Nat
  | .add => 0 | .bitAnd => 2 | .bitOr => 3 | .bitXor => 4 | .slt => 5 | .sltu => 6
def shiftCode : ShiftOp → Nat | .left => 7 | .rightLogical => 8 | .rightArithmetic => 9

def registerOps : List RegisterOp := [.add, .sub, .bitAnd, .bitOr, .bitXor, .slt, .sltu, .sll, .srl, .sra]
def immediateOps : List ImmediateOp := [.add, .bitAnd, .bitOr, .bitXor, .slt, .sltu]

def rv32Campaign : IO Nat := do
  let mut checks := 0
  for rawX in boundaries 32 do
    for rawY in boundaries 32 ++ [31, 32, 33, 63, 64, 255] do
      let x := rawX%2^32
      let y := rawY%2^32
      let r : Values (Register 32) := state 32 y
      for control in [:16] do
        let i : Values (Input 32 5) := pins 32 5 control x 0
        let actual := ((Processor.RV32I.ALU.value (selector 32 5) (left 32 5) (right 32 5)).eval i r |>.toNat,
          (Processor.RV32I.ALU.valid (selector 32 5)).eval i r |>.toNat)
        require actual (reference 32 control x y (y%32)) "RV32 runtime low-five adapter"
        checks := checks+1
      for op in registerOps do
        let i : Values (Input 32 5) := pins 32 5 0 x 0
        let actual := (Processor.RV32I.ALU.register op (left 32 5) (right 32 5)).eval i r |>.toNat
        require (actual, 1) (reference 32 (registerCode op) x y (y%32)) "RV32 register adapter"
        checks := checks+1
  for raw in [:4096] do
    let x := (boundaries 32)[raw % (boundaries 32).length]!
    let extended := wrap 32 (if raw < 2048 then (raw : Int) else (raw : Int)-4096)
    let i : Values (Input 32 12) := pins 32 12 0 x raw
    let r : Values (Register 32) := state 32 0
    for op in immediateOps do
      let actual := (Processor.RV32I.ALU.immediate op (left 32 12) (amount 32 12)).eval i r |>.toNat
      require (actual, 1) (reference 32 (immediateCode op) x extended 0) "RV32 signed immediate adapter"
      checks := checks+1
  for x in boundaries 32 do
    for k in [:32] do
      for op in [ShiftOp.left, .rightLogical, .rightArithmetic] do
        let i : Values (Input 32 5) := pins 32 5 0 x k
        let r : Values (Register 32) := state 32 0
        let actual := (Processor.RV32I.ALU.shiftImmediate op (left 32 5) (amount 32 5)).eval i r |>.toNat
        require (actual, 1) (reference 32 (shiftCode op) x 0 k) "RV32 shift immediate adapter"
        checks := checks+1
  return checks

def reject (name : String) (actual expected : Nat × Nat) : IO Unit := do
  unless actual ≠ expected do throw (IO.userError s!"Expression mutation escaped: {name}")

def mutateValue (code : Nat) (replacement : E w n w) : E w n w :=
  .mux (.equal (selector w n) (.lit (BitVec.ofNat 4 code))) replacement
    (WordALU.value (selector w n) (left w n) (right w n) (amount w n))

def mutationControls : IO Nat := do
  let c := selector 8 6
  let l := left 8 6
  let r := right 8 6
  let a := amount 8 6
  let evaluate (v : E 8 6 8) (ok : E 8 6 1) (code x y k : Nat) : Nat × Nat :=
    ((v.eval (pins 8 6 code x k) (state 8 y)).toNat, (ok.eval (pins 8 6 code x k) (state 8 y)).toNat)
  let good := WordALU.value c l r a
  let ok := WordALU.valid c
  reject "add decoded as subtract" (evaluate (mutateValue 0 (.sub l r)) ok 0 5 3 0) (reference 8 0 5 3 0)
  reject "XOR decoded as OR" (evaluate (mutateValue 4 (WordOps.wordOr l r)) ok 4 1 1 0) (reference 8 4 1 1 0)
  reject "signed compare becomes unsigned"
    (evaluate (mutateValue 5 (.mux (.ult l r) (.lit 1) (.lit 0))) ok 5 128 0 0) (reference 8 5 128 0 0)
  reject "Boolean result sign-extended"
    (evaluate (mutateValue 5 (.mux (WordOps.signedLess l r) (.lit 255) (.lit 0))) ok 5 128 0 0) (reference 8 5 128 0 0)
  reject "arithmetic right loses sign"
    (evaluate (mutateValue 9 (WordOps.shiftRightBy l a)) ok 9 128 0 1) (reference 8 9 128 0 1)
  reject "generic shift silently masks high amount bit"
    (evaluate (mutateValue 7 (WordOps.shiftLeftBy l (.slice 0 5 (by decide) a))) ok 7 1 0 32) (reference 8 7 1 0 32)
  reject "reserved result leaks operand"
    (evaluate (mutateValue 15 l) ok 15 85 0 0) (reference 8 15 85 0 0)
  reject "reserved code accepted" (evaluate good (.lit 1) 10 0 0 0) (reference 8 10 0 0 0)
  reject "zero arithmetic result treated as invalid"
    (evaluate good (.inv (.zero good)) 0 0 0 0) (reference 8 0 0 0 0)
  let truncated : E 8 6 4 := .concat (.lit (0#1)) (.slice 0 3 (by decide) c)
  reject "high selector bit dropped"
    (evaluate (WordALU.value truncated l r a) (WordALU.valid truncated) 10 7 7 0) (reference 8 10 7 7 0)
  let wideAmount : E 32 5 32 := WordALU.value (selector 32 5) (left 32 5) (right 32 5)
    (.slice 0 6 (by decide) (right 32 5))
  reject "RV32 adapter fails low-five masking"
    ((wideAmount.eval (pins 32 5 7 1 0) (state 32 32)).toNat, 1) (reference 32 7 1 32 0)
  let unsignedImm : E 32 12 32 := WordALU.value (.lit 6) (left 32 12)
    (.concat (.lit (0#20)) (amount 32 12)) (.lit (0#5))
  reject "SLTIU immediate zero extended"
    ((unsignedImm.eval (pins 32 12 0 4096 4095) (state 32 0)).toNat, 1) (reference 32 6 4096 (2^32-1) 0)
  return 12

/-- The same arbitrary pin/register rewiring is valid at the adapter boundary. -/
theorem immediate_bind (input : {b : Nat} → I b → Expr J S b)
    (register : {b : Nat} → R b → Expr J S b) (op : ImmediateOp)
    (x : Expr I R 32) (bits : Expr I R 12) (i : Values J) (s : Values S) :
    ((Processor.RV32I.ALU.immediate op x bits).bind input register).eval i s =
      Processor.RV32I.Semantics.immediateALU op ((x.bind input register).eval i s)
        ((bits.bind input register).eval i s) := by
  simp only [Expr.eval_bind, Processor.RV32I.ALU.immediate_eval]

example :
    (WordALU.value (selector 8 6) (left 8 6) (right 8 6) (amount 8 6)).eval
      (pins 8 6 15 255 63) (state 8 255) = 0 ∧
    (WordALU.valid (selector 8 6)).eval (pins 8 6 15 255 63) (state 8 255) = 0 := by
  apply WordALU.reserved_eval
  decide +kernel

end HardwareWordALUTests

elab "#audit_word_alu" : command => do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    if name.toString.startsWith "Pinwheel.Hardware.WordALU." ||
        name.toString.startsWith "_private.Pinwheel.Hardware.WordALU." ||
        name.toString.startsWith "Pinwheel.Hardware.Processor.RV32I.ALU." ||
        name.toString.startsWith "_private.Pinwheel.Hardware.Processor.RV32I.ALU." ||
        name.toString.startsWith "HardwareWordALUTests." then
      count := count+1
      let axioms ← collectAxioms name
      let bad := axioms.filter fun a => a != ``propext && a != ``Classical.choice && a != ``Quot.sound
      unless bad.isEmpty do throwError "Unapproved word ALU axioms in {name}: {bad}"
  if count < 50 then throwError "Incomplete word ALU audit"
  logInfo m!"Word ALU audit: {count} declarations, standard axioms only."

#audit_word_alu

def main : IO Unit := do
  let generic ← HardwareWordALUTests.genericCampaign
  let rv32 ← HardwareWordALUTests.rv32Campaign
  let mutants ← HardwareWordALUTests.mutationControls
  IO.println s!"Word ALU: {generic} independent runtime-selector cases, {rv32} RV32 adapter cases, {mutants} actual-expression mutations rejected."
