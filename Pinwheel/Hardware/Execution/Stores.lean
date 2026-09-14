import Pinwheel.Hardware.Execution.Decode
import Pinwheel.Hardware.Execution.Images

namespace Pinwheel.Hardware.Execution

/-! Two register-store alternatives with equal raw write interfaces and two combinational read ports.
Writes are accepted only while !busy. Atomic commit, staging, and initialization belong to a future loader. -/
inductive Input : Nat → Type where
  | write : Input 1 | busy : Input 1 | indexBank : Input 1
  | address : Input 8 | data : Input 64
  | readA : Input 8 | readB : Input 8

structure Inputs where
  write : Bool
  busy : Bool
  indexBank : Bool
  address : BitVec 8
  data : BitVec 64
  readA : BitVec 8
  readB : BitVec 8
  deriving Repr

def Inputs.values (i : Inputs) : Values Input
  | _, .write => BitVec.ofBool i.write | _, .busy => BitVec.ofBool i.busy
  | _, .indexBank => BitVec.ofBool i.indexBank
  | _, .address => i.address | _, .data => i.data | _, .readA => i.readA | _, .readB => i.readB

inductive DirectReg : Nat → Type where
  | word (address : BitVec 8) : DirectReg 64
inductive IndexedReg : Nat → Type where
  | word (address : BitVec 6) : IndexedReg 64
  | index (address : BitVec 8) : IndexedReg 6
inductive Output : Nat → Type where
  | a (port : Port w) : Output w
  | b (port : Port w) : Output w

def directValues (words : Words) : Values DirectReg
  | _, .word address => words[address.toNat]
def indexedValues (image : Indexed) : Values IndexedReg
  | _, .word address => image.dictionary[address.toNat]
  | _, .index address => image.addresses[address.toNat]

def accept (index : Bool) : Expr Input R 1 :=
  .band (.band (.input .write) (.inv (.input .busy)))
    (.equal (.input .indexBank) (.lit (BitVec.ofBool index)))

def writeWord (old : Expr Input R w) (new : Expr Input R w) (index : Bool) (address : BitVec 8) : Expr Input R w :=
  .mux (.band (accept index) (.equal (.input .address) (.lit address))) new old

def directRead (address : Expr Input DirectReg 8) : Expr Input DirectReg 64 :=
  readTree 8 (fun k => .reg (.word k)) address

def indexedRead (address : Expr Input IndexedReg 8) : Expr Input IndexedReg 64 :=
  readTree 6 (fun k => .reg (.word k)) (readTree 8 (fun k => .reg (.index k)) address)

def directCircuit : Circuit Input DirectReg Output where
  next := fun r => match r with
    | .word k => writeWord (.reg (.word k)) (.input .data) false k
  output := fun o => match o with
    | .a p => logic (directRead (.input .readA)) p
    | .b p => logic (directRead (.input .readB)) p

def indexedCircuit : Circuit Input IndexedReg Output where
  next := fun r => match r with
    | .word k => writeWord (.reg (.word k)) (.input .data) false (BitVec.ofNat 8 k.toNat)
    | .index k => writeWord (.reg (.index k)) (.slice 0 6 (by decide) (.input .data)) true k
  output := fun o => match o with
    | .a p => logic (indexedRead (.input .readA)) p
    | .b p => logic (indexedRead (.input .readB)) p

def writeValue (i : Inputs) (old new : BitVec w) (index : Bool) (address : BitVec 8) : BitVec w :=
  if i.write && !i.busy && (i.indexBank == index) && (i.address == address) then new else old

def directTick (i : Inputs) (words : Words) : Words :=
  Vector.ofFn fun k => writeValue i words[k.val] i.data false (BitVec.ofFin k)

def indexedTick (i : Inputs) (image : Indexed) : Indexed :=
  { dictionary := Vector.ofFn fun k => writeValue i image.dictionary[k.val] i.data false (BitVec.ofNat 8 k.val)
    addresses := Vector.ofFn fun k => writeValue i image.addresses[k.val] (i.data.extractLsb' 0 6) true (BitVec.ofFin k) }

end Pinwheel.Hardware.Execution
