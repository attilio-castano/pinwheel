import Pinwheel.Hardware.Loader.Proofs

namespace Pinwheel.Hardware.Loader.Store

inductive Register : Nat → Type where
  | word (k : BitVec 6) : Register 64
  | index (k : BitVec 8) : Register 6
  | idle : Register 6
  | last : Register 8

def offset : Register w → BitVec 9
  | .word k => BitVec.ofNat 9 k.toNat
  | .index k => BitVec.ofNat 9 (64 + k.toNat)
  | .idle => 320
  | .last => 321

theorem width_bound : (r : Register w) → w ≤ 64
  | .word _ | .index _ | .idle | .last => by decide

inductive Input : Nat → Type where
  | write : Input 1 | cursor : Input 9 | data : Input 64 | address : Input 8

structure Inputs where
  write : Bool
  cursor : BitVec 9
  data : BitVec 64
  address : BitVec 8 := 0

def Inputs.values (i : Inputs) : Values Input
  | _, .write => BitVec.ofBool i.write | _, .cursor => i.cursor
  | _, .data => i.data | _, .address => i.address

abbrev Image := Values Register

def tick (i : Inputs) (m : Image) : Image := fun {w} r =>
  if i.write && i.cursor == offset r then i.data.extractLsb' 0 w else m r

def read (m : Image) (address : BitVec 8) : BitVec 64 := m (.word (m (.index address)))

def next (r : Register w) : Expr Input Register w :=
  .mux (.band (.input .write) (.equal (.input .cursor) (.lit (offset r))))
    (.slice 0 w (by simpa using width_bound r) (.input .data)) (.reg r)

def readExpr (address : Expr I Register 8) : Expr I Register 64 :=
  Execution.readTree 6 (fun k => .reg (.word k))
    (Execution.readTree 8 (fun k => .reg (.index k)) address)

set_option backward.isDefEq.respectTransparency false in
theorem next_correct (i : Inputs) (m : Image) (r : Register w) :
    (next r).eval i.values m = tick i m r := by
  simp [next, Expr.eval, Inputs.values, tick, Bool.beq_eq_decide_eq]
  done

theorem read_correct (i : Values I) (m : Image) (address : Expr I Register 8) :
    (readExpr address).eval i m = read m (address.eval i m) := by
  simp [readExpr, Execution.readTree_correct, Expr.eval, read]
  done

end Pinwheel.Hardware.Loader.Store
