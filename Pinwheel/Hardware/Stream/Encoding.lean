import Pinwheel.Hardware.Stream.Ports
import Pinwheel.Hardware.Stream.Pipeline

namespace Pinwheel.Hardware.Stream

def inputValues (i : Input (BitVec w)) : Values (In w)
  | _, .at ⟨0, _⟩ => BitVec.ofBool i.reset
  | _, .at ⟨1, _⟩ => BitVec.ofBool i.offered.isSome
  | _, .at ⟨2, _⟩ => BitVec.ofBool i.ready
  | _, .at ⟨3, _⟩ => i.offered.getD 0
  | _, .at ⟨k + 4, h⟩ => False.elim (by change k + 4 < 4 at h; omega)

def decodeInput (i : Values (In w)) : Input (BitVec w) :=
  ⟨i reset == 1, if i valid = 1 then some (i payload) else none, i ready == 1⟩

def outputValues (o : Output (BitVec w)) : Values (Out w)
  | _, .at ⟨0, _⟩ => BitVec.ofBool o.ready
  | _, .at ⟨1, _⟩ => BitVec.ofBool o.offered.isSome
  | _, .at ⟨2, _⟩ => o.offered.getD 0
  | _, .at ⟨k + 3, h⟩ => False.elim (by change k + 3 < 3 at h; omega)

theorem decode_encode (i : Input (BitVec w)) : decodeInput (inputValues i) = i := by
  cases i with
  | mk r o d => cases r <;> cases o <;> cases d <;> rfl

def _root_.Pinwheel.Hardware.Expr.bor (x y : Expr I R 1) : Expr I R 1 := .inv (.band (.inv x) (.inv y))

def _root_.Pinwheel.Hardware.Expr.plus (x y : Expr I R w) : Expr I R w := .sub x (.sub (.lit 0) y)

@[simp] theorem eval_bor (x y : Expr I R 1) (i : Values I) (s : Values R) :
    (x.bor y).eval i s = x.eval i s ||| y.eval i s := by
  simp [Expr.bor, Expr.eval, BitVec.not_and]

@[simp] theorem eval_plus (x y : Expr I R w) (i : Values I) (s : Values R) :
    (x.plus y).eval i s = x.eval i s + y.eval i s := by
  simp [Expr.plus, Expr.eval]

end Pinwheel.Hardware.Stream
