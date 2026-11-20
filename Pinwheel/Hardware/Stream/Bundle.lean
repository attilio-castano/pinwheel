import Pinwheel.Hardware.Stream.CompositionProof

namespace Pinwheel.Hardware.Stream

set_option backward.isDefEq.respectTransparency false

/-- A payload layout. Left fields occupy the more significant bits. Names are
presentation metadata; typed field identities determine all wiring. -/
inductive Bundle where
  | bits (name : String) (width : Nat)
  | pair (left right : Bundle)

def Bundle.width : Bundle → Nat
  | .bits _ w => w
  | .pair a b => a.width + b.width

def Bundle.Value : Bundle → Type
  | .bits _ w => BitVec w
  | .pair a b => a.Value × b.Value

def Bundle.Port : Bundle → Nat → Type
  | .bits _ w => DataInput w
  | .pair a b => Joint a.Port b.Port

def Bundle.pack : (b : Bundle) → b.Value → BitVec b.width
  | .bits _ _, v => v
  | .pair a b, v => a.pack v.1 ++ b.pack v.2

def Bundle.unpack : (b : Bundle) → BitVec b.width → b.Value
  | .bits _ _, v => v
  | .pair a b, v => (a.unpack (v.extractLsb' b.width a.width), b.unpack (v.extractLsb' 0 b.width))

theorem Bundle.unpack_pack (b : Bundle) (v : b.Value) : b.unpack (b.pack v) = v := by
  induction b with
  | bits => rfl
  | pair a b ha hb =>
    simp only [pack, unpack, BitVec.extractLsb'_append_eq_left,
      BitVec.extractLsb'_append_eq_right, ha, hb]
    rfl

theorem Bundle.pack_unpack (b : Bundle) (v : BitVec b.width) : b.pack (b.unpack v) = v := by
  induction b with
  | bits => rfl
  | pair a b ha hb => simp only [pack, unpack, ha, hb, BitVec.extractLsb'_append_extractLsb']

def Bundle.values : (b : Bundle) → b.Value → Values b.Port
  | .bits _ _, v => dataValues v
  | .pair a b, v => Joint.values (a.values v.1) (b.values v.2)

def Bundle.fromValues : (b : Bundle) → Values b.Port → b.Value
  | .bits _ _, v => v .data
  | .pair a b, v => (a.fromValues (fun p => v (.left p)), b.fromValues (fun p => v (.right p)))

theorem Bundle.fromValues_values (b : Bundle) (v : b.Value) : b.fromValues (b.values v) = v := by
  induction b with
  | bits => rfl
  | pair a b ha hb => exact Prod.ext (ha v.1) (hb v.2)

theorem Bundle.values_fromValues (b : Bundle) (v : Values b.Port) (p : b.Port w) :
    b.values (b.fromValues v) p = v p := by
  induction b with
  | bits => cases p; rfl
  | pair a b ha hb => cases p with
    | left p => exact ha _ p
    | right p => exact hb _ p

def Bundle.shape : (b : Bundle) → Interface b.Port
  | .bits name _ => {
      size := 1
      signal := fun _ => ⟨_, .data⟩
      position := fun _ => 0
      signal_position := fun p => by cases p; rfl
      label := fun _ => name
      unique := fun _ _ _ => Subsingleton.elim _ _ }
  | .pair a b => Joint.interface a.shape b.shape

def Bundle.label : (b : Bundle) → b.Port w → String
  | .bits name _, _ => name
  | .pair a _, .left p => a.label p
  | .pair _ b, .right p => b.label p

/-- Names must be unique; concrete layouts discharge this finite obligation
with `decide +kernel`. Enumeration, widths and bindings are derived. -/
def Bundle.interface (b : Bundle)
    (unique : ∀ a c, b.label (b.shape.signal a).2 = b.label (b.shape.signal c).2 → a = c) :
    Interface b.Port := b.shape.rename b.label unique

def Bundle.unpackExpr (b : Bundle) (e : Expr I R b.width) : {w : Nat} → b.Port w → Expr I R w :=
  match b with
  | .bits _ _ => fun p => match p with | .data => e
  | .pair a b => fun p => match p with
    | .left p => a.unpackExpr (.slice b.width a.width (by simp [width]; omega) e) p
    | .right p => b.unpackExpr (.slice 0 b.width (by simp [width]) e) p

def Bundle.packExpr (b : Bundle) (v : {w : Nat} → b.Port w → Expr I R w) : Expr I R b.width :=
  match b with
  | .bits _ _ => v .data
  | .pair a b => .concat (a.packExpr (fun p => v (.left p))) (b.packExpr (fun p => v (.right p)))

theorem Bundle.packExpr_eval (b : Bundle) (v : {w : Nat} → b.Port w → Expr I R w)
    (i : Values I) (s : Values R) :
    (b.packExpr v).eval i s = b.pack (b.fromValues (fun p => (v p).eval i s)) := by
  induction b with
  | bits => rfl
  | pair a b ha hb => simp only [packExpr, Expr.eval, pack, fromValues, ha, hb]

theorem Bundle.unpackExpr_eval (b : Bundle) (e : Expr I R b.width) (i : Values I) (s : Values R)
    (p : b.Port w) : (b.unpackExpr e p).eval i s = b.values (b.unpack (e.eval i s)) p := by
  induction b with
  | bits => cases p; rfl
  | pair a b ha hb => cases p with
    | left p => exact ha _ p
    | right p => exact hb _ p

end Pinwheel.Hardware.Stream
