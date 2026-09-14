import Pinwheel.Hardware.Loader.Emit

namespace Pinwheel.Hardware.Storage.Dense
open Execution

/-- Qualify owns a budget; the other operations own capture/finish fields. -/
def compress (word : BitVec 64) : BitVec 55 :=
  (if word.extractLsb' 0 3 = 3 then (0#26) ++ word.extractLsb' 17 12
   else word.extractLsb' 25 38) ++ word.extractLsb' 0 17

def expand (word : BitVec 55) : BitVec 64 :=
  if word.extractLsb' 0 3 = 3 then (0#35) ++ word.extractLsb' 17 12 ++ word.extractLsb' 0 17
  else (0#1) ++ word.extractLsb' 17 38 ++ (0#8) ++ word.extractLsb' 0 17

private theorem ordinary_parts (hi : BitVec 38) (lo : BitVec 17) :
    (((0#1) ++ hi ++ (0#8) ++ lo).extractLsb' 0 3 = lo.extractLsb' 0 3) ∧
    (((0#1) ++ hi ++ (0#8) ++ lo).extractLsb' 25 38 = hi) ∧
    (((0#1) ++ hi ++ (0#8) ++ lo).extractLsb' 0 17 = lo) := by
  bv_normalize
  done

private theorem dense_parts (hi : BitVec 38) (lo : BitVec 17) :
    ((hi ++ lo).extractLsb' 0 3 = lo.extractLsb' 0 3) ∧
    ((hi ++ lo).extractLsb' 17 38 = hi) ∧ ((hi ++ lo).extractLsb' 0 17 = lo) ∧
    ((hi ++ lo).extractLsb' 17 12 = hi.extractLsb' 0 12) := by
  bv_normalize
  done

private theorem qualify_parts (hi : BitVec 12) (lo : BitVec 17) :
    (((0#35) ++ hi ++ lo).extractLsb' 0 3 = lo.extractLsb' 0 3) ∧
    (((0#35) ++ hi ++ lo).extractLsb' 17 12 = hi) ∧
    (((0#35) ++ hi ++ lo).extractLsb' 0 17 = lo) ∧
    (((0#26) ++ hi).extractLsb' 0 12 = hi) := by
  bv_normalize
  done

private theorem ordinary (hi : BitVec 38) (lo : BitVec 17) (h : lo.extractLsb' 0 3 ≠ 3) :
    expand (compress ((0#1) ++ hi ++ (0#8) ++ lo)) = (0#1) ++ hi ++ (0#8) ++ lo := by
  simp only [compress, ordinary_parts, h, if_false, expand, dense_parts hi lo]
  done

private theorem qualifying (hi : BitVec 12) (lo : BitVec 17) (h : lo.extractLsb' 0 3 = 3) :
    expand (compress ((0#35) ++ hi ++ lo)) = (0#35) ++ hi ++ lo := by
  simp only [compress, qualify_parts, h, if_true, expand, dense_parts ((0#26) ++ hi) lo, (qualify_parts hi lo).2.2.2]
  done

def upper (f : Fields) : BitVec 38 := f.no ++ f.yes ++ f.sample ++ f.finish ++ f.terminal ++ f.entry ++ f.check
def lower (f : Fields) : BitVec 17 := f.duration ++ f.enabled ++ f.levels ++ f.kind

private theorem pack_group (f : Fields) : pack f = (0#1) ++ upper f ++ f.budget ++ lower f := by
  cases f
  simp only [pack, packRaw, upper, lower, BitVec.append_assoc, BitVec.cast_eq]
  rfl
  done

private theorem lower_kind (f : Fields) : (lower f).extractLsb' 0 3 = f.kind := by
  cases f
  simp only [lower]
  bv_normalize
  done

private theorem ordinary_fields (f : Fields) (hb : f.budget = 0) (hk : f.kind ≠ 3) :
    expand (compress (pack f)) = pack f := by
  rw [pack_group, hb]
  exact ordinary (upper f) (lower f) (by simpa only [lower_kind] using hk)
  done

private theorem qualify_raw_group (c : BitVec 4) (b d : BitVec 8) (en le : BitVec 3) :
    (0#35) ++ c ++ b ++ d ++ en ++ le ++ (3#3) =
      (0#35) ++ (c ++ b) ++ (d ++ en ++ le ++ (3#3)) := by
  simp only [BitVec.append_assoc, BitVec.cast_eq]
  done

set_option backward.isDefEq.respectTransparency false in
private theorem qualify_group (q : Engine.Reactive.Qualify) :
    pack (fields (.qualify q)) = (0#35) ++ (checkBits q.condition ++ (BitVec.ofFin q.budgetMinusOne : BitVec 8)) ++
      lower (fields (.qualify q)) := by
  simp [pack, packRaw, fields]
  exact qualify_raw_group _ _ _ _ _
  done

set_option maxHeartbeats 2000000 in
theorem encode_roundtrip (i : Operation) : expand (compress (encode i)) = encode i := by
  cases i with
  | action a => exact ordinary_fields _ rfl (by simp [fields, actionFields])
  | wait w => exact ordinary_fields _ rfl (by simp [fields])
  | halt => exact ordinary_fields _ rfl (by simp [fields])
  | checked a =>
    apply ordinary_fields
    · cases h : a.finish <;> simp [fields, finishFields, actionFields, h]
    · cases h : a.finish <;> simp [fields, finishFields, actionFields, h]
  | qualify q =>
    change expand (compress (pack (fields (.qualify q)))) = pack (fields (.qualify q))
    rw [qualify_group]
    exact qualifying _ _ (by simp only [lower_kind, fields])
  done

theorem accepted_roundtrip (word : BitVec 64) (h : validValue word = true) :
    expand (compress word) = word := by
  rw [valid_decode] at h
  cases hd : decode word with
  | none => simp [hd] at h
  | some i => rw [← accepted_canonical word i hd]; exact encode_roundtrip i
  done

def compressExpr (word : Expr I R 64) : Expr I R 55 :=
  .concat (.mux (.equal (.slice 0 3 (by decide) word) (.lit 3))
    (.concat (.lit (0#26)) (.slice 17 12 (by decide) word : Expr I R 12))
    (.slice 25 38 (by decide) word)) (.slice 0 17 (by decide) word : Expr I R 17)

def expandExpr (word : Expr I R 55) : Expr I R 64 :=
  .mux (.equal (.slice 0 3 (by decide) word) (.lit 3))
    (.concat (.concat (.lit (0#35)) (.slice 17 12 (by decide) word : Expr I R 12))
      (.slice 0 17 (by decide) word : Expr I R 17))
    (.concat (.concat (.concat (.lit (0#1)) (.slice 17 38 (by decide) word : Expr I R 38))
      (.lit (0#8))) (.slice 0 17 (by decide) word : Expr I R 17))

set_option backward.isDefEq.respectTransparency false in
theorem compress_correct (word : Expr I R 64) (i : Values I) (s : Values R) :
    (compressExpr word).eval i s = compress (word.eval i s) := by
  simp [compressExpr, Expr.eval, compress]
  done

set_option backward.isDefEq.respectTransparency false in
theorem expand_correct (word : Expr I R 55) (i : Values I) (s : Values R) :
    (expandExpr word).eval i s = expand (word.eval i s) := by
  simp [expandExpr, Expr.eval, expand]
  done

end Pinwheel.Hardware.Storage.Dense
