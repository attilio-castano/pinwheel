import Pinwheel.Hardware.Enable
import Pinwheel.Hardware.Storage.CacheEnable

/-! Certified enables of the composed backends. Every storage register and the
cached word already has the shape `mux enable data hold`; this file reads the
enable and data off the proved expressions, certifies them, and states which
registers a flow may clock-gate. No expression changes, so emitted RTL and its
read-back proofs are untouched. -/
namespace Pinwheel.Hardware.Storage.Backend.Enabled
open Loader

abbrev Body := Circuit FinalInput Register Machine.Output

/-- Registers that load under an enable and otherwise hold. -/
def stores : {w : Nat} → Register w → Bool
  | _, .word _ _ => true | _, .index _ _ => true | _, .idle _ => true
  | _, .last _ => true | _, .current => true
  | _, .control _ => false | _, .core _ => false

/-- The shapes the proved bodies have by definitional unfolding. Index registers
hold five bits of a six-bit logical value, so their multiplexer sits under a slice. -/
structure Shaped (body : Body) : Prop where
  word : ∀ b k, ∃ c d, body.next (.word b k) = .mux c d (.reg (.word b k))
  index : ∀ b k, ∃ c d fits, body.next (.index b k) =
    .slice 0 5 fits (.mux c d (.concat (.lit (0#1)) (.reg (.index b k))))
  idle : ∀ b, ∃ c d, body.next (.idle b) = .mux c d (.reg (.idle b))
  last : ∀ b, ∃ c d, body.next (.last b) = .mux c d (.reg (.last b))
  current : ∃ c d, body.next .current = .mux c d (.reg .current)

theorem bankSelect_shaped : Shaped BankSelect.body :=
  ⟨fun _ _ => ⟨_, _, rfl⟩, fun _ _ => ⟨_, _, _, rfl⟩, fun _ => ⟨_, _, rfl⟩,
    fun _ => ⟨_, _, rfl⟩, ⟨_, _, rfl⟩⟩

theorem cacheEnable_shaped : Shaped CacheEnable.body :=
  ⟨fun _ _ => ⟨_, _, rfl⟩, fun _ _ => ⟨_, _, _, rfl⟩, fun _ => ⟨_, _, rfl⟩,
    fun _ => ⟨_, _, rfl⟩, ⟨_, _, rfl⟩⟩

def update (body : Body) {w : Nat} (r : Register w) : Option (Update FinalInput Register w) :=
  if stores r then (body.next r).updateShape else none

theorem index_kept (i : Values FinalInput) (s : Values Register) (b : Bool) (k : BitVec 8) :
    ((Expr.concat (.lit (0#1)) (.reg (.index b k)) : Expr FinalInput Register (1 + 5)).eval i s).extractLsb' 0 5 =
      s (.index b k) := by
  simp only [Expr.eval]
  generalize s (.index b k) = x
  bv_decide

/-- Every view read off a shaped body is sound. -/
def enables (body : Body) (shaped : Shaped body) : body.Enables where
  update := update body
  sound := by
    intro w r u h
    cases r with
    | control r => simp [update, stores] at h
    | core r => simp [update, stores] at h
    | word b k =>
      obtain ⟨c, d, shape⟩ := shaped.word b k
      simp only [update, stores, shape, Expr.updateShape, if_true, Option.some.injEq] at h
      subst h
      rw [shape]
      exact Update.describes_mux c d _
    | index b k =>
      obtain ⟨c, d, fits, shape⟩ := shaped.index b k
      simp only [update, stores, shape, Expr.updateShape, if_true, Option.some.injEq] at h
      subst h
      rw [shape]
      exact Update.describes_slice_mux c d _ _ 0 fits (fun i s => index_kept i s b k)
    | idle b =>
      obtain ⟨c, d, shape⟩ := shaped.idle b
      simp only [update, stores, shape, Expr.updateShape, if_true, Option.some.injEq] at h
      subst h
      rw [shape]
      exact Update.describes_mux c d _
    | last b =>
      obtain ⟨c, d, shape⟩ := shaped.last b
      simp only [update, stores, shape, Expr.updateShape, if_true, Option.some.injEq] at h
      subst h
      rw [shape]
      exact Update.describes_mux c d _
    | current =>
      obtain ⟨c, d, shape⟩ := shaped.current
      simp only [update, stores, shape, Expr.updateShape, if_true, Option.some.injEq] at h
      subst h
      rw [shape]
      exact Update.describes_mux c d _

/-- Every storing register has a certified update. -/
theorem update_isSome (body : Body) (shaped : Shaped body) {w : Nat} (r : Register w)
    (h : stores r = true) : (update body r).isSome = true := by
  cases r with
  | control r => simp [stores] at h
  | core r => simp [stores] at h
  | word b k => obtain ⟨c, d, shape⟩ := shaped.word b k; simp [update, stores, shape, Expr.updateShape]
  | index b k => obtain ⟨c, d, fits, shape⟩ := shaped.index b k; simp [update, stores, shape, Expr.updateShape]
  | idle b => obtain ⟨c, d, shape⟩ := shaped.idle b; simp [update, stores, shape, Expr.updateShape]
  | last b => obtain ⟨c, d, shape⟩ := shaped.last b; simp [update, stores, shape, Expr.updateShape]
  | current => obtain ⟨c, d, shape⟩ := shaped.current; simp [update, stores, shape, Expr.updateShape]

/-- Which registers a flow may clock-gate. The cached word is never gated: its
enable closes the design's critical loop, and a clock gate needs it earlier than
a data input would. -/
inductive Policy where
  | none        -- recirculate everywhere, as emitted
  | dictionary  -- the 64 dictionary words and the two last-address registers
  | storage     -- also the 512 index entries and the idle profiles
  deriving DecidableEq, Repr

def Policy.gates : Policy → {w : Nat} → Register w → Bool
  | .none, _, _ => false
  | .dictionary, _, .word _ _ => true
  | .dictionary, _, .last _ => true
  | .dictionary, _, _ => false
  | .storage, _, .current => false
  | .storage, _, r => stores r

theorem cached_word_never_gated (p : Policy) : p.gates Register.current = false := by
  cases p <;> rfl

/-- A policy gates only registers with a certified update, so gating replaces
`mux enable data hold` by "clock only when enabled", which `Circuit.Enables.step` justifies. -/
theorem gated_has_update (p : Policy) (body : Body) (shaped : Shaped body) {w : Nat}
    (r : Register w) (h : p.gates r = true) : (update body r).isSome = true := by
  apply update_isSome body shaped
  cases p <;> cases r <;> simp_all [Policy.gates, stores]

end Pinwheel.Hardware.Storage.Backend.Enabled
