import Pinwheel.Hardware.Structure

/-! Register enables as first-class, certified structure. A register's update is
split into *when* it loads and *what* it loads, with a proof that the emitted
next-state expression means exactly that. The expression itself is unchanged,
so emitted artifacts and their proofs are untouched; what is gained is a named
enable cone, a named data cone, and a sound basis for choosing which registers
may stop their clock instead of recirculating. -/
namespace Pinwheel.Hardware

structure Update (I R : Nat → Type) (w : Nat) where
  enable : Expr I R 1
  data : Expr I R w

/-- The recirculating encoding of an update. -/
def Update.next (u : Update I R w) (r : R w) : Expr I R w := .mux u.enable u.data (.reg r)

/-- `next` loads `data` on edges where `enable` holds and otherwise keeps `r`.
This is the contract a clock gate or an enable flip-flop implements. -/
def Update.Describes (u : Update I R w) (r : R w) (next : Expr I R w) : Prop :=
  ∀ (i : Values I) (s : Values R),
    next.eval i s = if u.enable.eval i s = 1 then u.data.eval i s else s r

theorem Update.describes_next (u : Update I R w) (r : R w) : u.Describes r (u.next r) :=
  fun _ _ => rfl

theorem Update.Describes.load {u : Update I R w} {r : R w} {next : Expr I R w}
    (h : u.Describes r next) (i : Values I) (s : Values R) (enabled : u.enable.eval i s = 1) :
    next.eval i s = u.data.eval i s := by
  rw [h i s, if_pos enabled]

theorem Update.Describes.hold {u : Update I R w} {r : R w} {next : Expr I R w}
    (h : u.Describes r next) (i : Values I) (s : Values R) (disabled : u.enable.eval i s ≠ 1) :
    next.eval i s = s r := by
  rw [h i s, if_neg disabled]

/-- A multiplexer whose last branch is the register itself is an update. -/
theorem Update.describes_mux (c : Expr I R 1) (d : Expr I R w) (r : R w) :
    (⟨c, d⟩ : Update I R w).Describes r (.mux c d (.reg r)) := fun _ _ => rfl

/-- The same behind a slice, when the sliced hold branch is still the register:
narrow physical registers that store a field of a wider logical value. -/
theorem Update.describes_slice_mux (c : Expr I R 1) (d hold : Expr I R v) (r : R len)
    (start : Nat) (fits : start + len ≤ v)
    (kept : ∀ (i : Values I) (s : Values R), (hold.eval i s).extractLsb' start len = s r) :
    (⟨c, .slice start len fits d⟩ : Update I R len).Describes r
      (.slice start len fits (.mux c d hold)) := by
  intro i s
  simp only [Expr.eval]
  split <;> simp_all

/-- Read `(enable, data)` off the two shapes above. Soundness for a particular
register is a separate obligation: the last branch must be that register. -/
def Expr.updateShape : Expr I R w → Option (Update I R w)
  | .mux c d _ => some ⟨c, d⟩
  | .slice start len fits (.mux c d _) => some ⟨c, .slice start len fits d⟩
  | _ => none

/-- Certified updates of some of a circuit's registers. -/
structure Circuit.Enables (c : Circuit I R O) where
  update : {w : Nat} → R w → Option (Update I R w)
  sound : ∀ {w : Nat} (r : R w) (u : Update I R w), update r = some u → u.Describes r (c.next r)

/-- A gated register changes only on enabled edges, and then to its data. -/
theorem Circuit.Enables.step {c : Circuit I R O} (e : c.Enables) {w : Nat} (r : R w) (u : Update I R w)
    (h : e.update r = some u) (i : Values I) (s : Values R) :
    c.step i s r = if u.enable.eval i s = 1 then u.data.eval i s else s r :=
  e.sound r u h i s

end Pinwheel.Hardware
