import Pinwheel.Hardware.AddressWindow
import Pinwheel.Hardware.Processor.AddressMap

/-! Structural address routing for the frozen processor environment. The layout
is checked at elaboration. Kind and size select a circuit specialization; runtime
selectors can mux these expressions without changing their semantics. All range
checks include the entire footprint and use 33-bit endpoints before narrowing. -/
namespace Pinwheel.Hardware.Processor.AddressDecode

open AddressMap Memory.ByteAccess

def window (layout : Layout romWidth ramWidth) (region : Region) : AddressWindow.Window 32 :=
  ⟨layout.config.base region, layout.config.limit region,
    Nat.le_add_right _ _, (layout.valid.1 region).2.2⟩

def footprint (kind : Kind) (size : Size) : AddressWindow.Footprint 32 :=
  ⟨(Access.mk kind size 0).bytes, Access.bytes_pos _, by
    cases kind <;> cases size <;> decide +kernel⟩

def contains (layout : Layout romWidth ramWidth) (region : Region)
    (kind : Kind) (size : Size) (address : Expr I R 32) : Expr I R 1 :=
  AddressWindow.covers (window layout region) (footprint kind size) address

@[simp] theorem contains_eval (layout : Layout romWidth ramWidth) (region : Region)
    (kind : Kind) (size : Size) (address : Expr I R 32) (i : Values I) (s : Values R) :
    (contains layout region kind size address).eval i s =
      BitVec.ofBool (decide (Contains layout region ⟨kind, size, address.eval i s⟩)) := by
  simpa only [contains, AddressWindow.Contains, window, footprint, Contains, Access.bytes]
    using AddressWindow.covers_eval (window layout region) (footprint kind size) address i s

def aligned (kind : Kind) (size : Size) (address : Expr I R 32) : Expr I R 1 :=
  if kind = .fetch then .zero (.slice 0 2 (by decide) address) else
    match size with
    | .byte => .lit 1
    | .half => .zero (.slice 0 1 (by decide) address)
    | .word => .zero (.slice 0 2 (by decide) address)

@[simp] theorem aligned_eval (kind : Kind) (size : Size) (address : Expr I R 32)
    (i : Values I) (s : Values R) :
    (aligned kind size address).eval i s =
      BitVec.ofBool (decide (Access.Aligned ⟨kind, size, address.eval i s⟩)) := by
  cases kind <;> cases size <;>
    simp [aligned, Expr.eval, Access.Aligned, Access.bytes, Size.bytes,
      ← BitVec.toNat_inj, BitVec.extractLsb'_toNat]
  all_goals exact (congrArg Bool.toNat (decide_eq_true (Nat.mod_one _))).symm

def regionCode : Region → BitVec 3
  | .rom => 0 | .ram => 1 | .gpio => 2 | .timer => 3 | .uart => 4

def routeCode {l : Layout rw aw} {access : Access} : Except AddressMap.Fault (Hit l access) → BitVec 3
  | .ok hit => regionCode hit.region
  | .error .misaligned => 5
  | .error .access => 6

def selected (region : Region) (kind : Kind) (size : Size) : BitVec 3 :=
  if Permitted region ⟨kind, size, 0⟩ then regionCode region else 6

/-- Codes0..4 select ROM/RAM/GPIO/timer/UART;5 is misalignment and6 access
fault. Code7 is never produced. This checks routing, not MMIO register holes. -/
def result (layout : Layout romWidth ramWidth) (kind : Kind) (size : Size)
    (address : Expr I R 32) : Expr I R 3 :=
  .mux (aligned kind size address)
    (.mux (contains layout .rom kind size address) (.lit (selected .rom kind size))
      (.mux (contains layout .ram kind size address) (.lit (selected .ram kind size))
        (.mux (contains layout .gpio kind size address) (.lit (selected .gpio kind size))
          (.mux (contains layout .timer kind size address) (.lit (selected .timer kind size))
            (.mux (contains layout .uart kind size address) (.lit (selected .uart kind size)) (.lit 6))))))
    (.lit 5)

theorem result_eval (layout : Layout romWidth ramWidth) (kind : Kind) (size : Size)
    (address : Expr I R 32) (i : Values I) (s : Values R) :
    (result layout kind size address).eval i s =
      routeCode (route layout ⟨kind, size, address.eval i s⟩) := by
  simp only [result, Expr.eval, aligned_eval, contains_eval]
  have bit (p : Prop) [Decidable p] : BitVec.ofBool (decide p) = 1 ↔ p :=
    (BitVec.ofBool_eq_iff_eq (b := decide p) (b' := true)).trans decide_eq_true_iff
  simp only [bit]
  cases hr : route layout ⟨kind, size, address.eval i s⟩ with
  | ok hit =>
    have hp : Permitted hit.region ⟨kind, size, 0⟩ := hit.permitted
    simp only [routeCode, hit.aligned, if_pos, hit.contains_iff]
    cases he : hit.region <;> simp_all [selected]
  | error fault =>
    cases fault with
    | misaligned => simp [routeCode, (route_misaligned_iff _ _).mp hr]
    | access =>
      have rejected := (route_access_iff _ _).mp hr
      simp only [routeCode, rejected.1, if_pos]
      have sel (r : Region) (hc : Contains layout r ⟨kind, size, address.eval i s⟩) :
          selected r kind size = 6 := by
        have hp : ¬Permitted r ⟨kind, size, 0⟩ := fun p => rejected.2 ⟨r, hc, p⟩
        exact if_neg hp
      repeat' split
      all_goals first | exact sel _ (by assumption) | rfl

def decodeKind (raw : BitVec 2) : Option Kind :=
  if raw = 0 then some .fetch else if raw = 1 then some .load else if raw = 2 then some .store else none

def decodeSize (raw : BitVec 2) : Option Size :=
  if raw = 0 then some .byte else if raw = 1 then some .half else if raw = 2 then some .word else none

def runtimeSize (layout : Layout rw aw) (kind : Kind) (size : Expr I R 2)
    (address : Expr I R 32) : Expr I R 3 :=
  .mux (.equal size (.lit 0)) (result layout kind .byte address)
    (.mux (.equal size (.lit 1)) (result layout kind .half address)
      (.mux (.equal size (.lit 2)) (result layout kind .word address) (.lit 7)))

/-- Raw kinds0/1/2 mean fetch/load/store; sizes0/1/2 mean byte/half/word.
Either raw control3 is rejected with code7, before any address admission. -/
def runtime (layout : Layout rw aw) (kind size : Expr I R 2) (address : Expr I R 32) : Expr I R 3 :=
  .mux (.equal kind (.lit 0)) (runtimeSize layout .fetch size address)
    (.mux (.equal kind (.lit 1)) (runtimeSize layout .load size address)
      (.mux (.equal kind (.lit 2)) (runtimeSize layout .store size address) (.lit 7)))

def rawRouteCode (layout : Layout rw aw) (kind size : BitVec 2) (address : BitVec 32) : BitVec 3 :=
  match decodeKind kind, decodeSize size with
  | some k, some z => routeCode (route layout ⟨k, z, address⟩)
  | _, _ => 7

theorem runtime_eval (layout : Layout rw aw) (kind size : Expr I R 2) (address : Expr I R 32)
    (i : Values I) (s : Values R) :
    (runtime layout kind size address).eval i s = rawRouteCode layout (kind.eval i s) (size.eval i s) (address.eval i s) := by
  rcases Memory.ByteAccess.raw_cases (kind.eval i s) with hk | hk | hk | hk
  all_goals rcases Memory.ByteAccess.raw_cases (size.eval i s) with hs | hs | hs | hs
  all_goals simp [runtime, runtimeSize, Expr.eval, hk, hs, result_eval, rawRouteCode, decodeKind, decodeSize]

theorem runtime_bind_eval (input : {b : Nat} → I b → Expr J S b)
    (register : {b : Nat} → R b → Expr J S b) (layout : Layout rw aw)
    (kind size : Expr I R 2) (address : Expr I R 32) (i : Values J) (s : Values S) :
    ((runtime layout kind size address).bind input register).eval i s =
      (runtime layout (kind.bind input register) (size.bind input register) (address.bind input register)).eval i s := by
  simp only [Expr.eval_bind, runtime_eval]

end Pinwheel.Hardware.Processor.AddressDecode
