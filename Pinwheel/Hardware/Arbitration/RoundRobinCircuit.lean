import Pinwheel.Hardware.Arbitration.RoundRobin
import Pinwheel.Hardware.Stream.Ports
import Pinwheel.Hardware.NetlistTools
import Std.Data.String.ToNat

/-! A combinational round-robin selector with typed one-bit ports.

For N = n + 1 inputs, the external cursor is one-hot and must identify the
first requester to consider. The selected grant is one-hot or all zero. The
state owner advances the cursor only after an accepted service, using the
logical selector's `RoundRobin.next`; this module contains no state.

`output_eq` relates the expression implementation to the logical selector for
canonical inputs. `raw_output_eq` lifts this to arbitrary request wires and
raw cursor wires satisfying `CursorEncoding`. These are two-state expression
semantics; external MLIR/Verilog lowering is validated separately.
-/

namespace Pinwheel.Hardware.Arbitration.RoundRobinCircuit

set_option backward.isDefEq.respectTransparency false

/-- A synthesizable priority mux. The first asserted condition wins. -/
def priority (request : α → Expr I R 1) (value : α → Expr I R w)
    (fallback : Expr I R w) : List α → Expr I R w
  | [] => fallback
  | x :: rest => .mux (request x) (value x) (priority request value fallback rest)

theorem priority_eval (request : α → Expr I R 1) (value : α → Expr I R w)
    (fallback : Expr I R w) (xs : List α) (i : Values I) (s : Values R) (bits : α → Bool)
    (h : ∀ x, (request x).eval i s = BitVec.ofBool (bits x)) :
    (priority request value fallback xs).eval i s =
      match xs.find? bits with
      | none => fallback.eval i s
      | some x => (value x).eval i s := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases hx : bits x <;> simp [priority, Expr.eval, h, hx, ih]

abbrev bitPorts (count : Nat) (labelPrefix : String) : Stream.Ports where
  size := count
  widths := fun _ => 1
  names := fun k => labelPrefix ++ Nat.repr k.val
  distinct := by
    intro a b h
    simp only [String.append_right_inj] at h
    exact Fin.ext (Nat.repr_injective h)

/-- Inputs 0..N-1 are requests; inputs N..2N-1 are the one-hot cursor. -/
abbrev Inputs (n : Nat) := (bitPorts ((n + 1) + (n + 1)) "input_").Signal
/-- Outputs 0..N-1 are grants; output N is anyGrant. All widths are one. -/
abbrev Outputs (n : Nat) := (bitPorts (n + 2) "output_").Signal

def inputInterface (n : Nat) : Interface (Inputs n) :=
  (bitPorts ((n + 1) + (n + 1)) "input_").interface
def outputInterface (n : Nat) : Interface (Outputs n) :=
  (bitPorts (n + 2) "output_").interface

def requestPort (k : Fin (n + 1)) : Inputs n 1 := .at ⟨k.val, by dsimp only [bitPorts]; omega⟩
def cursorPort (k : Fin (n + 1)) : Inputs n 1 := .at ⟨n + 1 + k.val, by dsimp only [bitPorts]; omega⟩
def grantPort (k : Fin (n + 1)) : Outputs n 1 := .at ⟨k.val, by dsimp only [bitPorts]; omega⟩
def anyPort : Outputs n 1 := .at ⟨n + 1, by dsimp only [bitPorts]; omega⟩

def inputValues (cursor : Fin (n + 1)) (request : Fin (n + 1) → Bool) : Values (Inputs n) :=
  fun p => match p with
  | .at k => if h : k.val < n + 1 then BitVec.ofBool (request ⟨k.val, h⟩)
    else BitVec.ofBool (k.val - (n + 1) == cursor.val)

theorem input_request (cursor : Fin (n + 1)) (request : Fin (n + 1) → Bool) (k : Fin (n + 1)) :
    inputValues cursor request (requestPort k) = BitVec.ofBool (request k) := by
  simp [inputValues, requestPort, k.isLt]

theorem input_cursor (cursor : Fin (n + 1)) (request : Fin (n + 1) → Bool) (k : Fin (n + 1)) :
    inputValues cursor request (cursorPort k) = BitVec.ofBool (k == cursor) := by
  simp [inputValues, cursorPort, Nat.not_lt_of_ge (Nat.le_add_right (n + 1) k.val)]
  congr 1
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, Fin.ext_iff]

def selectedValue (winner : Fin (n + 1)) : {w : Nat} → Outputs n w → BitVec w :=
  fun p => match p with
  | .at k => if k.val < n + 1 then BitVec.ofBool (winner.val == k.val) else 1

def outputValues (selection : Option (Fin (n + 1))) : Values (Outputs n) :=
  match selection with
  | none => fun p => match p with | .at _ => 0
  | some winner => selectedValue winner

/-- One fixed-priority network per cursor, then a one-hot cursor selection.
There are O(N³) mux occurrences before emitter sharing and optimization;
this straightforward baseline prioritizes a small proof over area/depth. -/
def circuit (n : Nat) : Circuit (Inputs n) NoRegister (Outputs n) where
  next := fun r => nomatch r
  output := fun p => match p with
    | .at k => priority (fun c => .input (cursorPort c))
        (fun c => priority (fun r => .input (requestPort r))
          (fun r => .lit (selectedValue r (.at k))) (.lit 0) (RoundRobin.order c))
        (.lit 0) (List.finRange (n + 1))

theorem find_cursor (cursor : Fin (n + 1)) :
    (List.finRange (n + 1)).find? (fun k => k == cursor) = some cursor := by
  cases h : (List.finRange (n + 1)).find? (fun k => k == cursor) with
  | none =>
    have hn := List.find?_eq_none.mp h cursor (by simp)
    simp at hn
  | some winner =>
    have hw := List.find?_some h
    simp only [beq_iff_eq] at hw
    rw [hw]

theorem output_eq (cursor : Fin (n + 1)) (request : Fin (n + 1) → Bool) (p : Outputs n w) :
    (circuit n).observe (inputValues cursor request) NoRegister.values p =
      outputValues (RoundRobin.grant cursor request) p := by
  cases p with
  | «at» k =>
    simp only [Circuit.observe, circuit]
    rw [priority_eval _ _ _ _ _ _ _ (input_cursor cursor request), find_cursor]
    dsimp only
    rw [priority_eval _ _ _ _ _ _ _ (input_request cursor request)]
    cases h : RoundRobin.grant cursor request <;> simp only [RoundRobin.grant] at h <;> simp [h, outputValues, Expr.eval]

theorem grant_output (cursor : Fin (n + 1)) (request : Fin (n + 1) → Bool) (k : Fin (n + 1)) :
    (circuit n).observe (inputValues cursor request) NoRegister.values (grantPort k) =
      BitVec.ofBool (RoundRobin.grant cursor request == some k) := by
  rw [output_eq]
  cases RoundRobin.grant cursor request <;> simp [outputValues, selectedValue, grantPort, k.isLt]
  congr 1
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, Fin.ext_iff]

theorem any_output (cursor : Fin (n + 1)) (request : Fin (n + 1) → Bool) :
    (circuit n).observe (inputValues cursor request) NoRegister.values anyPort =
      BitVec.ofBool (RoundRobin.grant cursor request).isSome := by
  rw [output_eq]
  cases RoundRobin.grant cursor request <;> simp [outputValues, selectedValue, anyPort]

theorem any_output_zero_iff (cursor : Fin (n + 1)) (request : Fin (n + 1) → Bool) :
    (circuit n).observe (inputValues cursor request) NoRegister.values anyPort = 0 ↔
      ∀ k, request k = false := by
  rw [any_output, ← RoundRobin.grant_none_iff cursor request]
  cases RoundRobin.grant cursor request <;> simp

theorem grants_one_hot (cursor : Fin (n + 1)) (request : Fin (n + 1) → Bool)
    (a b : Fin (n + 1))
    (ha : (circuit n).observe (inputValues cursor request) NoRegister.values (grantPort a) = 1)
    (hb : (circuit n).observe (inputValues cursor request) NoRegister.values (grantPort b) = 1) : a = b := by
  rw [grant_output] at ha hb
  change BitVec.ofBool _ = BitVec.ofBool true at ha hb
  simp only [BitVec.ofBool_eq_iff_eq, beq_iff_eq] at ha hb
  exact Option.some.inj (ha.symm.trans hb)

theorem grant_output_requested (cursor : Fin (n + 1)) (request : Fin (n + 1) → Bool)
    (winner : Fin (n + 1))
    (h : (circuit n).observe (inputValues cursor request) NoRegister.values (grantPort winner) = 1) :
    request winner = true := by
  rw [grant_output] at h
  change BitVec.ofBool _ = BitVec.ofBool true at h
  simp only [BitVec.ofBool_eq_iff_eq, beq_iff_eq] at h
  exact RoundRobin.grant_requested h

theorem bit_roundtrip (x : BitVec 1) : BitVec.ofBool (x == 1) = x := by
  revert x
  decide +kernel

/-- Legal raw cursor bits have exactly one asserted bit. Request bits are
unrestricted; the one-bit type already gives complete two-state semantics. -/
def CursorEncoding (inputs : Values (Inputs n)) (cursor : Fin (n + 1)) : Prop :=
  ∀ k, inputs (cursorPort k) = BitVec.ofBool (k == cursor)

theorem input_encoding_eq (inputs : Values (Inputs n)) (cursor : Fin (n + 1))
    (h : CursorEncoding inputs cursor) :
    @inputs = @inputValues n cursor (fun k => inputs (requestPort k) == 1) := by
  funext w p
  cases p with
  | «at» k =>
    by_cases hk : k.val < n + 1
    · change inputs (requestPort ⟨k.val, hk⟩) =
        inputValues cursor (fun k => inputs (requestPort k) == 1) (requestPort ⟨k.val, hk⟩)
      rw [input_request]
      exact (bit_roundtrip _).symm
    · let r : Fin (n + 1) := ⟨k.val - (n + 1), by have := k.isLt; dsimp only [bitPorts] at this; omega⟩
      have he : cursorPort r = Stream.Ports.Signal.at k := by
        unfold cursorPort
        congr 1
        apply Fin.ext
        dsimp [r]
        omega
      rw [← he]
      exact (h r).trans (input_cursor cursor _ r).symm

theorem raw_output_eq (inputs : Values (Inputs n)) (cursor : Fin (n + 1))
    (h : CursorEncoding inputs cursor) (p : Outputs n w) :
    (circuit n).observe inputs NoRegister.values p =
      outputValues (RoundRobin.grant cursor (fun k => inputs (requestPort k) == 1)) p :=
  (congrArg (fun v : Values (Inputs n) => (circuit n).observe v NoRegister.values p)
    (input_encoding_eq inputs cursor h)).trans (output_eq cursor _ p)

end Pinwheel.Hardware.Arbitration.RoundRobinCircuit
