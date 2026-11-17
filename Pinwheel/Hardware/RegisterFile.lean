import Pinwheel.Hardware.Stream.Ports
import Pinwheel.Hardware.Execution.Memory
import Pinwheel.Hardware.Implementation

/-! Two combinational read ports and one synchronous write port. Address zero
has no physical storage and always reads zero. Reset is synchronous and wins
over writing; reads observe the old bank until the edge, even during reset.
All widths, including zero, have Lean semantics. Emitting zero-width ports is a
separate backend concern. No forwarding, additional latency, or memory macro
is implied by this flip-flop and balanced-multiplexer implementation. -/
namespace Pinwheel.Hardware.RegisterFile

set_option backward.isDefEq.respectTransparency false

abbrev State (a w : Nat) := Fin (2^a-1) → BitVec w

def read (state : State a w) (address : BitVec a) : BitVec w :=
  if h : address.toNat = 0 then 0 else
    state ⟨address.toNat-1, by have := address.isLt; omega⟩

def write (state : State a w) (address : BitVec a) (data : BitVec w) : State a w :=
  fun k => if address.toNat = k.val+1 then data else state k

def initial : State a w := fun _ => 0

def inputPorts (a w : Nat) : Stream.Ports where
  size := 6
  widths := fun k => if k.val < 2 then 1 else if k.val = 3 then w else a
  names := fun k => #["reset", "write_enable", "write_address", "write_data", "read_address_0", "read_address_1"][k]
  distinct := by decide +kernel

def outputPorts (w : Nat) : Stream.Ports where
  size := 2
  widths := fun _ => w
  names := fun k => #["read_data_0", "read_data_1"][k]
  distinct := by decide +kernel

def registerPorts (a w : Nat) : Stream.Ports where
  size := 2^a-1
  widths := fun _ => w
  names := fun k => "word_" ++ Nat.repr (k.val+1)
  distinct := by
    intro x y h
    simp only [String.append_right_inj] at h
    exact Fin.ext (Nat.add_right_cancel (Nat.repr_injective h))

abbrev Input (a w : Nat) := (inputPorts a w).Signal
abbrev Output (w : Nat) := (outputPorts w).Signal
abbrev Register (a w : Nat) := (registerPorts a w).Signal

def inputInterface (a w : Nat) := (inputPorts a w).interface
def outputInterface (w : Nat) := (outputPorts w).interface
def registerInterface (a w : Nat) := (registerPorts a w).interface

def reset : Input a w 1 := .at ⟨0, by change 0 < 6; decide⟩
def writeEnable : Input a w 1 := .at ⟨1, by change 1 < 6; decide⟩
def writeAddress : Input a w a := .at ⟨2, by change 2 < 6; decide⟩
def writeData : Input a w w := .at ⟨3, by change 3 < 6; decide⟩
def readAddress (port : Fin 2) : Input a w a :=
  if port.val = 0 then .at ⟨4, by change 4 < 6; decide⟩
  else .at ⟨5, by change 5 < 6; decide⟩
def readData (port : Fin 2) : Output w w := .at port
def word (k : Fin (2^a-1)) : Register a w w := .at k

def encode (state : State a w) : Values (Register a w)
  | _, .at k => state k

def view (state : Values (Register a w)) : State a w := fun k => state (word k)

def spec (a w : Nat) : Timed.Component (Values (Input a w)) (State a w) (Values (Output w)) where
  step := fun i state => if i reset = 1 then initial else
    if i writeEnable = 1 then write state (i writeAddress) (i writeData) else state
  observe := fun i state {_} o => match o with
    | .at port => read state (i (readAddress port))

def wordExpr (address : BitVec a) : Expr I (Register a w) w :=
  if h : address.toNat = 0 then .lit 0 else
    .reg (word ⟨address.toNat-1, by have := address.isLt; omega⟩)

def readExpr (address : Expr I (Register a w) a) : Expr I (Register a w) w :=
  Execution.readTree a wordExpr address

def circuit (a w : Nat) : Circuit (Input a w) (Register a w) (Output w) where
  next := fun r => match r with
    | .at k => .mux (.input reset) (.lit 0)
      (.mux (.band (.input writeEnable)
        (.equal (.input writeAddress) (.lit (BitVec.ofNat a (k.val+1)))))
        (.input writeData) (.reg (.at k)))
  output := fun o => match o with
    | .at port => readExpr (.input (readAddress port))

theorem readExpr_eval (address : Expr I (Register a w) a)
    (i : Values I) (s : Values (Register a w)) :
    (readExpr address).eval i s = read (view s) (address.eval i s) := by
  simp only [readExpr, Execution.readTree_correct, wordExpr, read]
  split <;> rfl

theorem address_eq (address : BitVec a) (k : Fin (2^a-1)) :
    address = BitVec.ofNat a (k.val+1) ↔ address.toNat = k.val+1 := by
  have bound : k.val+1 < 2^a := by have := k.isLt; omega
  simp [← BitVec.toNat_inj, Nat.mod_eq_of_lt bound]

theorem step_eq (i : Values (Input a w)) (s : Values (Register a w)) (k : Fin (2^a-1)) :
    (circuit a w).step i s (word k) = (spec a w).step i (view s) k := by
  change (if i reset = 1 then (0 : BitVec w) else
    if i writeEnable &&& BitVec.ofBool (decide (i writeAddress = BitVec.ofNat a (k.val+1))) = 1
      then i writeData else s (word k)) =
    (if i reset = 1 then initial else
      if i writeEnable = 1 then write (view s) (i writeAddress) (i writeData) else view s) k
  rcases BitVec.eq_zero_or_eq_one (i writeEnable) with he | he
  all_goals rcases BitVec.eq_zero_or_eq_one (i reset) with hr | hr
  all_goals simp [write, initial, view, he, hr, address_eq]
  by_cases ha : (i writeAddress).toNat = k.val+1 <;> simp [ha]

@[simp] theorem read_zero (state : State a w) : read state 0 = 0 := by simp [read]

@[simp] theorem write_zero (state : State a w) (data : BitVec w) : write state 0 data = state := by
  funext k
  simp [write]

theorem write_same (state : State a w) (k : Fin (2^a-1)) (data : BitVec w) :
    write state (BitVec.ofNat a (k.val+1)) data k = data := by
  have h := (address_eq (BitVec.ofNat a (k.val+1)) k).mp rfl
  simp [write, h]

theorem write_other (state : State a w) (address : BitVec a) (data : BitVec w)
    (k : Fin (2^a-1)) (h : address.toNat ≠ k.val+1) : write state address data k = state k := by
  simp [write, h]

theorem read_write_same (state : State a w) (address : BitVec a) (data : BitVec w)
    (h : address ≠ 0) : read (write state address data) address = data := by
  have hn : address.toNat ≠ 0 := by intro hz; exact h (BitVec.eq_of_toNat_eq hz)
  simp only [read, dif_neg hn, write]
  exact if_pos (by omega)

theorem read_write_other (state : State a w) (dest source : BitVec a) (data : BitVec w)
    (h : source ≠ dest) : read (write state dest data) source = read state source := by
  by_cases hz : source.toNat = 0
  · simp [read, hz]
  · have hn : dest.toNat ≠ source.toNat-1+1 := by
      intro he
      apply h
      apply BitVec.eq_of_toNat_eq
      omega
    simp [read, write, hz, hn]

theorem write_overwrite (state : State a w) (address : BitVec a) (first second : BitVec w) :
    write (write state address first) address second = write state address second := by
  funext k
  by_cases h : address.toNat = k.val+1 <;> simp [write, h]

@[simp] theorem view_encode (state : State a w) : view (encode state) = state := rfl

@[simp] theorem encode_view (state : Values (Register a w)) :
    @encode a w (view state) = @state := by
  funext b r
  cases r
  rfl

theorem step_view (i : Values (Input a w)) (s : Values (Register a w)) :
    view ((circuit a w).step i s) = (spec a w).step i (view s) := by
  funext k
  exact step_eq i s k

theorem output_eq (i : Values (Input a w)) (s : Values (Register a w)) (o : Output w b) :
    (circuit a w).observe i s o = (spec a w).observe i (view s) o := by
  cases o
  exact readExpr_eval _ i s

/-- This is a pre-edge observation: write and reset controls cannot forward
new storage values onto either read port before the edge. -/
theorem observe_read (i : Values (Input a w)) (s : Values (Register a w)) (port : Fin 2) :
    (circuit a w).observe i s (readData port) = read (view s) (i (readAddress port)) :=
  readExpr_eval _ i s

theorem after_write_same (i : Values (Input a w)) (s : Values (Register a w))
    (hr : i reset = 0) (he : i writeEnable = 1) (ha : i writeAddress ≠ 0) :
    read (view ((circuit a w).step i s)) (i writeAddress) = i writeData := by
  rw [step_view]
  simpa [spec, hr, he] using read_write_same (view s) (i writeAddress) (i writeData) ha

theorem after_write_other (i : Values (Input a w)) (s : Values (Register a w))
    (hr : i reset = 0) (he : i writeEnable = 1) (address : BitVec a)
    (ha : address ≠ i writeAddress) :
    read (view ((circuit a w).step i s)) address = read (view s) address := by
  rw [step_view]
  simpa [spec, hr, he] using read_write_other (view s) (i writeAddress) address (i writeData) ha

theorem zero_write_ignored (i : Values (Input a w)) (s : Values (Register a w))
    (hr : i reset = 0) (ha : i writeAddress = 0) :
    view ((circuit a w).step i s) = view s := by
  rw [step_view]
  simp [spec, hr, ha]
  intro _
  exact write_zero (view s) (i writeData)

def implementation (a w : Nat) : Implementation (circuit a w) (spec a w) where
  Valid := fun _ => True
  encode := encode
  preserved := fun _ _ _ => trivial
  step_eq := fun i state _ _ r => by
    cases r
    exact step_eq i (encode state) _
  output_eq := fun i state _ _ o => output_eq i (encode state) o

theorem reset_eq (i : Values (Input a w)) (s : Values (Register a w))
    (h : i reset = 1) (r : Register a w b) :
    (circuit a w).step i s r = encode initial r := by
  cases r with
  | «at» k =>
    change (if i reset = 1 then 0 else _) = 0
    exact if_pos h

def resetCertificate (a w : Nat) : (implementation a w).Reset reset where
  initial := initial
  initial_valid := trivial
  reset_eq := fun i s h _ r => reset_eq i s h r

theorem raw_trace (state : Values (Register a w)) (inputs : List (Values (Input a w))) :
    (circuit a w).component.trace state inputs = (spec a w).trace (view state) inputs := by
  simpa only [implementation, encode_view] using (implementation a w).trace_eq (view state) trivial inputs

theorem trace_after_reset (i : Values (Input a w)) (s : Values (Register a w))
    (h : i reset = 1) (inputs : List (Values (Input a w))) :
    (circuit a w).component.trace ((circuit a w).step i s) inputs =
      (spec a w).trace initial inputs :=
  Implementation.Reset.trace_after_reset (implementation a w) reset (resetCertificate a w) i s h inputs

theorem readExpr_bind_eval (input : {b : Nat} → I b → Expr J S b)
    (register : {b : Nat} → Register a w b → Expr J S b)
    (address : Expr I (Register a w) a) (i : Values J) (s : Values S) :
    ((readExpr address).bind input register).eval i s =
      read (fun k => (register (word k)).eval i s) ((address.bind input register).eval i s) := by
  simp only [Expr.eval_bind, readExpr_eval]
  rfl

end Pinwheel.Hardware.RegisterFile
