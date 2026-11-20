import Pinwheel.Hardware.Timebase.Circuit
import Pinwheel.Hardware.Stream.Ports
import Pinwheel.Hardware.TypedModule

/-! A finite TX client for the fractional timebase. A START loads an eight-bit
image and independent timing configuration. The first bit is presented on
START; each subsequent beat completes the bit currently on the wire. -/
namespace Pinwheel.Hardware.Timebase.Tx
open Pinwheel.Hardware.Stream

abbrev inputPorts (w : Nat) : Ports where
  size := 5
  widths := fun k => if k.val < 2 then 1 else if k.val = 2 then 8 else w
  names := fun k => #["reset", "start", "image", "numerator", "denominator"][k]
  distinct := by decide +kernel

abbrev registerPorts (w : Nat) : Ports where
  size := 5
  widths := fun k => if k.val = 0 then 8 else if k.val = 1 then 4 else if k.val = 2 then w + 1 else w
  names := fun k => #["shift", "remaining", "phase", "numerator_reg", "denominator_reg"][k]
  distinct := by decide +kernel

abbrev outputPorts : Ports where
  size := 3
  widths := fun _ => 1
  names := fun k => #["busy", "tx", "beat"][k]
  distinct := by decide +kernel

abbrev Input (w : Nat) := (inputPorts w).Signal
abbrev Register (w : Nat) := (registerPorts w).Signal
abbrev Output := outputPorts.Signal
abbrev E (w b : Nat) := Expr (Input w) (Register w) b

def reset : Input w 1 := .at ⟨0, by simp⟩
def start : Input w 1 := .at ⟨1, by simp⟩
def image : Input w 8 := .at ⟨2, by simp⟩
def numerator : Input w w := .at ⟨3, by simp⟩
def denominator : Input w w := .at ⟨4, by simp⟩

def shiftReg : Register w 8 := .at ⟨0, by simp⟩
def remainingReg : Register w 4 := .at ⟨1, by simp⟩
def phaseReg : Register w (w + 1) := .at ⟨2, by simp⟩
def numeratorReg : Register w w := .at ⟨3, by simp⟩
def denominatorReg : Register w w := .at ⟨4, by simp⟩

def busy : Output 1 := .at ⟨0, by simp⟩
def tx : Output 1 := .at ⟨1, by simp⟩
def completedBit : Output 1 := .at ⟨2, by simp⟩

def running : E w 1 := .inv (.zero (.reg remainingReg))

def accept : E w 1 :=
  .band (.input start) (.band (.inv running)
    (.band (.inv (.zero (.input denominator))) (.inv (.ult (.input numerator) (.input denominator)))))

def tick : E w 1 :=
  .band running (beatExpr (.reg phaseReg) (.reg numeratorReg) (.reg denominatorReg))

def circuit (w : Nat) : Circuit (Input w) (Register w) Output where
  next r := .mux (.input reset) (.lit 0) (match r with
    | .at ⟨0, _⟩ => .mux accept (.input image)
        (.mux tick (WordOps.shiftRight 1 (.reg shiftReg)) (.reg shiftReg))
    | .at ⟨1, _⟩ => .mux accept (.lit 8)
        (.mux tick (.sub (.reg remainingReg) (.lit 1)) (.reg remainingReg))
    | .at ⟨2, _⟩ => .mux running (advanceExpr (.reg phaseReg) (.reg numeratorReg) (.reg denominatorReg)) (.lit 0)
    | .at ⟨3, _⟩ => .mux accept (.input numerator) (.reg numeratorReg)
    | .at ⟨4, _⟩ => .mux accept (.input denominator) (.reg denominatorReg)
    | .at ⟨k + 5, h⟩ => False.elim (by change k + 5 < 5 at h; omega))
  output o := match o with
    | .at ⟨0, _⟩ => .mux (.input reset) (.lit 0) running
    | .at ⟨1, _⟩ => .mux (.input reset) (.lit 1) (.mux running (.slice 0 1 (by decide) (.reg shiftReg)) (.lit 1))
    | .at ⟨2, _⟩ => .mux (.input reset) (.lit 0) tick
    | .at ⟨k + 3, h⟩ => False.elim (by change k + 3 < 3 at h; omega)

def module (w : Nat) : TypedModule (Input w) (Register w) Output :=
  ⟨"fractional_tx", circuit w, (inputPorts w).interface, (registerPorts w).interface, outputPorts.interface⟩

def component (w : Nat) :
    Timed.Component (Values (Input w)) (Values (Register w)) (Values Output) :=
  ⟨(circuit w).step, (circuit w).observe⟩

theorem reset_eq (i : Values (Input w)) (s : Values (Register w)) (h : i reset = 1#1)
    (r : Register w b) : (component w).step i s r = 0 := by
  simp [component, Circuit.step, circuit, Expr.eval, h]
  done

/-- The active TX clock uses the same rational phase and beat as the source
model. START and reset are separate edges in this interface. -/
theorem active_timing (p : Period) (i : Values (Input w)) (s : Values (Register w))
    (unreset : i reset ≠ 1#1) (active : s remainingReg ≠ 0#4)
    (hp : (s numeratorReg).toNat = p.numerator)
    (hq : (s denominatorReg).toNat = p.denominator)
    (phase : (s phaseReg).toNat < p.numerator) :
    ((circuit w).step i s phaseReg).toNat = advance p (s phaseReg).toNat ∧
      (circuit w).observe i s completedBit = BitVec.ofBool (beat p (s phaseReg).toNat) := by
  have timing := expressions_correct p (.reg phaseReg) (.reg numeratorReg) (.reg denominatorReg)
    i s hp hq phase
  have enabled : running.eval i s = 1 := by simp [running, Expr.eval, active]
  constructor
  · simpa [Circuit.step, circuit, Expr.eval, phaseReg, unreset, enabled] using timing.2
  · cases fire : beat p (s phaseReg).toNat <;>
      simp [Circuit.observe, circuit, Expr.eval, completedBit, unreset, tick, enabled, timing.1, fire]
  done

end Pinwheel.Hardware.Timebase.Tx
