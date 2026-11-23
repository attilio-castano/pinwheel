import Pinwheel.Hardware.Uart.Interface
import Pinwheel.Hardware.WordOps

/-! Six-register sampled UART using only existing expression primitives.
Counters have enough space for the strict upper bound 10D. Malformed active
counts or RX phase3 suppress that unit's events and clear its active/phase
control on the next edge. They cannot wrap into a completion. Other inactive
metadata is retained; external reset clears all six registers.
-/
namespace Pinwheel.Hardware.Uart.Structural
open Physical

def width (d : Timing) : Nat := d.frame.log2+1

theorem frame_fits (d : Timing) : d.frame < 2^(width d) := Nat.lt_log2_self

theorem width_positive (d : Timing) : 0 < width d := by simp [width]

theorem stop_before_frame (d : Timing) : d.stopSample < d.frame := by
  have h := d.half_lt
  simp only [Timing.stopSample, Timing.frame]
  omega

inductive Register (d : Timing) : Nat → Type where
  | txActive : Register d 1
  | txCount : Register d (width d)
  | txByte : Register d 8
  | rxPhase : Register d 2
  | rxCount : Register d (width d)
  | rxByte : Register d 8

def registerPosition : Register d b → Fin 6
  | .txActive => 0 | .txCount => 1 | .txByte => 2
  | .rxPhase => 3 | .rxCount => 4 | .rxByte => 5

def registerSignal (d : Timing) : Fin 6 → Sigma (Register d)
  | ⟨0, _⟩ => ⟨1, .txActive⟩ | ⟨1, _⟩ => ⟨width d, .txCount⟩ | ⟨2, _⟩ => ⟨8, .txByte⟩
  | ⟨3, _⟩ => ⟨2, .rxPhase⟩ | ⟨4, _⟩ => ⟨width d, .rxCount⟩ | ⟨5, _⟩ => ⟨8, .rxByte⟩
  | ⟨k+6, h⟩ => False.elim (by omega)

def registerName (k : Fin 6) : String := #["tx_active", "tx_count", "tx_data", "rx_phase", "rx_count", "rx_data"][k]

theorem signal_position (r : Register d b) : registerSignal d (registerPosition r) = ⟨b, r⟩ := by cases r <;> rfl

theorem position_signal (k : Fin 6) : registerPosition (registerSignal d k).2 = k := by
  match k with
  | ⟨0, _⟩ | ⟨1, _⟩ | ⟨2, _⟩ | ⟨3, _⟩ | ⟨4, _⟩ | ⟨5, _⟩ => rfl
  | ⟨k+6, h⟩ => omega

def registers (d : Timing) : Hardware.Interface (Register d) where
  size := 6
  signal := registerSignal d
  position := registerPosition
  signal_position := signal_position
  label r := registerName (registerPosition r)
  unique := by
    intro i j h
    have hu : ∀ i j : Fin 6, registerName i = registerName j → i = j := by decide +kernel
    exact hu i j (by simpa only [position_signal] using h)

def view (s : Values (Register d)) : Uart.State :=
  ⟨if s .txActive = 1 then .active (s .txByte) (s .txCount).toNat else .idle,
   if s .rxPhase = 1 then .receiving (s .rxCount).toNat (s .rxByte)
   else if s .rxPhase = 2 then .waitHigh else .idle⟩

def Valid (d : Timing) (s : Values (Register d)) : Prop :=
  (s .txActive = 1 → (s .txCount).toNat < d.frame) ∧
  (s .rxPhase = 1 → (s .rxCount).toNat < d.stopSample) ∧ s .rxPhase ≠ 3

def encode (d : Timing) (s : Uart.State) : Values (Register d)
  | _, .txActive => match s.tx with | .idle => 0 | .active _ _ => 1
  | _, .txCount => match s.tx with | .idle => 0 | .active _ elapsed => BitVec.ofNat _ elapsed
  | _, .txByte => match s.tx with | .idle => 0 | .active byte _ => byte
  | _, .rxPhase => match s.rx with | .idle => 0 | .receiving _ _ => 1 | .waitHigh => 2
  | _, .rxCount => match s.rx with | .receiving elapsed _ => BitVec.ofNat _ elapsed | _ => 0
  | _, .rxByte => match s.rx with | .receiving _ byte => byte | _ => 0

abbrev E (d : Timing) (w : Nat) := Expr Physical.Input (Register d) w

def count (d : Timing) (n : Nat) : E d (width d) := .lit (BitVec.ofNat _ n)
def phase (n : BitVec 2) : E d 1 := .equal (.reg .rxPhase) (.lit n)
def txOkay (d : Timing) : E d 1 := .ult (.reg .txCount) (count d d.frame)
def rxOkay (d : Timing) : E d 1 := .ult (.reg .rxCount) (count d d.stopSample)
def txClosing (d : Timing) : E d 1 := .equal (.reg .txCount) (count d (d.frame-1))
def rxClosing (d : Timing) : E d 1 := .equal (.reg .rxCount) (count d (d.stopSample-1))
def txAccept : E d 1 := .band (.inv (.reg .txActive)) (.input txValid)
def rxDetect : E d 1 := .band (phase 0) (.inv (.input rx))
def badStart (d : Timing) : E d 1 := .band (.input rx) (.equal (.reg .rxCount) (count d (d.half-1)))
def rxAdvance (d : Timing) : E d 1 :=
  .band (phase 1) (.band (rxOkay d) (.band (.inv (badStart d)) (.inv (rxClosing d))))

def packExpr (bits : Fin 8 → E d 1) : E d 8 :=
  .concat (bits 7) (.concat (bits 6) (.concat (bits 5) (.concat (bits 4)
    (.concat (bits 3) (.concat (bits 2) (.concat (bits 1) (bits 0)))))))

def rxUpdated (d : Timing) : E d 8 := packExpr (fun k =>
  .mux (.equal (.reg .rxCount) (count d (d.dataSample k-1))) (.input rx)
    (.slice k.val 1 (by omega) (.reg .rxByte)))

/-- Nine fixed thresholds; no division, new primitive or variable-index mux. -/
def txSelect (d : Timing) : E d 1 :=
  .mux (.ult (.reg .txCount) (count d d.divisor)) (.lit 0)
  (.mux (.ult (.reg .txCount) (count d (2*d.divisor))) (.slice 0 1 (by decide) (.reg .txByte))
  (.mux (.ult (.reg .txCount) (count d (3*d.divisor))) (.slice 1 1 (by decide) (.reg .txByte))
  (.mux (.ult (.reg .txCount) (count d (4*d.divisor))) (.slice 2 1 (by decide) (.reg .txByte))
  (.mux (.ult (.reg .txCount) (count d (5*d.divisor))) (.slice 3 1 (by decide) (.reg .txByte))
  (.mux (.ult (.reg .txCount) (count d (6*d.divisor))) (.slice 4 1 (by decide) (.reg .txByte))
  (.mux (.ult (.reg .txCount) (count d (7*d.divisor))) (.slice 5 1 (by decide) (.reg .txByte))
  (.mux (.ult (.reg .txCount) (count d (8*d.divisor))) (.slice 6 1 (by decide) (.reg .txByte))
  (.mux (.ult (.reg .txCount) (count d (9*d.divisor))) (.slice 7 1 (by decide) (.reg .txByte)) (.lit 1)))))))))

def completedExpr (d : Timing) : E d 1 :=
  .band (.inv (.input reset)) (.band (.reg .txActive) (.band (txOkay d) (txClosing d)))
def arrivalExpr (d : Timing) : E d 1 :=
  .band (.inv (.input reset)) (.band (phase 1) (.band (rxOkay d) (.band (rxClosing d) (.input rx))))
def errorExpr (d : Timing) : E d 1 :=
  .band (.inv (.input reset)) (.band (phase 1) (.band (rxOkay d) (.band (rxClosing d) (.inv (.input rx)))))

def circuit (d : Timing) : Hardware.Circuit Physical.Input (Register d) Physical.Output where
  next r := .mux (.input reset) (.lit 0) (match r with
    | .txActive => .mux (.reg .txActive) (.band (txOkay d) (.inv (txClosing d))) (.input txValid)
    | .txCount => .mux txAccept (.lit 0)
        (.mux (.band (.reg .txActive) (.band (txOkay d) (.inv (txClosing d))))
          (WordOps.add (.reg .txCount) (.lit 1)) (.reg .txCount))
    | .txByte => .mux txAccept (.input txData) (.reg .txByte)
    | .rxPhase => .mux (phase 0) (.mux (.input rx) (.lit 0) (.lit 1))
        (.mux (phase 1) (.mux (rxOkay d)
          (.mux (badStart d) (.lit 0) (.mux (rxClosing d) (.mux (.input rx) (.lit 0) (.lit 2)) (.lit 1))) (.lit 0))
          (.mux (phase 2) (.mux (.input rx) (.lit 0) (.lit 2)) (.lit 0)))
    | .rxCount => .mux rxDetect (.lit 0)
        (.mux (rxAdvance d) (WordOps.add (.reg .rxCount) (.lit 1)) (.reg .rxCount))
    | .rxByte => .mux rxDetect (.lit 0) (.mux (rxAdvance d) (rxUpdated d) (.reg .rxByte)))
  output o := match o with
    | .at ⟨0, _⟩ => .mux (.input reset) (.lit 1)
        (.mux (.reg .txActive) (.mux (txOkay d) (txSelect d) (.lit 1)) (.lit 1))
    | .at ⟨1, _⟩ => .band (.inv (.input reset)) (.inv (.reg .txActive))
    | .at ⟨2, _⟩ => completedExpr d
    | .at ⟨3, _⟩ => arrivalExpr d
    | .at ⟨4, _⟩ => .mux (arrivalExpr d) (.reg .rxByte) (.lit 0)
    | .at ⟨5, _⟩ => errorExpr d
    | .at ⟨k+6, h⟩ => False.elim (by change k+6 < 6 at h; omega)

end Pinwheel.Hardware.Uart.Structural
