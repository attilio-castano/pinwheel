import Pinwheel.Hardware.Timebase.Circuit
import Pinwheel.Hardware.Stream.Ports
import Pinwheel.Hardware.TypedModule

namespace Pinwheel.Hardware.Uart.FractionalRx
open Pinwheel.Hardware.Stream

namespace Sync

abbrev inputPorts : Ports where
  size := 2
  widths := fun _ => 1
  names := fun k => #["reset", "rx_raw"][k]
  distinct := by decide +kernel

abbrev registerPorts : Ports where
  size := 2
  widths := fun _ => 1
  names := fun k => #["first", "second"][k]
  distinct := by decide +kernel

abbrev outputPorts : Ports where
  size := 1
  widths := fun _ => 1
  names := fun _ => "rx_sampled"
  distinct := by decide +kernel

abbrev Input := inputPorts.Signal
abbrev Register := registerPorts.Signal
abbrev Output := outputPorts.Signal

def circuit : Circuit Input Register Output where
  next
    | .at ⟨0, _⟩ => .mux (.input (.at 0)) (.lit 1) (.input (.at 1))
    | .at ⟨1, _⟩ => .mux (.input (.at 0)) (.lit 1) (.reg (.at 0))
    | .at ⟨k + 2, h⟩ => False.elim (by change k + 2 < 2 at h; omega)
  output
    | .at _ => .reg (.at 1)

def design : TypedModule Input Register Output :=
  ⟨"fractional_uart_sync", circuit, inputPorts.interface, registerPorts.interface, outputPorts.interface⟩

end Sync

namespace Sampler

abbrev inputPorts (w : Nat) : Ports where
  size := 4
  widths := fun k => if k.val < 2 then 1 else w
  names := fun k => #["reset", "rx_sampled", "half_num", "half_den"][k]
  distinct := by decide +kernel

abbrev registerPorts (w : Nat) : Ports where
  size := 7
  widths := fun k => #[1, 1, 5, 8, w + 1, w, w][k]
  names := fun k => #["active", "previous", "half_count", "data_reg", "phase", "num_reg", "den_reg"][k]
  distinct := by decide +kernel

abbrev outputPorts : Ports where
  size := 6
  widths := fun k => #[1, 1, 5, 1, 8, 1][k]
  names := fun k => #["busy", "sample", "half_index", "arrival", "data", "framing_error"][k]
  distinct := by decide +kernel

abbrev Input (w : Nat) := (inputPorts w).Signal
abbrev Register (w : Nat) := (registerPorts w).Signal
abbrev Output := outputPorts.Signal
abbrev E (w b : Nat) := Expr (Input w) (Register w) b

def reset : Input w 1 := .at ⟨0, by simp⟩
def line : Input w 1 := .at ⟨1, by simp⟩
def numerator : Input w w := .at ⟨2, by simp⟩
def denominator : Input w w := .at ⟨3, by simp⟩
def activeReg : Register w 1 := .at ⟨0, by simp⟩
def prevReg : Register w 1 := .at ⟨1, by simp⟩
def countReg : Register w 5 := .at ⟨2, by simp⟩
def dataReg : Register w 8 := .at ⟨3, by simp⟩
def phaseReg : Register w (w + 1) := .at ⟨4, by simp⟩
def numReg : Register w w := .at ⟨5, by simp⟩
def denReg : Register w w := .at ⟨6, by simp⟩

def detect : E w 1 :=
  .band (.inv (.reg activeReg)) (.band (.reg prevReg) (.band (.inv (.input line))
    (.band (.inv (.zero (.input denominator))) (.inv (.ult (.input numerator) (.input denominator))))))
def beat : E w 1 :=
  .band (.reg activeReg) (Timebase.beatExpr (.reg phaseReg) (.reg numReg) (.reg denReg))
def sample : E w 1 := .band beat (.inv (.slice 0 1 (by decide) (.reg countReg)))
def startCenter : E w 1 := .zero (.reg countReg)
def stopCenter : E w 1 := .equal (.reg countReg) (.lit 18)
def complete : E w 1 := .band sample stopCenter
def abort : E w 1 := .band sample (.band startCenter (.input line))
def capture : E w 1 := .band sample (.band (.inv startCenter) (.inv stopCenter))

def circuit (w : Nat) : Circuit (Input w) (Register w) Output where
  next r := match r with
    | .at ⟨0, _⟩ => .mux (.input reset) (.lit 0)
        (.mux (WordOps.wordOr complete abort) (.lit 0) (WordOps.wordOr detect (.reg activeReg)))
    | .at ⟨1, _⟩ => .mux (.input reset) (.lit 1) (.input line)
    | .at ⟨2, _⟩ => .mux (WordOps.wordOr (.input reset) (.inv (.reg activeReg))) (.lit 0)
        (.mux beat (WordOps.add (.reg countReg) (.lit 1)) (.reg countReg))
    | .at ⟨3, _⟩ => .mux (WordOps.wordOr (.input reset) detect) (.lit 0)
        (.mux capture (.concat (.input line) (.slice 1 7 (by decide) (.reg dataReg))) (.reg dataReg))
    | .at ⟨4, _⟩ => .mux (WordOps.wordOr (.input reset) (.inv (.reg activeReg))) (.lit 0)
        (Timebase.advanceExpr (.reg phaseReg) (.reg numReg) (.reg denReg))
    | .at ⟨5, _⟩ => .mux (.input reset) (.lit 0) (.mux detect (.input numerator) (.reg numReg))
    | .at ⟨6, _⟩ => .mux (.input reset) (.lit 0) (.mux detect (.input denominator) (.reg denReg))
    | .at ⟨k + 7, h⟩ => False.elim (by change k + 7 < 7 at h; omega)
  output o := .mux (.input reset) (.lit 0) (match o with
    | .at ⟨0, _⟩ => .reg activeReg
    | .at ⟨1, _⟩ => sample
    | .at ⟨2, _⟩ => .reg countReg
    | .at ⟨3, _⟩ => complete
    | .at ⟨4, _⟩ => .reg dataReg
    | .at ⟨5, _⟩ => .inv (.input line)
    | .at ⟨k + 6, h⟩ => False.elim (by change k + 6 < 6 at h; omega))

def design (w : Nat) : TypedModule (Input w) (Register w) Output :=
  ⟨"fractional_uart_sampler", circuit w, (inputPorts w).interface, (registerPorts w).interface,
    outputPorts.interface⟩

end Sampler

namespace Mailbox

abbrev inputPorts : Ports where
  size := 6
  widths := fun k => if k.val = 4 then 8 else 1
  names := fun k => #["reset", "take", "clear_overrun", "arrival", "data", "framing_error"][k]
  distinct := by decide +kernel

abbrev registerPorts : Ports where
  size := 4
  widths := fun k => if k.val = 1 then 8 else 1
  names := fun k => #["valid_reg", "data_reg", "error_reg", "overrun_reg"][k]
  distinct := by decide +kernel

abbrev outputPorts : Ports where
  size := 4
  widths := fun k => if k.val = 1 then 8 else 1
  names := fun k => #["valid", "result", "result_error", "overrun"][k]
  distinct := by decide +kernel

abbrev Input := inputPorts.Signal
abbrev Register := registerPorts.Signal
abbrev Output := outputPorts.Signal
abbrev E (b : Nat) := Expr Input Register b

def retain : E 1 := .band (.reg (.at 0)) (.inv (.input (.at 1)))
def admit : E 1 := .band (.input (.at 3)) (.inv retain)
def drop : E 1 := .band (.input (.at 3)) retain

/-- The slot consumes its previous result before accepting a new arrival. -/
def circuit : Circuit Input Register Output where
  next r := .mux (.input (.at 0)) (.lit 0) (match r with
    | .at ⟨0, _⟩ => WordOps.wordOr retain (.input (.at 3))
    | .at ⟨1, _⟩ => .mux admit (.input (.at 4)) (.mux retain (.reg (.at 1)) (.lit 0))
    | .at ⟨2, _⟩ => .mux admit (.input (.at 5)) (.mux retain (.reg (.at 2)) (.lit 0))
    | .at ⟨3, _⟩ => WordOps.wordOr (.band (.reg (.at 3)) (.inv (.input (.at 2)))) drop
    | .at ⟨k + 4, h⟩ => False.elim (by change k + 4 < 4 at h; omega))
  output
    | .at ⟨0, _⟩ => .reg (.at 0)
    | .at ⟨1, _⟩ => .reg (.at 1)
    | .at ⟨2, _⟩ => .reg (.at 2)
    | .at ⟨3, _⟩ => .reg (.at 3)
    | .at ⟨k + 4, h⟩ => False.elim (by change k + 4 < 4 at h; omega)

def design : TypedModule Input Register Output :=
  ⟨"fractional_uart_mailbox", circuit, inputPorts.interface, registerPorts.interface, outputPorts.interface⟩

end Mailbox

end Pinwheel.Hardware.Uart.FractionalRx
