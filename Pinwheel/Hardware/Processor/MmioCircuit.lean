import Pinwheel.Hardware.Processor.MmioInterface
import Pinwheel.Hardware.WordOps
import Pinwheel.Hardware.Stream.Encoding

namespace Pinwheel.Hardware.Processor.MmioCircuit
open MmioInterface

abbrev registerPorts : Hardware.Stream.Ports where
  size := 8
  widths := fun k => if k.val < 2 then 32 else if k.val = 3 ∨ k.val = 5 then 8 else 1
  names := fun k => #["gpio", "timer", "tx_active", "tx_data", "rx_valid", "rx_data", "overrun", "framing"][k]
  distinct := by decide +kernel

abbrev Register := registerPorts.Signal
def gpio : Register 32 := .at ⟨0, by simp⟩
def timer : Register 32 := .at ⟨1, by simp⟩
def txActiveReg : Register 1 := .at ⟨2, by simp⟩
def txDataReg : Register 8 := .at ⟨3, by simp⟩
def rxValidReg : Register 1 := .at ⟨4, by simp⟩
def rxDataReg : Register 8 := .at ⟨5, by simp⟩
def overrun : Register 1 := .at ⟨6, by simp⟩
def framing : Register 1 := .at ⟨7, by simp⟩
def registers : Interface Register := registerPorts.interface

def view (s : Values Register) : MmioModel.State :=
  ⟨s gpio, s timer, if s txActiveReg = 1 then some (s txDataReg) else none,
    if s rxValidReg = 1 then some (s rxDataReg) else none,
    s overrun == 1, s framing == 1⟩

def encode (s : MmioModel.State) : Values Register
  | _, .at ⟨0, _⟩ => s.gpioOut
  | _, .at ⟨1, _⟩ => s.timer
  | _, .at ⟨2, _⟩ => BitVec.ofBool s.tx.isSome
  | _, .at ⟨3, _⟩ => s.tx.getD 0
  | _, .at ⟨4, _⟩ => BitVec.ofBool s.rx.isSome
  | _, .at ⟨5, _⟩ => s.rx.getD 0
  | _, .at ⟨6, _⟩ => BitVec.ofBool s.overrun
  | _, .at ⟨7, _⟩ => BitVec.ofBool s.framing
  | _, .at ⟨k+8, h⟩ => False.elim (by change k+8 < 8 at h; omega)

abbrev E (w : Nat) := Expr Input Register w

def selected (d : BitVec 2) (w : BitVec 6) : E 1 :=
  .band (.equal (.input device) (.lit d)) (.equal (.input word) (.lit w))

def active : E 1 := .band (.inv (.input reset)) (.input requestValid)
def gpioWrite : E 1 := .band (.input requestValid) (.band (selected 0 1) (.input write))
def txStart : E 1 := .band (.input requestValid)
  (.band (selected 2 1) (.band (.input write) (.inv (.reg txActiveReg))))
def rxConsume : E 1 := .band (.input requestValid)
  (.band (selected 2 2) (.band (.inv (.input write)) (.reg rxValidReg)))
def clearErrors : E 1 := .band (.input requestValid) (.band (selected 2 3) (.input write))
def rxRoom : E 1 := (Expr.inv (.reg rxValidReg)).bor rxConsume
def rxCapture : E 1 := .band (.input rxValid) rxRoom
def rxOverflow : E 1 := .band (.input rxValid) (.inv rxRoom)

def statusExpr : E 32 := .concat (.lit (0#28))
  (.concat (.reg framing) (.concat (.reg overrun) (.concat (.reg rxValidReg) (.inv (.reg txActiveReg)))))

def gpioCode : E 3 := .mux (.equal (.input word) (.lit 0))
  (.mux (.input write) (.lit 3) (.lit 0))
  (.mux (.equal (.input word) (.lit 1)) (.mux (.input write) (.lit 1) (.lit 0)) (.lit 2))
def timerCode : E 3 := .mux (.equal (.input word) (.lit 0))
  (.mux (.input write) (.lit 3) (.lit 0)) (.lit 2)
def uartCode : E 3 := .mux (.equal (.input word) (.lit 0))
  (.mux (.input write) (.lit 3) (.lit 0))
  (.mux (.equal (.input word) (.lit 1))
    (.mux (.input write) (.mux (.reg txActiveReg) (.lit 4) (.lit 1)) (.lit 3))
    (.mux (.equal (.input word) (.lit 2))
      (.mux (.input write) (.lit 3) (.mux (.reg rxValidReg) (.lit 0) (.lit 5)))
      (.mux (.equal (.input word) (.lit 3)) (.mux (.input write) (.lit 1) (.lit 3)) (.lit 2))))

def codeExpr : E 3 := .mux (.equal (.input device) (.lit 0)) gpioCode
  (.mux (.equal (.input device) (.lit 1)) timerCode
    (.mux (.equal (.input device) (.lit 2)) uartCode (.lit 2)))

def dataExpr : E 32 := .mux (.equal (.input device) (.lit 0))
  (.mux (.equal (.input word) (.lit 0)) (.input gpioInput) (.reg gpio))
  (.mux (.equal (.input device) (.lit 1)) (.reg timer)
    (.mux (.equal (.input word) (.lit 0)) statusExpr (.concat (.lit (0#24)) (.reg rxDataReg))))

def circuit : Circuit Input Register Output where
  next r := .mux (.input reset) (.lit 0) (match r with
    | .at ⟨0, _⟩ => .mux gpioWrite (.input data) (.reg gpio)
    | .at ⟨1, _⟩ => WordOps.add (.reg timer) (.lit 1)
    | .at ⟨2, _⟩ => txStart.bor (.band (.reg txActiveReg) (.inv (.input txComplete)))
    | .at ⟨3, _⟩ => .mux txStart (.slice 0 8 (by decide) (.input data)) (.reg txDataReg)
    | .at ⟨4, _⟩ => rxCapture.bor (.band (.reg rxValidReg) (.inv rxConsume))
    | .at ⟨5, _⟩ => .mux rxCapture (.input rxData) (.reg rxDataReg)
    | .at ⟨6, _⟩ => (Expr.band (.reg overrun)
        (.inv (.band clearErrors (.slice 2 1 (by decide) (.input data))))).bor rxOverflow
    | .at ⟨7, _⟩ => (Expr.band (.reg framing)
        (.inv (.band clearErrors (.slice 3 1 (by decide) (.input data))))).bor (.input framingError)
    | .at ⟨k+8, h⟩ => False.elim (by change k+8 < 8 at h; omega))
  output o := match o with
    | .at ⟨0, _⟩ => .inv (.input reset)
    | .at ⟨1, _⟩ => active
    | .at ⟨2, _⟩ => .mux active codeExpr (.lit 0)
    | .at ⟨3, _⟩ => .mux (.band active (.equal codeExpr (.lit 0))) dataExpr (.lit 0)
    | .at ⟨4, _⟩ => .mux (.input reset) (.lit 0) (.reg gpio)
    | .at ⟨5, _⟩ => .band (.inv (.input reset)) (.reg txActiveReg)
    | .at ⟨6, _⟩ => .mux (.band (.inv (.input reset)) (.reg txActiveReg)) (.reg txDataReg) (.lit 0)
    | .at ⟨k+7, h⟩ => False.elim (by change k+7 < 7 at h; omega)

end Pinwheel.Hardware.Processor.MmioCircuit
