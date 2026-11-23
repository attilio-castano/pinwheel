import Pinwheel.Hardware.RegisterFile
import Pinwheel.Hardware.Processor.RV32I.Semantics

/-! The RV32I specialization of the generic two-read/one-write register bank.
Only x1..x31 are stored. This adapter establishes architectural register access,
not instruction retirement, writeback scheduling, or a complete CPU datapath. -/
namespace Pinwheel.Hardware.Processor.RV32I.RegisterFile

abbrev Input := Hardware.RegisterFile.Input 5 32
abbrev Register := Hardware.RegisterFile.Register 5 32
abbrev Output := Hardware.RegisterFile.Output 32

def circuit : Circuit Input Register Output := Hardware.RegisterFile.circuit 5 32
def view (state : Values Register) : Semantics.Registers := Hardware.RegisterFile.view state
def encode (state : Semantics.Registers) : Values Register := Hardware.RegisterFile.encode state

theorem register_count : (Hardware.RegisterFile.registerInterface 5 32).size = 31 := rfl

theorem read_eq (state : Semantics.Registers) (address : RV32I.Register) :
    Hardware.RegisterFile.read state address = Semantics.read state address := rfl

theorem write_eq (state : Semantics.Registers) (address : RV32I.Register) (data : Word) :
    Hardware.RegisterFile.write state address data = Semantics.write state address data := rfl

@[simp] theorem view_encode (state : Semantics.Registers) : view (encode state) = state := rfl

theorem encode_view (state : Values Register) : @encode (view state) = @state :=
  Hardware.RegisterFile.encode_view state

/-- Reset clears x1..x31; otherwise an enabled write is exactly the pure
RV32I register update, including discarded writes to x0. -/
theorem step_eq (i : Values Input) (state : Values Register) :
    view (circuit.step i state) =
      if i Hardware.RegisterFile.reset = 1 then (fun _ => 0) else
        if i Hardware.RegisterFile.writeEnable = 1 then
          Semantics.write (view state) (i Hardware.RegisterFile.writeAddress) (i Hardware.RegisterFile.writeData)
        else view state := Hardware.RegisterFile.step_view i state

theorem observe_eq (i : Values Input) (state : Values Register) (port : Fin 2) :
    circuit.observe i state (Hardware.RegisterFile.readData port) =
      Semantics.read (view state) (i (Hardware.RegisterFile.readAddress port)) :=
  Hardware.RegisterFile.observe_read i state port

theorem reset_eq (i : Values Input) (state : Values Register)
    (h : i Hardware.RegisterFile.reset = 1) : view (circuit.step i state) = (fun _ => 0) := by
  rw [step_eq, if_pos h]

theorem readExpr_eval (address : Expr I Register 5) (i : Values I) (state : Values Register) :
    (Hardware.RegisterFile.readExpr address).eval i state = Semantics.read (view state) (address.eval i state) :=
  Hardware.RegisterFile.readExpr_eval address i state

end Pinwheel.Hardware.Processor.RV32I.RegisterFile
