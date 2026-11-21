import Pinwheel.Hardware.Uart.FractionalRxLeaves
import Pinwheel.Hardware.Stream.Compose
import Pinwheel.Hardware.TypedHierarchy

namespace Pinwheel.Hardware.Uart.FractionalRx
open Pinwheel.Hardware.Stream

abbrev inputPorts (w : Nat) : Ports where
  size := 6
  widths := fun k => if k.val < 4 then 1 else w
  names := fun k => #["reset", "rx_raw", "take", "clear_overrun", "half_num", "half_den"][k]
  distinct := by decide +kernel

abbrev outputPorts : Ports where
  size := 7
  widths := fun k => #[1, 8, 1, 1, 1, 1, 5][k]
  names := fun k => #["valid", "result", "result_error", "overrun", "busy", "sample", "half_index"][k]
  distinct := by decide +kernel

abbrev wirePorts : Ports where
  size := 4
  widths := fun k => if k.val = 2 then 8 else 1
  names := fun k => #["rx_sampled", "arrival", "arrival_data", "arrival_error"][k]
  distinct := by decide +kernel

abbrev Input (w : Nat) := (inputPorts w).Signal
abbrev Register (w : Nat) := Joint Sync.Register (Joint (Sampler.Register w) Mailbox.Register)
abbrev Output := outputPorts.Signal
abbrev Wire := wirePorts.Signal
abbrev LeafPin (w : Nat) := Joint (Input w) Wire

def registers (w : Nat) : Interface (Register w) :=
  Joint.interface Sync.registerPorts.interface
    (Joint.interface (Sampler.registerPorts w).interface Mailbox.registerPorts.interface)

def syncReg (p : Sync.Register b) : Register w b := .left p
def sampleReg (p : Sampler.Register w b) : Register w b := .right (.left p)
def mailboxReg (p : Mailbox.Register b) : Register w b := .right (.right p)

def syncInput : Sync.Input b → Input w b
  | .at ⟨0, _⟩ => .at ⟨0, by simp⟩
  | .at ⟨1, _⟩ => .at ⟨1, by simp⟩
  | .at ⟨k + 2, h⟩ => False.elim (by change k + 2 < 2 at h; omega)

def samplerInput : Sampler.Input w b → LeafPin w b
  | .at ⟨0, _⟩ => .left (.at ⟨0, by simp⟩)
  | .at ⟨1, _⟩ => .right (.at 0)
  | .at ⟨2, _⟩ => .left (.at ⟨4, by simp⟩)
  | .at ⟨3, _⟩ => .left (.at ⟨5, by simp⟩)
  | .at ⟨k + 4, h⟩ => False.elim (by change k + 4 < 4 at h; omega)

def mailboxInput : Mailbox.Input b → LeafPin w b
  | .at ⟨0, _⟩ => .left (.at ⟨0, by simp⟩)
  | .at ⟨1, _⟩ => .left (.at ⟨2, by simp⟩)
  | .at ⟨2, _⟩ => .left (.at ⟨3, by simp⟩)
  | .at ⟨3, _⟩ => .right (.at 1)
  | .at ⟨4, _⟩ => .right (.at 2)
  | .at ⟨5, _⟩ => .right (.at 3)
  | .at ⟨k + 6, h⟩ => False.elim (by change k + 6 < 6 at h; omega)

def samplerSink : Sampler.Output b → TypedHierarchy.Sink Wire Output b
  | .at ⟨0, _⟩ => .output (.at 4)
  | .at ⟨1, _⟩ => .output (.at 5)
  | .at ⟨2, _⟩ => .output (.at 6)
  | .at ⟨3, _⟩ => .net (.at 1)
  | .at ⟨4, _⟩ => .net (.at 2)
  | .at ⟨5, _⟩ => .net (.at 3)
  | .at ⟨k + 6, h⟩ => False.elim (by change k + 6 < 6 at h; omega)

def mailboxOutput : Mailbox.Output b → Output b
  | .at ⟨0, _⟩ => .at 0
  | .at ⟨1, _⟩ => .at 1
  | .at ⟨2, _⟩ => .at 2
  | .at ⟨3, _⟩ => .at 3
  | .at ⟨k + 4, h⟩ => False.elim (by change k + 4 < 4 at h; omega)

abbrev E (w b : Nat) := Expr (Input w) (Register w) b

def syncExpr (v : Expr Sync.Input Sync.Register b) : E w b :=
  v.bind (fun p => .input (syncInput p)) (fun p => .reg (syncReg p))

def samplePin : Wire b → E w b
  | .at ⟨0, _⟩ => syncExpr (Sync.circuit.output (.at 0))
  | .at ⟨1, _⟩ => .lit 0
  | .at ⟨2, _⟩ => .lit 0
  | .at ⟨3, _⟩ => .lit 0
  | .at ⟨k + 4, h⟩ => False.elim (by change k + 4 < 4 at h; omega)

def flatPin (net : ∀ {b}, Wire b → E w b) : LeafPin w b → E w b
  | .left p => .input p
  | .right p => net p

def samplerExpr (v : Expr (Sampler.Input w) (Sampler.Register w) b) : E w b :=
  v.bind (fun p => flatPin samplePin (samplerInput p)) (fun p => .reg (sampleReg p))

def mailboxPin : Wire b → E w b
  | .at ⟨0, _⟩ => samplePin (.at 0)
  | .at ⟨1, _⟩ => samplerExpr ((Sampler.circuit w).output (.at 3))
  | .at ⟨2, _⟩ => samplerExpr ((Sampler.circuit w).output (.at 4))
  | .at ⟨3, _⟩ => samplerExpr ((Sampler.circuit w).output (.at 5))
  | .at ⟨k + 4, h⟩ => False.elim (by change k + 4 < 4 at h; omega)

def mailboxExpr (v : Expr Mailbox.Input Mailbox.Register b) : E w b :=
  v.bind (fun p => flatPin mailboxPin (mailboxInput p)) (fun p => .reg (mailboxReg p))

def circuit (w : Nat) : Circuit (Input w) (Register w) Output where
  next
    | .left p => syncExpr (Sync.circuit.next p)
    | .right (.left p) => samplerExpr ((Sampler.circuit w).next p)
    | .right (.right p) => mailboxExpr (Mailbox.circuit.next p)
  output
    | .at ⟨0, _⟩ => mailboxExpr (Mailbox.circuit.output (.at 0))
    | .at ⟨1, _⟩ => mailboxExpr (Mailbox.circuit.output (.at 1))
    | .at ⟨2, _⟩ => mailboxExpr (Mailbox.circuit.output (.at 2))
    | .at ⟨3, _⟩ => mailboxExpr (Mailbox.circuit.output (.at 3))
    | .at ⟨4, _⟩ => samplerExpr ((Sampler.circuit w).output (.at 0))
    | .at ⟨5, _⟩ => samplerExpr ((Sampler.circuit w).output (.at 1))
    | .at ⟨6, _⟩ => samplerExpr ((Sampler.circuit w).output (.at 2))
    | .at ⟨k + 7, h⟩ => False.elim (by change k + 7 < 7 at h; omega)

def flat (w : Nat) : TypedModule (Input w) (Register w) Output :=
  ⟨"fractional_uart_flat", circuit w, (inputPorts w).interface, registers w, outputPorts.interface⟩

def source : LeafPin w b → TypedHierarchy.Source (Input w) Wire b
  | .left p => .input p
  | .right p => .net p

def hierarchy (w : Nat) : TypedHierarchy (Input w) (Register w) Output Wire where
  name := "fractional_uart_rx"
  flat := flat w
  wires := wirePorts.interface
  instances := #[
    .connect "sync" Sync.design (fun p => .input (syncInput p))
      (fun | .at _ => .net (.at 0)) syncReg,
    .connect "sampler" (Sampler.design w) (fun p => source (samplerInput p)) samplerSink sampleReg,
    .connect "mailbox" Mailbox.design (fun p => source (mailboxInput p))
      (fun p => .output (mailboxOutput p)) mailboxReg]

end Pinwheel.Hardware.Uart.FractionalRx
