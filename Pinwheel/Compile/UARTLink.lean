import Pinwheel.UART.LinkProofs
import Pinwheel.Compile.UART
import Pinwheel.Compile.UARTRxProofs

/-! Two independently clocked program instances connected through the digital link contract. -/
namespace Pinwheel.Compile.UARTLink
open Pinwheel.UART.Link

def txSource (cfg : Pinwheel.UART.Config) (byte : BitVec 8) (incoming : Nat → Bool)
    (cycle : Nat) : Bool := (UART.execute cfg byte incoming cycle).levels[0]

def pins (input : Fin 2) (signal spare : Bool) : Engine.Reactive.Inputs :=
  if input.val = 0 then BitVec.ofBoolListBE [spare, signal]
  else BitVec.ofBoolListBE [signal, spare]

def inputs (t : Timing) (byte : BitVec 8) (txIncoming spare : Nat → Bool) (age : Nat → Nat)
    (cycle : Nat) : Engine.Reactive.Inputs :=
  pins t.rx.input (observe t (txSource t.tx byte txIncoming) age cycle) (spare cycle)

theorem encodePin_selected (pin : Bool) : (UART.encodePin pin)[0] = pin := by
  cases pin <;> rfl

theorem txSource_correct (cfg : Pinwheel.UART.Config) (byte : BitVec 8)
    (incoming : Nat → Bool) (cycle : Nat) :
    txSource cfg byte incoming cycle = Pinwheel.UART.expected cfg byte cycle := by
  exact (congrArg (fun levels : Engine.Levels => levels[0])
    (UART.waveform_correct cfg byte incoming cycle)).trans (encodePin_selected _)
  done

theorem pins_selected (input : Fin 2) (signal spare : Bool) :
    (pins input signal spare)[input.val] = signal := by
  decide +revert

theorem inputs_selected (t : Timing) (byte : BitVec 8) (txIncoming spare : Nat → Bool)
    (age : Nat → Nat) (cycle : Nat) :
    (inputs t byte txIncoming spare age cycle)[t.rx.input.val] =
      observe t (txSource t.tx byte txIncoming) age cycle :=
  pins_selected t.rx.input _ _

/-- Compiler composition removes the waveform and sampled-frame premises from the client. -/
theorem receive_correct (t : Timing) (b : Latency) (byte : BitVec 8)
    (txIncoming spare : Nat → Bool) (age : Nat → Nat)
    (safe : Safe t b) (within : b.Contains age) :
    ∃ detected, firstEdge t b.earliest ≤ detected ∧ detected ≤ firstEdge t b.latest ∧
      UARTRx.result (UARTRx.execute t.rx (inputs t byte txIncoming spare age)
        (completion t detected)) = some (.byte byte) := by
  obtain ⟨d, lo, hi, result⟩ := Pinwheel.UART.Link.receive_correct t b
    (txSource t.tx byte txIncoming) byte age (txSource_correct t.tx byte txIncoming) safe within
  exact ⟨d, lo, hi, by simpa only [UARTRx.result_correct, inputs_selected] using result⟩
  done

theorem receive_fixed (t : Timing) (byte : BitVec 8) (txIncoming spare : Nat → Bool)
    (delay : Nat) (safe : Safe t (.fixed delay)) :
    UARTRx.result (UARTRx.execute t.rx (inputs t byte txIncoming spare (fun _ => delay))
      (completion t (firstEdge t delay))) = some (.byte byte) := by
  simpa only [UARTRx.result_correct, inputs_selected] using
    Pinwheel.UART.Link.receive_fixed t (txSource t.tx byte txIncoming) byte delay
      (txSource_correct t.tx byte txIncoming) safe
  done

theorem ideal_receive (rx : Pinwheel.UART.Rx.Config) (fits : rx.bitCycles ≤ 256)
    (start : Nat) (armed : 2 ≤ start) (byte : BitVec 8) (txIncoming spare : Nat → Bool) :
    UARTRx.result (UARTRx.execute rx (inputs (ideal rx fits start) byte txIncoming spare (fun _ => 0))
      (start + (rx.half + 9 * rx.bitCycles))) = some (.byte byte) := by
  simpa only [ideal_firstEdge rx fits start armed, completion,
    show (ideal rx fits start).rx = rx from rfl] using
    receive_fixed (ideal rx fits start) byte txIncoming spare 0 (ideal_safe rx fits start armed)
  done

end Pinwheel.Compile.UARTLink
