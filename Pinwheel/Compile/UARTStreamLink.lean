import Pinwheel.Compile.UARTRxStream
import Pinwheel.UART.StreamLinkProofs

namespace Pinwheel.Compile.UARTStreamLink
open Pinwheel.UART

/-- The independent-clock stream theorem for the existing compiled RX and its supervisor. -/
theorem receive_series (t : Link.Timing) (b : Link.Latency) (bytes : List (BitVec 8))
    (age : Nat → Nat) (incoming : Nat → Rx.Stream.Input) (spare : Nat → Bool)
    (buffer : Rx.Buffer.State) (safe : StreamLink.Safe t b) (within : b.Contains age)
    (line : ∀ n, (incoming n).line = StreamLink.sampled t bytes age n)
    (quiet : ∀ n, (incoming n).reset = false) :
    ∃ frames, frames.map Rx.Stream.FrameSpec.byte = bytes ∧ StreamLink.Windows t b frames ∧
      ∀ n, n ≤ Rx.Stream.horizon t.rx frames →
        UARTRx.result (UARTRxStream.run t.rx (UARTRxStream.lift t.rx ⟨Rx.initial, buffer⟩)
          incoming spare n).core = Rx.Stream.expected t.rx frames n := by
  obtain ⟨frames, payloads, windows, correct⟩ :=
    StreamLink.receive_series t b bytes age incoming buffer safe within line quiet
  refine ⟨frames, payloads, windows, fun n hn => ?_⟩
  rw [UARTRxStream.run_simulation t.rx ⟨Rx.initial, buffer⟩ incoming spare rfl]
  simpa only [UARTRxStream.lift, UARTRx.result_lift, Rx.Stream.arrival] using correct n hn

end Pinwheel.Compile.UARTStreamLink
