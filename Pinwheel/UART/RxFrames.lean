import Pinwheel.UART.RxStreamProofs

namespace Pinwheel.UART.Rx.Stream

structure FrameSpec where
  detected : Nat
  byte : BitVec 8
  deriving DecidableEq, Repr

def FrameSpec.span (f : FrameSpec) (cfg : Config) : Nat := completion cfg f.detected + 1

def horizon (cfg : Config) : List FrameSpec → Nat
  | [] => 0
  | frame :: rest => frame.span cfg + horizon cfg rest

def Matches (cfg : Config) (incoming : Nat → Input) : List FrameSpec → Prop
  | [] => True
  | frame :: rest => Frame cfg incoming frame.detected frame.byte ∧
      Matches cfg (fun n => incoming (frame.span cfg + n)) rest

def expected (cfg : Config) : List FrameSpec → Nat → Option Outcome
  | [], _ => none
  | frame :: rest, n =>
    if n < frame.span cfg then
      if n = completion cfg frame.detected then some (.byte frame.byte) else none
    else expected cfg rest (n - frame.span cfg)

theorem state_of_receiver (s : State) (h : s.receiver = Rx.initial) :
    s = ⟨Rx.initial, s.buffer⟩ := by
  cases s <;> simp_all

/-- All receive events of a finite frame sequence, independent of consumer readiness. -/
theorem series_correct (cfg : Config) (frames : List FrameSpec) (buffer : Buffer.State)
    (incoming : Nat → Input) (valid : Matches cfg incoming frames) (n : Nat)
    (within : n ≤ horizon cfg frames) :
    arrival (run cfg ⟨Rx.initial, buffer⟩ incoming n) = expected cfg frames n := by
  induction frames generalizing buffer incoming n with
  | nil => simp [show n = 0 from Nat.eq_zero_of_le_zero within, run, arrival, Rx.initial, Rx.result, expected]
  | cons frame rest ih =>
    by_cases before : n < frame.span cfg
    case neg =>
      rw [expected, if_neg before]
      conv => lhs; rw [show n = frame.span cfg + (n - frame.span cfg) by omega, run_add]
      rw [state_of_receiver (run cfg ⟨Rx.initial, buffer⟩ incoming (frame.span cfg))
        (frame_rearm cfg buffer incoming frame.detected frame.byte valid.1)]
      exact ih _ _ valid.2 _ (by unfold horizon at within; omega)
    case pos =>
      rw [expected, if_pos before]
      split
      case isFalse h =>
        exact frame_silent cfg buffer incoming frame.detected n frame.byte valid.1
          (by unfold FrameSpec.span at before; omega)
      case isTrue h => simpa only [h] using frame_complete cfg buffer incoming frame.detected frame.byte valid.1

end Pinwheel.UART.Rx.Stream
