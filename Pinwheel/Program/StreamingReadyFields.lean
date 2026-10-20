import Pinwheel.Program.StreamingReadyWait

namespace Pinwheel.Program.StreamingReady

theorem engine_rx_fields (p : Program) (s : State a) :
    (engine p s).rxPartial = (if s.timedOut then 0 else
      if s.captures then (if s.emittingCapture then 0 else s.capturedWord) else s.rxPartial) ∧
    (engine p s).rxUsed = (if s.timedOut then 0 else
      if s.captures then (if s.emittingCapture then 0 else s.rxUsed + 1) else s.rxUsed) ∧
    (engine p s).rxProduced = s.rxProduced + (if s.captures then 1 else 0) := by
  cases phase : s.phase
  case waiting =>
    cases ready : s.waitReady <;> cases stream : s.current.isStream <;>
      cases expired : s.current.guard.limit.expires s.countdown <;>
      simp [engine,phase,ready,stream,expired,State.timedOut,State.captures,
        State.enterHigh,State.captureData,State.timeoutFault]
  case fetch =>
    cases fetched : p.fetch s.pc.toNat with
    | none => simp [engine,phase,fetched,State.stop,State.timedOut,State.captures]
    | some instruction =>
      cases instruction <;> simp [engine,phase,fetched,State.stop,State.timedOut,State.captures]
      split <;> simp
  case boundary =>
    cases credit : s.canReserve <;> simp [engine,phase,credit,State.timedOut,State.captures]
  case high =>
    by_cases zero : s.countdown = 0#8 <;> simp [engine,phase,zero,State.timedOut,State.captures]
  case low =>
    by_cases zero : s.countdown = 0#8 <;> cases guard : s.current.hasHighGuard <;>
      simp [engine,phase,zero,guard,State.timedOut,State.captures,State.enterHigh,State.captureData]
  all_goals simp [engine,phase,State.timedOut,State.captures]
  all_goals done

theorem engine_total (p : Program) (s : State a) : (engine p s).total = s.total := by
  unfold engine
  split <;> dsimp only [State.enterHigh,State.captureData,State.timeoutFault,State.stop]
  all_goals repeat' first | rfl | split

theorem engine_frame (p : Program) (s : State a) :
    (engine p s).tx = s.tx ∧ (engine p s).rx = s.rx ∧
    (engine p s).txAccepted = s.txAccepted ∧ (engine p s).rxPopped = s.rxPopped ∧
    (engine p s).generation = s.generation ∧ (engine p s).transfer = s.transfer ∧
    (engine p s).samplerFirst = s.samplerFirst ∧ (engine p s).samplerSecond = s.samplerSecond := by
  unfold engine
  split <;> dsimp only [State.enterHigh,State.captureData,State.timeoutFault,State.stop]
  all_goals repeat' first | rfl | constructor | split

def State.consumes (s : State a) : Bool :=
  s.phase == .boundary && s.canReserve && s.current.isStream && s.current.cell.transmit

theorem engine_tx_fields (p : Program) (s : State a) :
    (engine p s).txShift = (if s.consumes then s.selectedTx.data <<< 1 else s.txShift) ∧
    (engine p s).txValid =
      (if s.consumes then BitVec.ofNat 6 (s.selectedTx.validBits-1) else s.txValid) ∧
    (engine p s).txConsumed = s.txConsumed + (if s.consumes then 1 else 0) := by
  cases phase : s.phase
  case boundary =>
    cases credit : s.canReserve <;> cases stream : s.current.isStream <;>
      cases transmit : s.current.cell.transmit <;>
      simp [engine,phase,credit,stream,transmit,State.consumes]
  all_goals simp only [engine,phase]
  all_goals try dsimp only [State.enterHigh,State.captureData,State.timeoutFault,State.stop]
  all_goals simp [State.consumes,phase]
  all_goals repeat' first | rfl | constructor | split

end Pinwheel.Program.StreamingReady
