import Pinwheel.Program.StreamingSWD
import Pinwheel.Program.StreamingSWDReply
import Pinwheel.Program.StreamingReadyBitTrace

/-! The capture cuts of the actual SWD program use the resolved SWDIO
sample from two core clocks earlier. -/
namespace Pinwheel.Program.StreamingSWD
open StreamingReady StreamingUART.QuietTiming

set_option maxRecDepth 10000
set_option maxHeartbeats 5000000

def leading (before next : Pins) : Bool := !before.levels[0] && next.levels[0]

private def risesFrom (seen : Nat) : List Pins → List Nat
  | before :: after :: later =>
    seen :: risesFrom (seen + if leading before after then 1 else 0) (after :: later)
  | [_] => [seen]
  | [] => []

/-- The number of rising SWCLK edges already seen at each public pad snapshot. -/
def risesSeen (pins : List Pins) : List Nat := risesFrom 0 pins

private theorem risesFrom_length (pins : List Pins) (seen : Nat) :
    (risesFrom seen pins).length = pins.length := by
  induction pins generalizing seen with
  | nil => rfl
  | cons before after ih =>
    cases after with
    | nil => rfl
    | cons next later => simp [risesFrom,ih]

theorem risesSeen_length (pins : List Pins) : (risesSeen pins).length = pins.length :=
  risesFrom_length pins 0

private def risingCutsFrom (k : Nat) : List Pins → List Nat
  | before :: after :: later =>
    (if leading before after then [k] else []) ++ risingCutsFrom (k+1) (after :: later)
  | _ => []

/-- Pre-edge indices of every rising SWCLK edge. -/
def risingCuts (pins : List Pins) : List Nat := risingCutsFrom 0 pins

private def captureCuts : List Pose → List (Nat × Nat)
  | before :: after :: later =>
    (if before.capture then [(0,before.rxPort)] else []) ++
      (captureCuts (after :: later)).map (fun cut => (cut.1+1,cut.2))
  | _ => []

/-- Cuts index the raw samples before their two synchronizer steps. -/
def responseApertures : List Nat := (captureCuts reference).map (fun cut => cut.1-2)

def responseSamples (raw : List (BitVec 2)) : List Bool :=
  responseApertures.map fun k => (raw[k]?.getD 0).getLsbD 1

def referenceSeenAt (k : Nat) : Nat :=
  (risesSeen (reference.map Pose.pins))[k]?.getD 0

private def apertureTape (s : State a) (inputs : List Input) : List (BitVec 2) :=
  s.samplerSecond :: s.samplerFirst :: inputs.map (·.rawInputs)

private def posedSamples (snapshots : List Pose) (apertures : List (BitVec 2)) : List Bool :=
  (captureCuts snapshots).map (fun cut => (apertures[cut.1]?.getD 0).getLsbD cut.2)

private theorem advance_tape (s : State a) (i : Input) (rest : List Input) (quiet : Quiet i) :
    (apertureTape s (i :: rest)).tail = apertureTape (step program i s) rest := by
  have samplers := step_samples program s i (quiet.runtime i)
  simp only [apertureTape,List.map_cons,List.tail_cons,samplers.1,samplers.2]

private theorem cuts_cons (s : State a) (i : Input) (rest : List Input) :
    captureCuts (poses s (i :: rest)) =
      (if s.captures then [(0,s.current.cell.rxInput.val)] else []) ++
        (captureCuts (poses (step program i s) rest)).map (fun cut => (cut.1+1,cut.2)) := by
  cases rest <;> rfl

private theorem samples_cons (s : State a) (i : Input) (rest : List Input) (quiet : Quiet i) :
    posedSamples (poses s (i :: rest)) (apertureTape s (i :: rest)) =
      s.rxEvent ++ posedSamples (poses (step program i s) rest)
        (apertureTape (step program i s) rest) := by
  rw [posedSamples,cuts_cons,List.map_append,List.map_map,← advance_tape s i rest quiet]
  cases cap : s.captures <;> simp [cap,State.rxEvent,posedSamples,apertureTape,Function.comp_def]

private theorem trace_quiet (trace : BitTrace) (s : State a) (i : Input) (quiet : Quiet i) :
    trace.step s i = trace.clock s i := by
  simp [BitTrace.step,quiet.cold,quiet.command]

private theorem capture_poses (s : State a) (inputs : List Input) (trace : BitTrace)
    (quiet : ∀ i ∈ inputs, Quiet i) :
    (traceRun program s trace inputs).captured =
      trace.captured ++ posedSamples (poses s inputs) (apertureTape s inputs) := by
  induction inputs generalizing s trace with
  | nil => simp [traceRun,poses,posedSamples,captureCuts]
  | cons i rest ih =>
    have first := quiet i List.mem_cons_self
    rw [traceRun,ih _ _ (fun j member => quiet j (List.mem_cons_of_mem _ member)),
      trace_quiet trace s i first,samples_cons s i rest first]
    simp [BitTrace.clock,List.append_assoc]

private theorem reference_cuts :
    ∀ cut ∈ captureCuts reference, 2 ≤ cut.1 ∧ cut.1 < clockCount ∧ cut.2 = 1 := by
  decide +kernel

theorem reference_apertures_bound : ∀ k ∈ responseApertures, k < clockCount := by
  intro k member
  obtain ⟨cut,inCuts,rfl⟩ := List.mem_map.mp member
  exact Nat.lt_of_le_of_lt (Nat.sub_le _ _) (reference_cuts cut inCuts).2.1

/-- The target's independently clocked reply advances from ACK[0] to
    parity across the thirty-six actual sample apertures. -/
theorem reference_rise_counts :
    responseApertures.map referenceSeenAt = (List.range 36).map (fun k => 9+k) := by
  decide +kernel

@[simp] theorem responseSamples_length (raw : List (BitVec 2)) :
    (responseSamples raw).length = 36 := by
  have counts := congrArg List.length reference_rise_counts
  simpa only [responseSamples,List.length_map,List.length_range] using counts

/-- Every response capture is tied to its physical SWCLK rise. The
    first nine rises precede the reply and the last nine follow it. -/
theorem reference_capture_edges :
    responseApertures.map (· + 2) = ((risingCuts (reference.map Pose.pins)).drop 9).take 36 := by
  decide +kernel

/-- A peer advancing on public SWCLK rises provides precisely its own reply
    bits when the controller's delayed aperture reads the shared line. -/
theorem response_of_peer (bits : List Bool) (raw : List (BitVec 2)) (size : bits.length = 36)
    (wire : ∀ k, k < clockCount → 9 ≤ referenceSeenAt k → referenceSeenAt k < 45 →
      (raw[k]?.getD 0).getLsbD 1 = (bits[referenceSeenAt k - 9]?.getD false)) :
    responseSamples raw = bits := by
  calc
    _ = (responseApertures.map referenceSeenAt).map (fun seen => bits[seen-9]?.getD false) := by
      unfold responseSamples
      rw [List.map_map]
      apply List.map_congr_left
      intro k inside
      have count : referenceSeenAt k ∈ (List.range 36).map (fun j => 9+j) := by
        rw [← reference_rise_counts]
        exact List.mem_map_of_mem inside
      obtain ⟨j,within,seen⟩ := List.mem_map.mp count
      have bound := List.mem_range.mp within
      exact wire k (reference_apertures_bound k inside) (by omega) (by omega)
    _ = bits := by
      rw [reference_rise_counts,List.map_map]
      simp only [Function.comp_def,Nat.add_comm 9,Nat.add_sub_cancel]
      apply List.ext_getElem (by simp [size])
      intro k _ inside
      simp [List.getElem?_eq_getElem inside]

private theorem aperture_at (first second : BitVec 2) (raw : List (BitVec 2)) (k : Nat)
    (within : 2 ≤ k) : (second :: first :: raw)[k]? = raw[k-2]? := by
  cases k with
  | zero => omega
  | succ k =>
    cases k with
    | zero => omega
    | succ k => rfl

private theorem reference_samples (s : State a) (inputs : List Input) :
    posedSamples reference (apertureTape s inputs) = responseSamples (inputs.map (·.rawInputs)) := by
  unfold posedSamples responseSamples responseApertures
  rw [List.map_map]
  apply List.map_congr_left
  intro cut inside
  have ⟨lower,_,port⟩ := reference_cuts cut inside
  simp only [Function.comp_def,apertureTape,aperture_at _ _ _ _ lower,port]

/-- For a run with the standard control trace, only physically clocked
    response bits enter the capture FIFO. Earlier sampler contents are unused. -/
theorem captured_of_poses (initial : State a) (inputs : List Input)
    (quiet : ∀ i ∈ inputs, Quiet i) (controls : poses initial inputs = reference) :
    (traceRun program initial {} inputs).captured = responseSamples (inputs.map (·.rawInputs)) := by
  rw [capture_poses initial inputs {} quiet,controls]
  exact reference_samples initial inputs

theorem captured_response (before : State 1) (start : Input) (inputs : List Input)
    (count : start.startCount = 36#16) (quiet : ∀ i ∈ inputs, Quiet i)
    (length : inputs.length = clockCount) :
    (traceRun program (before.start program start) {} inputs).captured =
      responseSamples (inputs.map (·.rawInputs)) :=
  captured_of_poses _ inputs quiet (quiet_poses before start inputs count quiet length)

end Pinwheel.Program.StreamingSWD
