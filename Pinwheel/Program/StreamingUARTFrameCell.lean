import Pinwheel.Program.StreamingUARTQuiet
import Pinwheel.Program.StreamingUARTFrameControl

namespace Pinwheel.Program.StreamingUART.FrameCell
open Pinwheel.Program.StreamingReady
open QuietTiming

@[simp] theorem sampleInputs_pc (s : State a) (inputs : List Input) :
    (sampleInputs s inputs).pc = s.pc := by rw [sampleInputs_eq]

@[simp] theorem sampleInputs_remaining (s : State a) (inputs : List Input) :
    (sampleInputs s inputs).remaining = s.remaining := by rw [sampleInputs_eq]

@[simp] theorem sampleInputs_countdown (s : State a) (inputs : List Input) :
    (sampleInputs s inputs).countdown = s.countdown := by rw [sampleInputs_eq]

@[simp] theorem sampleInputs_cellBit (s : State a) (inputs : List Input) :
    (sampleInputs s inputs).cellBit = s.cellBit := by rw [sampleInputs_eq]

@[simp] theorem sampleInputs_tx (s : State a) (inputs : List Input) :
    (sampleInputs s inputs).tx = s.tx := by rw [sampleInputs_eq]

@[simp] theorem sampleInputs_rx (s : State a) (inputs : List Input) :
    (sampleInputs s inputs).rx = s.rx := by rw [sampleInputs_eq]

@[simp] theorem sampleInputs_txShift (s : State a) (inputs : List Input) :
    (sampleInputs s inputs).txShift = s.txShift := by rw [sampleInputs_eq]

@[simp] theorem sampleInputs_txValid (s : State a) (inputs : List Input) :
    (sampleInputs s inputs).txValid = s.txValid := by rw [sampleInputs_eq]

@[simp] theorem sampleInputs_rxPartial (s : State a) (inputs : List Input) :
    (sampleInputs s inputs).rxPartial = s.rxPartial := by rw [sampleInputs_eq]

@[simp] theorem sampleInputs_rxUsed (s : State a) (inputs : List Input) :
    (sampleInputs s inputs).rxUsed = s.rxUsed := by rw [sampleInputs_eq]

@[simp] theorem sampleInputs_generation (s : State a) (inputs : List Input) :
    (sampleInputs s inputs).generation = s.generation := by rw [sampleInputs_eq]

@[simp] theorem sampleInputs_transfer (s : State a) (inputs : List Input) :
    (sampleInputs s inputs).transfer = s.transfer := by rw [sampleInputs_eq]

@[simp] theorem sampleInputs_txAccepted (s : State a) (inputs : List Input) :
    (sampleInputs s inputs).txAccepted = s.txAccepted := by rw [sampleInputs_eq]

@[simp] theorem sampleInputs_txConsumed (s : State a) (inputs : List Input) :
    (sampleInputs s inputs).txConsumed = s.txConsumed := by rw [sampleInputs_eq]

@[simp] theorem sampleInputs_rxProduced (s : State a) (inputs : List Input) :
    (sampleInputs s inputs).rxProduced = s.rxProduced := by rw [sampleInputs_eq]

@[simp] theorem sampleInputs_rxPopped (s : State a) (inputs : List Input) :
    (sampleInputs s inputs).rxPopped = s.rxPopped := by rw [sampleInputs_eq]

@[simp] theorem sampleInputs_total (s : State a) (inputs : List Input) :
    (sampleInputs s inputs).total = s.total := by rw [sampleInputs_eq]

@[simp] theorem sampleInputs_pins (s : State a) (inputs : List Input) :
    (sampleInputs s inputs).pins = s.pins := by rw [sampleInputs_eq]

theorem sampleInputs_rebase (s t : State a) (inputs : List Input)
    (first : s.samplerFirst = t.samplerFirst) (second : s.samplerSecond = t.samplerSecond) :
    (sampleInputs s inputs).samplerFirst = (sampleInputs t inputs).samplerFirst ∧
    (sampleInputs s inputs).samplerSecond = (sampleInputs t inputs).samplerSecond := by
  induction inputs generalizing s t with
  | nil => exact ⟨first,second⟩
  | cons i rest ih =>
    exact ih (s.sample i.rawInputs) (t.sample i.rawInputs) rfl first

def samplePair (first second : BitVec 2) (inputs : List Input) : BitVec 2 × BitVec 2 :=
  inputs.foldl (fun pair i => (i.rawInputs,pair.1)) (first,second)

@[simp] theorem samplePair_nil (first second : BitVec 2) :
    samplePair first second [] = (first,second) := rfl

@[simp] theorem samplePair_append (first second : BitVec 2) (before after : List Input) :
    samplePair first second (before ++ after) =
      samplePair (samplePair first second before).1 (samplePair first second before).2 after :=
  List.foldl_append

@[simp] theorem samplePair_cons (first second : BitVec 2) (i : Input) (rest : List Input) :
    samplePair first second (i :: rest) = samplePair i.rawInputs first rest := rfl

@[simp] theorem samplePair_single (first second : BitVec 2) (i : Input) :
    samplePair first second [i] = (i.rawInputs,first) := rfl

theorem sampleInputs_pair (s : State a) (inputs : List Input) :
    sampleInputs s inputs =
      {s with
        samplerFirst := (samplePair s.samplerFirst s.samplerSecond inputs).1,
        samplerSecond := (samplePair s.samplerFirst s.samplerSecond inputs).2} := by
  induction inputs generalizing s with
  | nil => rfl
  | cons i rest ih =>
    change sampleInputs (s.sample i.rawInputs) rest = _
    rw [ih]
    rfl

/-- The sole sample appended by one UART receive cell. This is an expected
state transformation, not a definition of the executing machine. -/
def captured (s : State a) (bit : Bool) : BitVec 32 :=
  (s.rxPartial <<< 1) ||| BitVec.ofNat 32 (if bit then 1 else 0)

def cellExit (s : State a) (bit : Bool) : State a :=
  {s with
    phase := if s.remaining.toNat > 1 then .boundary else .fetch
    pc := if s.remaining.toNat > 1 then s.pc else s.pc+1
    remaining := s.remaining-1
    countdown := 0
    cellBit := false
    pins := ⟨0,0⟩
    rxPartial := if s.remaining == 1 then 0 else captured s bit
    rxUsed := if s.remaining == 1 then 0 else s.rxUsed+1
    rxProduced := s.rxProduced+1
    rx := s.rx.tick (if s.remaining == 1 then
      some ⟨captured s bit,⟨s.rxUsed.toNat % 32,Nat.mod_lt _ (by decide)⟩⟩ else none) false}

theorem rx_cell_run (p : Profile) (s : State a) (first lowLast highLast : Input)
    (lowWait highWait : List Input)
    (phase : s.phase = .boundary) (current : s.current = .stream (cell p) none)
    (room : s.rx.writable = true) (used : s.rxUsed ≠ 31#6)
    (quietFirst : Quiet first) (quietLow : ∀ i ∈ lowWait,Quiet i)
    (quietLowLast : Quiet lowLast) (quietHigh : ∀ i ∈ highWait,Quiet i)
    (quietHighLast : Quiet highLast)
    (lowLength : lowWait.length = (cell p).lowDuration.val)
    (highLength : highWait.length = (cell p).highDuration.val)
    (bit : Bool)
    (sample : (sampleInputs (s.sample first.rawInputs) lowWait).samplerSecond[p.rxInput.val] = bit) :
    run (image p).program s ([first] ++ lowWait ++ [lowLast] ++ highWait ++ [highLast]) =
      sampleInputs (cellExit s bit) ([first] ++ lowWait ++ [lowLast] ++ highWait ++ [highLast]) := by
  have reserve := boundary_reserve (image p).program s first (cell p) quietFirst phase current
    rfl rfl room
  have low := low_finish (image p).program
    {s.sample first.rawInputs with
      phase := .low
      countdown := BitVec.ofNat 8 (cell p).lowDuration.val,
      cellBit := false,pins := (cell p).dataPins false (s.remaining == 1) false}
    lowWait lowLast rfl quietLow quietLowLast
    (by simp only [BitVec.toNat_ofNat]; simpa [Nat.mod_eq_of_lt (cell p).lowDuration.isLt] using lowLength)
    (by simp [State.sample,current,Instruction.hasHighGuard])
  have high := high_finish (image p).program
    ((lowExit {sampleInputs
      {s.sample first.rawInputs with
      phase := .low
      countdown := BitVec.ofNat 8 (cell p).lowDuration.val,
        cellBit := false,pins := (cell p).dataPins false (s.remaining == 1) false}
      lowWait with countdown := 0}).sample lowLast.rawInputs)
    highWait highLast rfl quietHigh quietHighLast
    (by simp only [lowExit,State.enterHigh,State.sample,sampleInputs_current];
        simp [current,Instruction.cell,highLength])
  have split : [first] ++ lowWait ++ [lowLast] ++ highWait ++ [highLast] =
      first :: ((lowWait ++ [lowLast]) ++ (highWait ++ [highLast])) := by
    simp only [List.append_assoc,List.cons_append,List.nil_append]
  rw [split]
  change run (image p).program (step (image p).program first s)
    ((lowWait ++ [lowLast]) ++ (highWait ++ [highLast])) = _
  rw [reserve,run_append,low,high]
  have sampledBit : (samplePair first.rawInputs s.samplerFirst lowWait).2[p.rxInput.val] = bit := by
    simpa only [sampleInputs_pair,State.sample] using sample
  simp [highExit,lowExit,State.enterHigh,State.captureData,State.captures,
    State.emittingCapture,State.timedOut,State.waitReady,State.highPins,State.lastCell,
    State.capturedWord,State.enginePush,cellExit,captured,State.sample,
    current,Instruction.cell,Instruction.isStream,Instruction.hasHighGuard,
    cell,Streaming.Cell.dataPins,Streaming.Cell.basePins,used,
    Bool.beq_eq_decide_eq,sampleInputs_pair,sampledBit]

/-- One complete receive cell reads the raw pin two sampler clocks before its
capture edge. All other raw values and the initial sampler state are arbitrary. -/
theorem rx_cell_clocks (p : Profile) (s : State a) (incoming : Nat → Input) (offset : Nat)
    (phase : s.phase = .boundary) (current : s.current = .stream (cell p) none)
    (room : s.rx.writable = true) (used : s.rxUsed ≠ 31#6)
    (quiet : ∀ n,Quiet (incoming n)) :
    run (image p).program s (FrameSamples.clocks incoming offset (4*p.Q)) =
      sampleInputs (cellExit s ((incoming (offset+2*p.Q-3)).rawInputs[p.rxInput.val]))
        (FrameSamples.clocks incoming offset (4*p.Q)) := by
  have q := p.Q_ge4
  have total : (cell p).lowDuration.val+(cell p).highDuration.val+3 = 4*p.Q := by
    simp only [cell]
    omega
  rw [← total,FrameSamples.clocks_layout]
  refine rx_cell_run p s _ _ _ _ _ phase current room used (quiet _) ?_ (quiet _) ?_ (quiet _)
    (FrameSamples.clocks_length _ _ _) (FrameSamples.clocks_length _ _ _) _ ?_
  · intro i member
    simp only [FrameSamples.clocks,List.mem_map] at member
    rcases member with ⟨n,_,rfl⟩
    exact quiet _
  · intro i member
    simp only [FrameSamples.clocks,List.mem_map] at member
    rcases member with ⟨n,_,rfl⟩
    exact quiet _
  · have enough : 2 ≤ (cell p).lowDuration.val := by simp only [cell]; omega
    have length : (cell p).lowDuration.val = ((cell p).lowDuration.val-2)+2 := by omega
    change (FrameSamples.sampled (s.sample (incoming offset).rawInputs)
      (FrameSamples.clocks incoming (offset+1) (cell p).lowDuration.val)).samplerSecond[p.rxInput.val] = _
    rw [length,FrameSamples.sampled_window]
    have index : offset+1+((cell p).lowDuration.val-2) = offset+2*p.Q-3 := by
      simp only [cell]
      omega
    rw [index]

end Pinwheel.Program.StreamingUART.FrameCell
