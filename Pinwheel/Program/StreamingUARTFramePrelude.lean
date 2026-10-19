import Pinwheel.Program.StreamingUARTFrameData
import Pinwheel.Program.StreamingUARTArm

namespace Pinwheel.Program.StreamingUART.FramePrelude
open Pinwheel.Program.StreamingReady
open QuietTiming FrameControl FrameCell FrameSamples

private theorem mark_bit (channel : Fin 2) : (3#2)[channel.val] = true := by
  revert channel
  decide +kernel

def startExit (s : State a) : State a := {s with phase := .fetch,pc := s.pc+1,countdown := 0}

def dataBase (p : Profile) (generation transfer : BitVec 16) : State a :=
  {Arm.armed (a := a) p generation transfer with
    phase := .boundary,pc := 5,current := .stream (cell p) none,cellBit := false}

theorem start_low {a : Nat} (p : Profile) (generation transfer : BitVec 16) (incoming : Nat → Input)
    (quiet : ∀ n,Quiet (incoming n))
    (falling : (incoming 0).rawInputs[p.rxInput.val] = false) :
    run (image p).program (Arm.armed (a := a) p generation transfer) (clocks incoming 0 3) =
      sampleInputs (startExit (Arm.armed (a := a) p generation transfer)) (clocks incoming 0 3) := by
  let s : State a := Arm.armed (a := a) p generation transfer
  have first := wait_unbounded_miss (image p).program s (incoming 0) ⟨0,0⟩ (startGuard p)
    ((quiet _).runtime _) (quiet _).tx (quiet _).rx rfl rfl rfl
    (by simp [s,Arm.armed,start_matches,mark_bit])
  have second := wait_unbounded_miss (image p).program (s.sample (incoming 0).rawInputs)
    (incoming 1) ⟨0,0⟩ (startGuard p) ((quiet _).runtime _) (quiet _).tx (quiet _).rx rfl rfl rfl
    (by simp [s,Arm.armed,State.sample,start_matches,mark_bit])
  have third := wait_ready (image p).program
    ((s.sample (incoming 0).rawInputs).sample (incoming 1).rawInputs)
    (incoming 2) ⟨0,0⟩ (startGuard p) ((quiet _).runtime _) (quiet _).tx (quiet _).rx rfl rfl
    (by simp [State.sample,start_matches,falling])
  have three : clocks incoming 0 3 = [incoming 0,incoming 1,incoming 2] := by
    simp [clocks,List.range_succ]
  rw [three]
  change step (image p).program (incoming 2)
    (step (image p).program (incoming 1) (step (image p).program (incoming 0) s)) = _
  rw [first,second,third]
  rfl

theorem pulseFinish_samples (s : State a) (c : Cell) (inputs : List Input) :
    pulseFinish (sampleInputs s inputs) c = sampleInputs (pulseFinish s c) inputs := by
  simp [pulseFinish,sampleInputs_pair]

theorem guardExit_samples (s : State a) (pins : Pins) (guard : Guard) (inputs : List Input) :
    guardExit (sampleInputs s inputs) pins guard = sampleInputs (guardExit s pins guard) inputs := by
  simp [guardExit,sampleInputs_pair]

theorem guardFault_samples (program : Program) (s : State a) (pins : Pins) (guard : Guard)
    (inputs : List Input) :
    guardFault program (sampleInputs s inputs) pins guard =
      sampleInputs (guardFault program s pins guard) inputs := by
  simp [guardFault,sampleInputs_pair]

theorem clocks_quiet (incoming : Nat → Input) (quiet : ∀ n,Quiet (incoming n))
    (offset edges : Nat) : ∀ i ∈ clocks incoming offset edges,Quiet i := by
  intro i member
  simp only [clocks,List.mem_map] at member
  rcases member with ⟨n,_,rfl⟩
  exact quiet _

def afterA (p : Profile) (generation transfer : BitVec 16) : State a :=
  pulseFinish (startExit (Arm.armed (a := a) p generation transfer)) (pulseA p)

theorem prefixA {a : Nat} (p : Profile) (generation transfer : BitVec 16) (incoming : Nat → Input)
    (quiet : ∀ n,Quiet (incoming n))
    (falling : (incoming 0).rawInputs[p.rxInput.val] = false) :
    run (image p).program (Arm.armed (a := a) p generation transfer) (clocks incoming 0 (2*p.Q+1)) =
      sampleInputs (afterA p generation transfer) (clocks incoming 0 (2*p.Q+1)) := by
  have q := p.Q_ge4
  have split : 2*p.Q+1 = 3+((pulseA p).lowDuration.val+(pulseA p).highDuration.val+4) := by
    simp only [pulseA]
    omega
  rw [split,clocks_add,run_append,start_low p generation transfer incoming quiet falling]
  have pulse := pulse_run (image p).program
    (sampleInputs (startExit (Arm.armed (a := a) p generation transfer)) (clocks incoming 0 3)) (pulseA p)
    (clocks incoming (0+3) ((pulseA p).lowDuration.val+(pulseA p).highDuration.val+4))
    (by simp [sampleInputs_pair,startExit])
    (by change (image p).program.fetch 2 = _; rw [source_fetch p 2 (by decide)]; rfl)
    (clocks_quiet incoming quiet _ _) (clocks_length _ _ _)
  rw [pulse,pulseFinish_samples,pulseFinish_samples,← FrameData.sampleInputs_append]
  rfl

def afterStart (p : Profile) (generation transfer : BitVec 16) : State a :=
  guardExit (afterA p generation transfer) ⟨0,0⟩ (checkStart p)

theorem prefixStart {a : Nat} (p : Profile) (generation transfer : BitVec 16) (incoming : Nat → Input)
    (quiet : ∀ n,Quiet (incoming n))
    (falling : (incoming 0).rawInputs[p.rxInput.val] = false)
    (startLow : (incoming (2*p.Q)).rawInputs[p.rxInput.val] = false) :
    run (image p).program (Arm.armed (a := a) p generation transfer) (clocks incoming 0 (2*p.Q+3)) =
      sampleInputs (afterStart p generation transfer) (clocks incoming 0 (2*p.Q+3)) := by
  have split : 2*p.Q+3 = (2*p.Q+1)+2 := by omega
  rw [split,clocks_add,run_append,prefixA p generation transfer incoming quiet falling]
  simp only [Nat.zero_add,clocks_two]
  have firstSample : (sampleInputs (afterA (a := a) p generation transfer)
      (clocks incoming 0 (2*p.Q+1))).samplerFirst = (incoming (2*p.Q)).rawInputs := by
    change (sampled _ _).samplerFirst = _
    simpa only [Nat.zero_add] using sampled_last (afterA (a := a) p generation transfer) incoming 0 (2*p.Q)
  have guardStep := guard_success (image p).program
    (sampleInputs (afterA (a := a) p generation transfer) (clocks incoming 0 (2*p.Q+1)))
    ⟨0,0⟩ (checkStart p) (incoming (2*p.Q+1)) (incoming (2*p.Q+1+1)) (quiet _) (quiet _)
    (by simp [sampleInputs_pair,afterA,pulseFinish])
    (by rw [sampleInputs_pc]; change (image p).program.fetch 3 = _; rw [source_fetch p 3 (by decide)]; rfl)
    (by rw [checkStart_matches,firstSample,startLow]; rfl)
  rw [guardStep,guardExit_samples,← FrameData.sampleInputs_append]
  rfl

theorem falseStart {a : Nat} (p : Profile) (generation transfer : BitVec 16) (incoming : Nat → Input)
    (quiet : ∀ n,Quiet (incoming n))
    (falling : (incoming 0).rawInputs[p.rxInput.val] = false)
    (startHigh : (incoming (2*p.Q)).rawInputs[p.rxInput.val] = true) :
    run (image p).program (Arm.armed (a := a) p generation transfer) (clocks incoming 0 (2*p.Q+3)) =
      sampleInputs (guardFault (image p).program (afterA p generation transfer) ⟨0,0⟩ (checkStart p))
        (clocks incoming 0 (2*p.Q+3)) := by
  have split : 2*p.Q+3 = (2*p.Q+1)+2 := by omega
  rw [split,clocks_add,run_append,prefixA p generation transfer incoming quiet falling]
  simp only [Nat.zero_add,clocks_two]
  have firstSample : (sampleInputs (afterA (a := a) p generation transfer)
      (clocks incoming 0 (2*p.Q+1))).samplerFirst = (incoming (2*p.Q)).rawInputs := by
    change (sampled _ _).samplerFirst = _
    simpa only [Nat.zero_add] using sampled_last (afterA (a := a) p generation transfer) incoming 0 (2*p.Q)
  have guardStep := guard_failure (image p).program
    (sampleInputs (afterA (a := a) p generation transfer) (clocks incoming 0 (2*p.Q+1)))
    ⟨0,0⟩ (checkStart p) (incoming (2*p.Q+1)) (incoming (2*p.Q+1+1)) (quiet _) (quiet _)
    (by simp [sampleInputs_pair,afterA,pulseFinish])
    (by rw [sampleInputs_pc]; change (image p).program.fetch 3 = _; rw [source_fetch p 3 (by decide)]; rfl)
    rfl (by rw [checkStart_matches,firstSample,startHigh]; rfl)
    (by simp [sampleInputs_pair,afterA,pulseFinish,startExit,Arm.armed])
  rw [guardStep,guardFault_samples,← FrameData.sampleInputs_append]

def afterB (p : Profile) (generation transfer : BitVec 16) : State a :=
  pulseFinish (afterStart p generation transfer) (pulseB p)

theorem prefixB {a : Nat} (p : Profile) (generation transfer : BitVec 16) (incoming : Nat → Input)
    (quiet : ∀ n,Quiet (incoming n))
    (falling : (incoming 0).rawInputs[p.rxInput.val] = false)
    (startLow : (incoming (2*p.Q)).rawInputs[p.rxInput.val] = false) :
    run (image p).program (Arm.armed (a := a) p generation transfer) (clocks incoming 0 (4*p.Q+2)) =
      sampleInputs (afterB p generation transfer) (clocks incoming 0 (4*p.Q+2)) := by
  have q := p.Q_ge4
  have split : 4*p.Q+2 = (2*p.Q+3)+((pulseB p).lowDuration.val+(pulseB p).highDuration.val+4) := by
    simp only [pulseB]
    omega
  rw [split,clocks_add,run_append,prefixStart p generation transfer incoming quiet falling startLow]
  have pulse := pulse_run (image p).program
    (sampleInputs (afterStart (a := a) p generation transfer) (clocks incoming 0 (2*p.Q+3))) (pulseB p)
    (clocks incoming (0+(2*p.Q+3)) ((pulseB p).lowDuration.val+(pulseB p).highDuration.val+4))
    (by simp [sampleInputs_pair,afterStart,guardExit])
    (by rw [sampleInputs_pc]; change (image p).program.fetch 4 = _; rw [source_fetch p 4 (by decide)]; rfl)
    (clocks_quiet incoming quiet _ _) (clocks_length _ _ _)
  rw [pulse,pulseFinish_samples,pulseFinish_samples,← FrameData.sampleInputs_append]
  rfl

theorem prelude {a : Nat} (p : Profile) (generation transfer : BitVec 16) (incoming : Nat → Input)
    (quiet : ∀ n,Quiet (incoming n))
    (falling : (incoming 0).rawInputs[p.rxInput.val] = false)
    (startLow : (incoming (2*p.Q)).rawInputs[p.rxInput.val] = false) :
    run (image p).program (Arm.armed (a := a) p generation transfer) (clocks incoming 0 (4*p.Q+3)) =
      sampleInputs (dataBase p generation transfer) (clocks incoming 0 (4*p.Q+3)) := by
  have split : 4*p.Q+3 = (4*p.Q+2)+1 := by omega
  rw [split,clocks_add,run_append,prefixB p generation transfer incoming quiet falling startLow]
  simp only [Nat.zero_add,clocks_one]
  change step (image p).program (incoming (4*p.Q+2))
    (sampleInputs (afterB p generation transfer) (clocks incoming 0 (4*p.Q+2))) = _
  rw [stream_fetch p _ _ (quiet _) (by simp [sampleInputs_pair,afterB,pulseFinish])
    (by simp [sampleInputs_pair,afterB,pulseFinish,afterStart,guardExit,afterA,startExit,Arm.armed])
    (by simp [sampleInputs_pair,afterB,pulseFinish,afterStart,guardExit,afterA,startExit,Arm.armed])]
  simp [sampleInputs_pair,dataBase,afterB,pulseFinish,afterStart,guardExit,afterA,startExit,
    Arm.armed,State.sample]

end Pinwheel.Program.StreamingUART.FramePrelude
