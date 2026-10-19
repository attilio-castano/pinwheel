import Pinwheel.Program.StreamingReadyTiming

/-! Index-preserving input windows for autonomous UART proofs. These windows
contain ordinary source inputs; no capture or terminal event is encoded here. -/
namespace Pinwheel.Program.StreamingUART.FrameSamples
open Pinwheel.Program.StreamingReady

def clocks (incoming : Nat → Input) (offset edges : Nat) : List Input :=
  (List.range edges).map (fun n => incoming (offset+n))

theorem clocks_length (incoming : Nat → Input) (offset edges : Nat) :
    (clocks incoming offset edges).length = edges := by simp [clocks]

theorem clocks_add (incoming : Nat → Input) (offset first second : Nat) :
    clocks incoming offset (first+second) =
      clocks incoming offset first ++ clocks incoming (offset+first) second := by
  simp [clocks,List.range_add,List.map_map,Function.comp_def,Nat.add_assoc]


theorem clocks_zero (incoming : Nat → Input) (offset : Nat) : clocks incoming offset 0 = [] := rfl

theorem clocks_one (incoming : Nat → Input) (offset : Nat) :
    clocks incoming offset 1 = [incoming offset] := by simp [clocks]

theorem clocks_two (incoming : Nat → Input) (offset : Nat) :
    clocks incoming offset 2 = [incoming offset,incoming (offset+1)] := by simp [clocks,List.range_succ]

theorem clocks_layout (incoming : Nat → Input) (offset low high : Nat) :
    clocks incoming offset (low+high+3) =
      [incoming offset] ++ clocks incoming (offset+1) low ++ [incoming (offset+low+1)] ++
        clocks incoming (offset+low+2) high ++ [incoming (offset+low+high+2)] := by
  have total : low+high+3 = (((1+low)+1)+high)+1 := by omega
  rw [total,clocks_add,clocks_add,clocks_add,clocks_add]
  simp only [clocks_one]
  simp only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

/-- Exact causal samples at an indexed cut, with arbitrary initial synchronizers. -/
theorem run_samples (p : Program) (s : State a) (incoming : Nat → Input) (offset edges : Nat)
    (runtime : ∀ n, (incoming n).Runtime) :
    (run p s (clocks incoming offset (edges+2))).samplerFirst = (incoming (offset+edges+1)).rawInputs ∧
      (run p s (clocks incoming offset (edges+2))).samplerSecond = (incoming (offset+edges)).rawInputs := by
  rw [clocks_add,clocks_two]
  exact run_two_samples p s _ _ _ (runtime _) (runtime _)

def sampled (s : State a) (inputs : List Input) : State a :=
  inputs.foldl (fun state input => state.sample input.rawInputs) s

theorem sampled_append (s : State a) (first second : List Input) :
    sampled s (first++second) = sampled (sampled s first) second := List.foldl_append

theorem sampled_window (s : State a) (incoming : Nat → Input) (offset edges : Nat) :
    sampled s (clocks incoming offset (edges+2)) =
      {(sampled s (clocks incoming offset edges)) with
        samplerFirst := (incoming (offset+edges+1)).rawInputs
        samplerSecond := (incoming (offset+edges)).rawInputs} := by
  rw [clocks_add,clocks_two,sampled_append]
  rfl

theorem sampled_last (s : State a) (incoming : Nat → Input) (offset edges : Nat) :
    (sampled s (clocks incoming offset (edges+1))).samplerFirst =
      (incoming (offset+edges)).rawInputs := by
  rw [clocks_add,clocks_one,sampled_append]
  rfl

end Pinwheel.Program.StreamingUART.FrameSamples
