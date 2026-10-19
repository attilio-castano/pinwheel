import Pinwheel.Program.StreamingUARTFrameCell
import Pinwheel.Program.StreamingPacking

namespace Pinwheel.Program.StreamingUART.FrameData
open Pinwheel.Program.StreamingReady
open QuietTiming FrameCell FrameSamples
open Pinwheel.Program.Streaming.Packing

def bits (payload : BitVec 8) : List Bool := List.ofFn (fun k : Fin 8 => payload[k.val])

theorem bits_length (payload : BitVec 8) : (bits payload).length = 8 := List.length_ofFn

theorem prefix_succ (payload : BitVec 8) (k : Nat) (within : k < 8) :
    rxWord ((bits payload).take (k+1)) =
      (rxWord ((bits payload).take k) <<< 1) |||
        BitVec.ofNat 32 (if payload[k] then 1 else 0) := by
  rw [List.take_succ_eq_append_getElem (by simpa only [bits_length] using within),rxWord_append]
  simp only [bits,List.getElem_ofFn]

def bytePrefix (s : State a) (payload : BitVec 8) (k : Nat) : State a :=
  {s with
    phase := if k = 8 then .fetch else .boundary
    pc := if k = 8 then s.pc+1 else s.pc
    remaining := BitVec.ofNat 16 (8-k)
    countdown := 0
    cellBit := false
    pins := ⟨0,0⟩
    rxPartial := if k = 8 then 0 else rxWord ((bits payload).take k)
    rxUsed := if k = 8 then 0 else BitVec.ofNat 6 k
    rxProduced := BitVec.ofNat 16 k
    rx := if k = 8 then (Streaming.Queue.empty a).tick
      (some ⟨rxWord (bits payload),⟨7,by decide⟩⟩) false else Streaming.Queue.empty a}

theorem bytePrefix_zero (s : State a) (payload : BitVec 8)
    (phase : s.phase = .boundary) (remaining : s.remaining = 8#16)
    (countdown : s.countdown = 0#8) (cellBit : s.cellBit = false)
    (pins : s.pins = ⟨0,0⟩) (rxPartial : s.rxPartial = 0#32)
    (rxUsed : s.rxUsed = 0#6) (rxProduced : s.rxProduced = 0#16)
    (rx : s.rx = Streaming.Queue.empty a) : bytePrefix s payload 0 = s := by
  cases s
  simp_all [bytePrefix]

private theorem queue_idle (q : Queue a) : q.tick none false = q := by cases q; rfl

theorem bytePrefix_succ (s : State a) (payload : BitVec 8) (k : Nat) (within : k < 8) :
    cellExit (bytePrefix s payload k) payload[k] = bytePrefix s payload (k+1) := by
  have next := prefix_succ payload k within
  have full : (bits payload).take 8 = bits payload := by
    simpa only [bits_length] using List.take_length (l := bits payload)
  have casesK : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 := by omega
  rcases casesK with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp only [cellExit,captured,bytePrefix] <;> simp [queue_idle]
  all_goals first | simpa using next.symm | rw [← next,full]

theorem cellExit_samples (s : State a) (inputs : List Input) (bit : Bool) :
    cellExit (sampleInputs s inputs) bit = sampleInputs (cellExit s bit) inputs := by
  simp [cellExit,captured,sampleInputs_pair]

theorem sampleInputs_append (s : State a) (before after : List Input) :
    sampleInputs s (before ++ after) = sampleInputs (sampleInputs s before) after :=
  List.foldl_append

/-- The eight receive iterations are autonomous. The premise constrains raw
sample instants only; the observed RX word is derived from the machine steps. -/
theorem data_prefix (p : Profile) (s : State a) (payload : BitVec 8)
    (incoming : Nat → Input) (offset k : Nat) (within : k ≤ 8)
    (current : s.current = .stream (cell p) none) (quiet : ∀ n,Quiet (incoming n))
    (samples : ∀ (j : Nat) (bound : j < 8),
      (incoming (offset+(4*p.Q)*j+2*p.Q-3)).rawInputs[p.rxInput.val] = payload[j]'bound) :
    run (image p).program (bytePrefix s payload 0) (clocks incoming offset ((4*p.Q)*k)) =
      sampleInputs (bytePrefix s payload k) (clocks incoming offset ((4*p.Q)*k)) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have bound : k < 8 := by omega
    have notLast : k ≠ 8 := by omega
    have before := ih (by omega) samples
    rw [Nat.mul_succ,clocks_add,run_append,before]
    have cellStep := rx_cell_clocks p
      (sampleInputs (bytePrefix s payload k) (clocks incoming offset ((4*p.Q)*k)))
      incoming (offset+(4*p.Q)*k)
      (by simp [sampleInputs_pair,bytePrefix,notLast])
      (by simpa [sampleInputs_pair,bytePrefix] using current)
      (by simp [sampleInputs_pair,bytePrefix,notLast,Streaming.Queue.empty,Streaming.Queue.writable,Streaming.queueDepth_positive])
      (by
        simp only [sampleInputs_rxUsed,bytePrefix,if_neg notLast]
        intro equal
        have natural := congrArg BitVec.toNat equal
        simp only [BitVec.toNat_ofNat] at natural
        have small : k % 64 = k := Nat.mod_eq_of_lt (by omega)
        omega) quiet
    rw [cellStep,samples k bound,cellExit_samples,bytePrefix_succ s payload k bound,
      ← sampleInputs_append]

end Pinwheel.Program.StreamingUART.FrameData
