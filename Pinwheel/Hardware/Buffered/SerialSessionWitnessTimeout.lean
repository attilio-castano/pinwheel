import Pinwheel.Hardware.Buffered.SerialStartAdmission

/-! A nonempty I²C session witness uses a physically stuck-low sampled bus.
The initial bounded bus-free qualification must time out, even when START
inherits an arbitrary older second sampler. This is a diagnostic outcome. -/
namespace Pinwheel.Hardware.Buffered.SerialSessionWitness
open Pinwheel.Hardware Pinwheel.Program Pinwheel.Engine.Reactive
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

def initialQualify : Program.Buffered.Instruction :=
  {operation := .qualify ⟨⟨0, 0⟩, ⟨3, 3⟩, 3, 31⟩}

theorem fetch_zero : I2cSource.source.fetch 0 = some initialQualify := rfl

def qualifying (e : Transfer.Execution) (epoch nextSequence : Nat) (sample : BitVec 2) :
    Program.Buffered.State :=
  {core := ⟨.qualifying 0 3 31, ⟨0, 0⟩, Vector.replicate 16 false⟩
   buffers := ⟨epoch, nextSequence, .running e⟩
   owner := e.request.identity
   samplerFirst := 0
   samplerSecond := sample}

def stalled (e : Transfer.Execution) (epoch nextSequence : Nat) (remaining wait : Fin 256) :
    Program.Buffered.State :=
  {qualifying e epoch nextSequence 0 with core := ⟨.qualifying 0 remaining wait,
    ⟨0, 0⟩, Vector.replicate 16 false⟩}

theorem stalled_step (e : Transfer.Execution) (epoch nextSequence : Nat)
    (remaining wait : Fin 256) (positive : 0 < wait.val) :
    Program.Buffered.advance I2cSource.source Refinement.capacity (stalled e epoch nextSequence remaining wait) 0 =
      stalled e epoch nextSequence 3 ⟨wait.val-1, by omega⟩ := by
  simp [Program.Buffered.advance, stalled, qualifying, Program.Buffered.owned, busy,
    Program.Buffered.lower, fetch_zero, initialQualify, Program.Buffered.normalize,
    Program.Buffered.keepPins, Fetch.advance, Check.ready, Program.Buffered.entryTarget,
    Program.Buffered.settle, positive]
  done

def zeroRun (s : Program.Buffered.State) (n : Nat) : Program.Buffered.State :=
  Program.Buffered.run I2cSource.source Refinement.capacity s (fun _ => 0) n

theorem zeroRun_first (s : Program.Buffered.State) (n : Nat) :
    zeroRun s (n+1) = zeroRun (Program.Buffered.advance I2cSource.source Refinement.capacity s 0) n := by
  induction n
  case zero => rfl
  case succ n ih =>
    change Program.Buffered.advance _ _ (zeroRun s (n+1)) 0 =
      Program.Buffered.advance _ _ (zeroRun (Program.Buffered.advance _ _ s 0) n) 0
    rw [ih]
  done

theorem zeroRun_add (s : Program.Buffered.State) (a b : Nat) :
    zeroRun s (a+b) = zeroRun (zeroRun s a) b := by
  induction b
  case zero => rfl
  case succ b ih =>
    change Program.Buffered.advance _ _ (zeroRun s (a+b)) 0 =
      Program.Buffered.advance _ _ (zeroRun (zeroRun s a) b) 0
    rw [ih]
  done

theorem zeroRun_stopped (s : Program.Buffered.State) (reason : Stop) (n : Nat)
    (control : s.core.control = .stopped reason) : zeroRun s n = s := by
  induction n
  case zero => rfl
  case succ n ih =>
    change Program.Buffered.advance _ _ (zeroRun s n) 0 = _
    rw [ih]
    exact SpiInterpreter.advance_stopped _ _ s reason control 0
  done

theorem stalled_terminal (e : Transfer.Execution) (epoch nextSequence : Nat) (remaining : Fin 256) :
    (Program.Buffered.advance I2cSource.source Refinement.capacity
      (stalled e epoch nextSequence remaining 0) 0).core.control = .stopped .timeout := by
  simp [Program.Buffered.advance, stalled, qualifying, Program.Buffered.owned, busy,
    Program.Buffered.lower, fetch_zero, initialQualify, Program.Buffered.normalize,
    Program.Buffered.keepPins, Fetch.advance, Check.ready, Program.Buffered.entryTarget,
    Program.Buffered.settle, Program.Buffered.terminal, Fetch.stop]
  done

theorem stalled_timeout (e : Transfer.Execution) (epoch nextSequence : Nat)
    (wait : Nat) (bound : wait < 256) (remaining : Fin 256) :
    (zeroRun (stalled e epoch nextSequence remaining ⟨wait, bound⟩) (wait+1)).core.control = .stopped .timeout := by
  induction wait generalizing remaining
  case zero => exact stalled_terminal e epoch nextSequence remaining
  case succ n ih =>
    rw [zeroRun_first, stalled_step e epoch nextSequence remaining ⟨n+1, bound⟩ (by simp)]
    exact ih (by omega) 3
  done

theorem stalled_timeout_after (e : Transfer.Execution) (epoch nextSequence : Nat)
    (wait extra : Nat) (bound : wait < 256) (remaining : Fin 256) :
    (zeroRun (stalled e epoch nextSequence remaining ⟨wait, bound⟩) (wait+1+extra)).core.control = .stopped .timeout := by
  rw [zeroRun_add, zeroRun_stopped _ .timeout extra (stalled_timeout e epoch nextSequence wait bound remaining)]
  exact stalled_timeout e epoch nextSequence wait bound remaining
  done

theorem qualify_two (e : Transfer.Execution) (epoch nextSequence : Nat) (sample : BitVec 2) :
    zeroRun (qualifying e epoch nextSequence sample) 2 =
      stalled e epoch nextSequence 3 (if sample = 3#2 then 30 else 29) := by
  have cases : sample = 0#2 ∨ sample = 1#2 ∨ sample = 2#2 ∨ sample = 3#2 := by bv_omega
  rcases cases with sample | sample | sample | sample
  all_goals subst sample
  all_goals simp [zeroRun, Program.Buffered.run, Program.Buffered.advance, stalled, qualifying,
    Program.Buffered.owned, busy, Program.Buffered.lower, fetch_zero, initialQualify,
    Program.Buffered.normalize, Program.Buffered.keepPins, Fetch.advance,
    Check.ready, Program.Buffered.entryTarget, Program.Buffered.settle,
    show (31 : Fin 256).val = 31 from rfl, show (3 : Fin 256).val = 3 from rfl]
  all_goals rfl
  all_goals done

theorem qualify_timeout (e : Transfer.Execution) (epoch nextSequence : Nat) (sample : BitVec 2) :
    (Program.Buffered.run I2cSource.source Refinement.capacity
      (qualifying e epoch nextSequence sample) (fun _ => 0) 34).core.control = .stopped .timeout := by
  change (zeroRun (qualifying e epoch nextSequence sample) (2+32)).core.control = _
  rw [zeroRun_add, qualify_two]
  by_cases good : sample = 3#2
  · rw [if_pos good]
    exact stalled_timeout_after e epoch nextSequence 30 1 (by decide) 3
  · rw [if_neg good]
    exact stalled_timeout_after e epoch nextSequence 29 2 (by decide) 3
  done

theorem started_qualifying (r : Values Reactive.Register) (i : Values Reactive.Input)
    (raw : i .rawInputs = 0) :
    GenericStart.started I2cSource.source r i =
      qualifying ⟨GenericStart.request r i, 0, []⟩ 0 ((r .transfer).toNat + 2) (r .stage1) := by
  simp [GenericStart.started, GenericStart.seed, GenericStart.resample,
    Program.Buffered.start, Program.Buffered.owned, Program.Buffered.lower,
    Fetch.start, Fetch.enter, fetch_zero, initialQualify, Program.Buffered.normalize,
    Program.Buffered.keepPins, Program.Buffered.entryEffects, Program.Buffered.settle,
    qualifying, raw]
  done

theorem started_timeout (r : Values Reactive.Register) (i : Values Reactive.Input)
    (raw : i .rawInputs = 0) :
    (zeroRun (GenericStart.started I2cSource.source r i) 34).core.control = .stopped .timeout := by
  rw [started_qualifying r i raw]
  exact qualify_timeout _ _ _ _
  done

theorem zeroRun_timeout_after (r : Values Reactive.Register) (i : Values Reactive.Input)
    (raw : i .rawInputs = 0) (n : Nat) (enough : 34 ≤ n) :
    (zeroRun (GenericStart.started I2cSource.source r i) n).core.control = .stopped .timeout := by
  have count : n = 34 + (n-34) := by omega
  rw [count, zeroRun_add, zeroRun_stopped _ .timeout (n-34) (started_timeout r i raw)]
  exact started_timeout r i raw
  done

theorem sourceRun_zero (source : Program.Buffered.State) (pins : List SerialPackage.Pins)
    (raw : ∀ pin ∈ pins, pin.rawInputs = 0) :
    SerialSourceRead.sourceRun I2cSource.source source pins = zeroRun source pins.length := by
  induction pins generalizing source
  case nil => rfl
  case cons pin rest ih =>
    change SerialSourceRead.sourceRun _
      (Program.Buffered.advance _ _ source pin.rawInputs) rest = zeroRun source (rest.length+1)
    rw [raw pin (by simp), ih _ (fun p member => raw p (List.mem_cons_of_mem _ member)), zeroRun_first]
  done

theorem sourceAfter_timeout {before} (transaction : SerialWire.Transaction before)
    (dispatch : transaction.dispatch.rawInputs = 0) (capture : transaction.capture.rawInputs = 0)
    (read : ∀ pin ∈ transaction.read.pins, pin.rawInputs = 0) (enough : 33 ≤ transaction.read.pins.length) :
    (SerialStartAdmission.sourceAfter I2cSource.source transaction).core.control = .stopped .timeout := by
  unfold SerialStartAdmission.sourceAfter SerialSourceSession.Delivery.started
  rw [← SerialSourceTransaction.sourceRun_append, sourceRun_zero]
  · apply zeroRun_timeout_after
    · exact dispatch
    · simp only [List.length_append, List.length_singleton]
      omega
  · intro pin member
    rcases List.mem_append.mp member with first | last
    · have equal : pin = transaction.capture := by simpa [SerialStartAdmission.delivery] using first
      exact equal ▸ capture
    · exact read pin last
  done

theorem bitSamples_raw (raw : BitVec 2) (bits : List Bool) :
    ∀ pin ∈ SerialWire.bitSamples raw bits, pin.rawInputs = raw := by
  induction bits
  case nil => simp [SerialWire.bitSamples]
  case cons bit rest ih =>
    intro pin member
    simp only [SerialWire.bitSamples, List.mem_cons] at member
    rcases member with first | second | tail
    · subst pin
      rfl
    · subst pin
      rfl
    · exact ih pin tail
  done

theorem concrete_timeout (before : SerialPackage.State) (available : Serial.Frames.Available before.record)
    (sequence : BitVec 16) (payload : BitVec 32) (tx rx : BitVec 6) :
    (SerialStartAdmission.sourceAfter I2cSource.source
      (SerialStartAdmission.concreteStart before available sequence payload tx rx 0)).core.control = .stopped .timeout := by
  apply sourceAfter_timeout
  · rfl
  · rfl
  · intro pin member
    simp only [SerialStartAdmission.concreteStart, SerialWire.concrete, SerialWire.read,
      SerialWire.Read.pins, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at member
    rcases member with first | middle | last
    · subst pin
      rfl
    · exact bitSamples_raw 0 _ pin middle
    · subst pin
      rfl
  · simp [SerialStartAdmission.concreteStart, SerialWire.concrete, SerialWire.read,
      SerialWire.Read.pins, SerialWire.bitSamples_length]
  done

end Pinwheel.Hardware.Buffered.SerialSessionWitness
