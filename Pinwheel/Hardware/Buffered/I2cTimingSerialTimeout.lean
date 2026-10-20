import Pinwheel.Hardware.Buffered.I2cTimingLogicalWireInitialized
import Pinwheel.Hardware.Buffered.SerialSessionWitnessTimeout

/-! A diagnostic witness for every timing pair: the actual request flushes the
input sampler with raw zero, then the initial bus-free qualification times out
within budget+1 clocks. It does not assume a successful I²C peer. -/
namespace Pinwheel.Hardware.Buffered.I2cTiming.SerialWitness
open Pinwheel.Hardware Pinwheel.Program Pinwheel.Engine.Reactive
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

def initialQualify (duration budget : Fin 256) : Program.Buffered.Instruction :=
  {operation := .qualify ⟨⟨0,0⟩,⟨3,3⟩,duration,budget⟩}

theorem fetch_zero (duration budget : Fin 256) :
    (source duration budget).fetch 0 = some (initialQualify duration budget) := rfl

def qualifying (duration budget : Fin 256) (e : Transfer.Execution) (epoch nextSequence : Nat) :
    Program.Buffered.State :=
  {core := ⟨.qualifying 0 duration budget,⟨0,0⟩,Vector.replicate 16 false⟩
   buffers := ⟨epoch,nextSequence,.running e⟩
   owner := e.request.identity
   samplerFirst := 0
   samplerSecond := 0}

def stalled (duration budget : Fin 256) (e : Transfer.Execution) (epoch nextSequence : Nat)
    (remaining wait : Fin 256) : Program.Buffered.State :=
  {qualifying duration budget e epoch nextSequence with core :=
    ⟨.qualifying 0 remaining wait,⟨0,0⟩,Vector.replicate 16 false⟩}

theorem stalled_step (duration budget : Fin 256) (e : Transfer.Execution) (epoch nextSequence : Nat)
    (remaining wait : Fin 256) (positive : 0 < wait.val) :
    Program.Buffered.advance (source duration budget) Refinement.capacity
      (stalled duration budget e epoch nextSequence remaining wait) 0 =
      stalled duration budget e epoch nextSequence duration ⟨wait.val-1,by omega⟩ := by
  simp [Program.Buffered.advance,stalled,qualifying,Program.Buffered.owned,busy,
    Program.Buffered.lower,fetch_zero,initialQualify,Program.Buffered.normalize,
    Program.Buffered.keepPins,Fetch.advance,Check.ready,Program.Buffered.entryTarget,
    Program.Buffered.settle,positive]

def zeroRun (duration budget : Fin 256) (s : Program.Buffered.State) (n : Nat) : Program.Buffered.State :=
  Program.Buffered.run (source duration budget) Refinement.capacity s (fun _ => 0) n

theorem zeroRun_first (duration budget : Fin 256) (s : Program.Buffered.State) (n : Nat) :
    zeroRun duration budget s (n+1) = zeroRun duration budget
      (Program.Buffered.advance (source duration budget) Refinement.capacity s 0) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change Program.Buffered.advance _ _ (zeroRun duration budget s (n+1)) 0 =
      Program.Buffered.advance _ _
        (zeroRun duration budget (Program.Buffered.advance _ _ s 0) n) 0
    rw [ih]

theorem stalled_terminal (duration budget : Fin 256) (e : Transfer.Execution) (epoch nextSequence : Nat)
    (remaining : Fin 256) :
    (Program.Buffered.advance (source duration budget) Refinement.capacity
      (stalled duration budget e epoch nextSequence remaining 0) 0).core.control = .stopped .timeout := by
  simp [Program.Buffered.advance,stalled,qualifying,Program.Buffered.owned,busy,
    Program.Buffered.lower,fetch_zero,initialQualify,Program.Buffered.normalize,
    Program.Buffered.keepPins,Fetch.advance,Check.ready,Program.Buffered.entryTarget,
    Program.Buffered.settle,Program.Buffered.terminal,Fetch.stop]

theorem stalled_timeout (duration budget : Fin 256) (e : Transfer.Execution) (epoch nextSequence : Nat)
    (wait : Nat) (bound : wait < 256) (remaining : Fin 256) :
    (zeroRun duration budget (stalled duration budget e epoch nextSequence remaining ⟨wait,bound⟩)
      (wait+1)).core.control = .stopped .timeout := by
  induction wait generalizing remaining with
  | zero => exact stalled_terminal duration budget e epoch nextSequence remaining
  | succ n ih =>
    rw [zeroRun_first,stalled_step duration budget e epoch nextSequence remaining ⟨n+1,bound⟩ (by simp)]
    exact ih (by omega) duration

theorem zeroRun_add (duration budget : Fin 256) (s : Program.Buffered.State) (a b : Nat) :
    zeroRun duration budget s (a+b) = zeroRun duration budget (zeroRun duration budget s a) b := by
  induction b with
  | zero => rfl
  | succ b ih =>
    change Program.Buffered.advance _ _ (zeroRun duration budget s (a+b)) 0 =
      Program.Buffered.advance _ _ (zeroRun duration budget (zeroRun duration budget s a) b) 0
    rw [ih]

theorem zeroRun_stopped (duration budget : Fin 256) (s : Program.Buffered.State)
    (reason : Stop) (n : Nat) (control : s.core.control = .stopped reason) :
    zeroRun duration budget s n = s := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change Program.Buffered.advance _ _ (zeroRun duration budget s n) 0 = _
    rw [ih]
    exact SpiInterpreter.advance_stopped _ _ s reason control 0

theorem qualify_timeout (duration budget : Fin 256) (e : Transfer.Execution) (epoch nextSequence : Nat) :
    (zeroRun duration budget (qualifying duration budget e epoch nextSequence)
      (budget.val+1)).core.control = .stopped .timeout :=
  stalled_timeout duration budget e epoch nextSequence budget.val budget.isLt duration

theorem started_qualifying (duration budget : Fin 256) (r : Values Reactive.Register)
    (i : Values Reactive.Input) (raw : i .rawInputs = 0) (first : r .stage1 = 0) :
    GenericStart.started (source duration budget) r i =
      qualifying duration budget ⟨GenericStart.request r i,0,[]⟩ 0 ((r .transfer).toNat+2) := by
  simp [GenericStart.started,GenericStart.seed,GenericStart.resample,
    Program.Buffered.start,Program.Buffered.owned,Program.Buffered.lower,
    Fetch.start,Fetch.enter,fetch_zero,initialQualify,Program.Buffered.normalize,
    Program.Buffered.keepPins,Program.Buffered.entryEffects,Program.Buffered.settle,
    qualifying,raw,first]

theorem zeroRun_timeout_after (duration budget : Fin 256) (r : Values Reactive.Register)
    (i : Values Reactive.Input) (raw : i .rawInputs = 0) (first : r .stage1 = 0)
    (n : Nat) (enough : budget.val+1 ≤ n) :
    (zeroRun duration budget (GenericStart.started (source duration budget) r i) n).core.control = .stopped .timeout := by
  have count : n = budget.val+1 + (n-(budget.val+1)) := by omega
  rw [started_qualifying duration budget r i raw first,count,zeroRun_add,
    zeroRun_stopped _ _ _ .timeout _ (qualify_timeout duration budget _ _ _)]
  exact qualify_timeout duration budget _ _ _

theorem sourceRun_zero (duration budget : Fin 256) (state : Program.Buffered.State)
    (pins : List SerialPackage.Pins) (raw : ∀ pin ∈ pins, pin.rawInputs = 0) :
    SerialSourceRead.sourceRun (source duration budget) state pins = zeroRun duration budget state pins.length := by
  induction pins generalizing state with
  | nil => rfl
  | cons pin rest ih =>
    change SerialSourceRead.sourceRun _ (Program.Buffered.advance _ _ state pin.rawInputs) rest =
      zeroRun duration budget state (rest.length+1)
    rw [raw pin (by simp),ih _ (fun p member => raw p (List.mem_cons_of_mem _ member)),zeroRun_first]

theorem stage1_zero (s : SramState.State) (i : Values Reactive.Input) (raw : i .rawInputs = 0) :
    (s.step i).core .stage1 = 0 := by
  rw [Lifecycle.scalar_step s i .stage1 trivial]
  simp [Circuit.step,Reactive.circuit,Reactive.next,Expr.eval,Lifecycle.effective_rawInputs,raw]

theorem package_stage1_zero (s : SerialPackage.State) (pin : SerialPackage.Pins)
    (raw : pin.rawInputs = 0) : (s.step pin).controller.core .stage1 = 0 := by
  apply stage1_zero
  exact raw

theorem request_stage1_zero {before} (request : SerialWire.Request before)
    (raw : request.close.rawInputs = 0) : request.framed.controller.core .stage1 = 0 := by
  change (before.run (request.assert :: (request.samples ++ [request.close]))).controller.core .stage1 = 0
  simp only [SerialPackage.State.run,List.foldl_cons,List.foldl_append,List.foldl_nil]
  exact package_stage1_zero _ _ raw

theorem sourceAfter_timeout (duration budget : Fin 256) {before}
    (transaction : SerialWire.Transaction before)
    (dispatch : transaction.dispatch.rawInputs = 0) (capture : transaction.capture.rawInputs = 0)
    (close : transaction.request.close.rawInputs = 0)
    (read : ∀ pin ∈ transaction.read.pins, pin.rawInputs = 0)
    (enough : budget.val ≤ transaction.read.pins.length) :
    (SerialStartAdmission.sourceAfter (source duration budget) transaction).core.control = .stopped .timeout := by
  unfold SerialStartAdmission.sourceAfter SerialSourceSession.Delivery.started
  rw [← SerialSourceTransaction.sourceRun_append,sourceRun_zero]
  · apply zeroRun_timeout_after
    · exact dispatch
    · exact request_stage1_zero transaction.request close
    · simp only [List.length_append,List.length_singleton]
      omega
  · intro pin member
    rcases List.mem_append.mp member with first | last
    · have equal : pin = transaction.capture := by simpa [SerialStartAdmission.delivery] using first
      exact equal ▸ capture
    · exact read pin last

theorem concrete_timeout (duration budget : Fin 256) (before : SerialPackage.State)
    (available : Serial.Frames.Available before.record) (sequence : BitVec 16)
    (payload : BitVec 32) (tx rx : BitVec 6) :
    (SerialStartAdmission.sourceAfter (source duration budget)
      (SerialStartAdmission.concreteStart before available sequence payload tx rx 0)).core.control = .stopped .timeout := by
  apply sourceAfter_timeout
  · rfl
  · rfl
  · rfl
  · intro pin member
    simp only [SerialStartAdmission.concreteStart,SerialWire.concrete,SerialWire.read,
      SerialWire.Read.pins,List.mem_cons,List.mem_append,List.not_mem_nil,or_false] at member
    rcases member with first | middle | last
    · subst pin
      rfl
    · exact SerialSessionWitness.bitSamples_raw 0 _ pin middle
    · subst pin
      rfl
  · have bound := budget.isLt
    simp only [SerialStartAdmission.concreteStart,SerialWire.concrete,SerialWire.read,
      SerialWire.Read.pins,SerialWire.bitSamples_length,List.length_cons,List.length_append,
      List.length_replicate]
    omega

end Pinwheel.Hardware.Buffered.I2cTiming.SerialWitness
