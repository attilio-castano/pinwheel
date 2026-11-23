import Pinwheel.Hardware.Processor.CoreCircuitDatapath
import Pinwheel.Hardware.Processor.RV32I.ExecuteCircuitProofs
import Pinwheel.Hardware.DecodedImplementation

namespace Pinwheel.Hardware.Processor.CoreCircuit
open CoreInterface
set_option backward.isDefEq.respectTransparency false

/-- Every architectural register is the actual physical x1..x31 word; x0 has
no storage. Held instruction and fault metadata are separate control storage. -/
abbrev arch := architecture

def rfValues (s : Values Register) : Values (Hardware.RegisterFile.Register 5 32) :=
  fun r => s (.left r)

def rfPins (i : Values Input) (s : Values Register) : Values (Hardware.RegisterFile.Input 5 32) :=
  fun p => (registerInput p).eval i s

theorem rf_step (i : Values Input) (s : Values Register)
    (r : Hardware.RegisterFile.Register 5 32 b) :
    circuit.step i s (.left r) = (Hardware.RegisterFile.circuit 5 32).step (rfPins i s) (rfValues s) r :=
  Expr.eval_bind registerInput (fun r => .reg (.left r)) ((Hardware.RegisterFile.circuit 5 32).next r) i s

theorem register_step (i : Values Input) (s : Values Register) :
    (arch (circuit.step i s)).registers =
      if i reset = 1 then (fun _ => 0) else
        if writeEnabled.eval i s = 1 then
          RV32I.Semantics.write (arch s).registers (writeRd.eval i s) (writeData.eval i s)
        else (arch s).registers := by
  have h : @rfValues (circuit.step i s) =
      (fun {b} r => (Hardware.RegisterFile.circuit 5 32).step (rfPins i s) (rfValues s) r) := by
    funext b r
    exact rf_step i s r
  change Hardware.RegisterFile.view (rfValues (circuit.step i s)) = _
  rw [h, Hardware.RegisterFile.step_view]
  rfl

/-- Reset clears all 37 actual registers from arbitrary raw states, including
reserved phase7 and dirty inactive instruction/fault metadata. -/
theorem reset_eq (i : Values Input) (s : Values Register) (hr : i reset = 1) (r : Register b) :
    circuit.step i s r = 0 := by
  cases r with
  | left r =>
      rw [rf_step]
      have h := Hardware.RegisterFile.reset_eq (rfPins i s) (rfValues s) hr r
      cases r
      exact h
  | right r =>
      rcases r with ⟨⟨k, hk⟩⟩
      have bound : k < 6 := hk
      match k with
      | 0 | 1 | 2 | 3 | 4 | 5 => simp [Circuit.step, circuit, controlNext, Expr.eval, hr]
      | k+6 => omega

/-- Reconstruct the issued data request from the held instruction and unchanged
architectural state. Invalid phase/instruction combinations are excluded by
`Valid`, rather than interpreted as invented requests. -/
def request (s : Values Register) : Option CoreModel.DataRequest :=
  match RV32I.Semantics.step (arch s) (s instruction) with
  | .pending (.load context op dest address) => some (.load context op dest address)
  | .pending (.store context op address data) => some (.store context op address data)
  | _ => none

def fenceContext (s : Values Register) : Option RV32I.Semantics.Context :=
  match RV32I.Semantics.step (arch s) (s instruction) with
  | .pending (.fence context) => some context
  | _ => none

def decodeCause (code : BitVec 4) (address : BitVec 32) : CoreModel.Cause :=
  match code.toNat with
  | 0 => .fetchMisaligned | 1 => .fetchAccessFault
  | 2 => .instruction .illegalInstruction | 3 => .instruction .environmentCall
  | 4 => .instruction .breakpoint | 5 => .instruction (.instructionAddressMisaligned address)
  | 6 => .instruction (.loadFault .misaligned address) | 7 => .instruction (.loadFault .accessFault address)
  | 8 => .instruction (.storeFault .misaligned address) | 9 => .instruction (.storeFault .accessFault address)
  | _ => .instruction .illegalInstruction

def fault (s : Values Register) : CoreModel.Fault :=
  ⟨s pc, if s faultWordValid = 1 then some (s instruction) else none,
    decodeCause (s faultCause) (s faultAddress)⟩

/-- Inactive IR/fault storage is forgotten. Invalid raw phase encodings have a
specified fallback only to keep the projection total; they are outside Valid. -/
def view (s : Values Register) : CoreModel.State :=
  ⟨arch s,
    if s phase = 0 then .fetchRequest
    else if s phase = 1 then .fetchResponse
    else if s phase = 2 then .execute (s instruction)
    else if s phase = 3 then match request s with | some q => .dataRequest q | none => .fetchRequest
    else if s phase = 4 then match request s with | some q => .dataResponse q | none => .fetchRequest
    else if s phase = 5 then match fenceContext s with | some c => .fence c | none => .fetchRequest
    else .terminal (fault s)⟩

/-- A representation relation permits retained inactive metadata while making
pending instruction/operand provenance and terminal fields explicit. -/
def Represents (raw : Values Register) (state : CoreModel.State) : Prop :=
  arch raw = state.arch ∧ match state.phase with
  | .fetchRequest => raw phase = 0
  | .fetchResponse => raw phase = 1
  | .execute w => raw phase = 2 ∧ raw instruction = w
  | .dataRequest q => raw phase = 3 ∧ q.context.state = state.arch ∧
      q.context.word = raw instruction ∧ q.pending.Issued
  | .dataResponse q => raw phase = 4 ∧ q.context.state = state.arch ∧
      q.context.word = raw instruction ∧ q.pending.Issued
  | .fence c => raw phase = 5 ∧ c.state = state.arch ∧ c.word = raw instruction ∧
      (RV32I.Semantics.Pending.fence c).Issued
  | .terminal f => raw phase = 6 ∧ f.pc = state.arch.pc ∧ raw faultCause = causeCode f.cause ∧
      raw faultAddress = CoreInterface.faultAddress f ∧ raw faultWordValid = BitVec.ofBool f.word.isSome ∧
      (∀ w, f.word = some w → raw instruction = w)

def Valid (raw : Values Register) : Prop :=
  ∃ state, CoreModel.Valid state ∧ Represents raw state

theorem issued_step (p : RV32I.Semantics.Pending) (h : p.Issued) :
    RV32I.Semantics.step p.context.state p.context.word = .pending p := by
  rw [RV32I.Semantics.step_decoded _ _ _ p.context.decoded]
  exact h

theorem represented_request (raw : Values Register) (state : CoreModel.State) (q : CoreModel.DataRequest)
    (ha : arch raw = state.arch) (hs : q.context.state = state.arch)
    (hw : q.context.word = raw instruction) (hi : q.pending.Issued) : request raw = some q := by
  have h := issued_step q.pending hi
  change RV32I.Semantics.step q.context.state q.context.word = .pending q.pending at h
  rw [hs, hw, ← ha] at h
  unfold request
  rw [h]
  cases q <;> rfl

theorem represented_fence (raw : Values Register) (state : CoreModel.State) (c : RV32I.Semantics.Context)
    (ha : arch raw = state.arch) (hs : c.state = state.arch)
    (hw : c.word = raw instruction) (hi : (RV32I.Semantics.Pending.fence c).Issued) :
    fenceContext raw = some c := by
  have h := issued_step (.fence c) hi
  change RV32I.Semantics.step c.state c.word = .pending (.fence c) at h
  rw [hs, hw, ← ha] at h
  simp [fenceContext, h]

theorem decode_cause (f : CoreModel.Fault) : decodeCause (causeCode f.cause) (CoreInterface.faultAddress f) = f.cause := by
  rcases f with ⟨pc, w, cause⟩
  cases cause with
  | fetchMisaligned => rfl
  | fetchAccessFault => rfl
  | instruction trap => cases trap <;> try rfl
                        all_goals rename_i reason address
                        all_goals cases reason <;> rfl

theorem represented_fault (raw : Values Register) (f : CoreModel.Fault)
    (hp : f.pc = (arch raw).pc) (hc : raw faultCause = causeCode f.cause)
    (ha : raw faultAddress = CoreInterface.faultAddress f)
    (hv : raw faultWordValid = BitVec.ofBool f.word.isSome)
    (hw : ∀ w, f.word = some w → raw instruction = w) : fault raw = f := by
  unfold fault
  simp only [hc, ha, decode_cause]
  rcases f with ⟨p, w, c⟩
  cases w with
  | none => simp_all [arch, architecture]
  | some w => simp_all [arch, architecture]

theorem view_of_represents (raw : Values Register) (state : CoreModel.State)
    (h : Represents raw state) : view raw = state := by
  rcases state with ⟨a, p⟩
  rcases h with ⟨ha, hp⟩
  dsimp only at ha hp
  subst a
  cases p with
  | fetchRequest => simp [view, hp]
  | fetchResponse => simp [view, hp]
  | execute w => rcases hp with ⟨hp, hw⟩; simp [view, hp, hw]
  | dataRequest q =>
      rcases hp with ⟨hp, hs, hw, hi⟩
      have hq := represented_request raw ⟨arch raw, .dataRequest q⟩ q rfl hs hw hi
      simp [view, hp, hq]
  | dataResponse q =>
      rcases hp with ⟨hp, hs, hw, hi⟩
      have hq := represented_request raw ⟨arch raw, .dataResponse q⟩ q rfl hs hw hi
      simp [view, hp, hq]
  | fence c =>
      rcases hp with ⟨hp, hs, hw, hi⟩
      have hf := represented_fence raw ⟨arch raw, .fence c⟩ c rfl hs hw hi
      simp [view, hp, hf]
  | terminal f =>
      rcases hp with ⟨hp, hpc, hc, ha, hv, hw⟩
      have hf := represented_fault raw f hpc hc ha hv hw
      simp [view, hp, hf]

theorem valid_model (raw : Values Register) (h : Valid raw) : CoreModel.Valid (view raw) := by
  obtain ⟨state, hv, hr⟩ := h
  rw [view_of_represents raw state hr]
  exact hv

def zeroValues : Values Register := fun _ => 0

theorem zero_represents : Represents zeroValues CoreModel.initial := by
  constructor
  · rfl
  · rfl

theorem zero_valid : Valid zeroValues := ⟨CoreModel.initial, CoreModel.initial_valid, zero_represents⟩

theorem zero_view : view zeroValues = CoreModel.initial := view_of_represents _ _ zero_represents

theorem reset_values (i : Values Input) (s : Values Register) (hr : i reset = 1) :
    (fun {_b} r => circuit.step i s r) = @zeroValues := by
  funext _b r
  exact reset_eq i s hr r

theorem reset_view (i : Values Input) (s : Values Register) (hr : i reset = 1) :
    view (circuit.step i s) = CoreModel.initial := by
  rw [reset_values i s hr]
  exact zero_view

@[simp] theorem both_eval (x y : E 1) (i : Values Input) (s : Values Register) :
    (both x y).eval i s = x.eval i s &&& y.eval i s := rfl

@[simp] theorem either_eval (x y : E 1) (i : Values Input) (s : Values Register) :
    (either x y).eval i s = x.eval i s ||| y.eval i s := WordOps.wordOr_eval x y i s

@[simp] theorem gated_eval (enable : E 1) (value : E b) (i : Values Input) (s : Values Register) :
    (gated enable value).eval i s = if enable.eval i s = 1 then value.eval i s else 0 := rfl

@[simp] theorem step_phase (i : Values Input) (s : Values Register) :
    circuit.step i s phase = if i reset = 1 then 0 else nextPhase.eval i s := by
  simp only [Circuit.step, circuit, phase, controlNext, Expr.eval]

@[simp] theorem step_pc (i : Values Input) (s : Values Register) :
    circuit.step i s pc = if i reset = 1 then 0 else if retiring.eval i s = 1 then nextPC.eval i s else s pc := by
  simp only [Circuit.step, circuit, pc, controlNext, Expr.eval]

@[simp] theorem step_instruction (i : Values Input) (s : Values Register) :
    circuit.step i s instruction = if i reset = 1 then 0 else
      if ((inPhase 1).eval i s &&& (i fetchResponseValid &&& ~~~i fetchResponseFault)) = 1 then
        i fetchResponseData else s instruction := by
  simp only [Circuit.step, circuit, instruction, controlNext, both, Expr.eval]

@[simp] theorem step_cause (i : Values Input) (s : Values Register) :
    circuit.step i s faultCause = if i reset = 1 then 0 else
      if trapping.eval i s = 1 then newCause.eval i s else s faultCause := by
  simp only [Circuit.step, circuit, faultCause, controlNext, Expr.eval]

@[simp] theorem step_address (i : Values Input) (s : Values Register) :
    circuit.step i s faultAddress = if i reset = 1 then 0 else
      if trapping.eval i s = 1 then newFaultAddress.eval i s else s faultAddress := by
  simp only [Circuit.step, circuit, faultAddress, controlNext, Expr.eval]

@[simp] theorem step_wordValid (i : Values Input) (s : Values Register) :
    circuit.step i s faultWordValid = if i reset = 1 then 0 else
      if trapping.eval i s = 1 then trapHasWord.eval i s else s faultWordValid := by
  simp only [Circuit.step, circuit, faultWordValid, controlNext, Expr.eval]

/-- The architectural part of a raw next state contains exactly the register
file update and the selected commit PC. -/
theorem arch_step (i : Values Input) (s : Values Register) :
    arch (circuit.step i s) =
      ⟨if i reset = 1 then 0 else if retiring.eval i s = 1 then nextPC.eval i s else s pc,
       if i reset = 1 then (fun _ => 0) else
         if writeEnabled.eval i s = 1 then
           RV32I.Semantics.write (arch s).registers (writeRd.eval i s) (writeData.eval i s)
         else (arch s).registers⟩ := by
  have h := register_step i s
  change RV32I.Semantics.State.mk _ ((arch (circuit.step i s)).registers) = _
  simp only [h, step_pc]

theorem pcAligned_eval (i : Values Input) (s : Values Register) :
    pcAligned.eval i s = BitVec.ofBool (decide (CoreModel.aligned (arch s))) := by
  simp [pcAligned, Expr.eval, RV32I.ExecuteCircuit.low_two_zero, CoreModel.aligned, arch, architecture]

theorem reset_output_eq (i : Values Input) (raw : Values Register) (state : CoreModel.State)
    (hr : i reset = 1) (o : Output b) :
    circuit.observe i raw o = CoreInterface.outputValues i state o := by
  rcases o with ⟨⟨k, hk⟩⟩
  have bound : k < 30 := hk
  match k with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 |
    15 | 16 | 17 | 18 | 19 | 20 | 21 | 22 | 23 | 24 | 25 | 26 | 27 | 28 | 29 =>
      simp [Circuit.observe, circuit, CoreInterface.outputValues, CoreInterface.eventWrite,
        CoreInterface.retired, CoreInterface.trapped, CoreModel.observe, CoreModel.event, CoreModel.tick,
        CoreInterface.decode, hr, active, executing, dataOffer, dataWaiting, retiring, immediateRetire,
        dataSuccess, dataCompletion, atomicCompletion, deferredCompletion, fenceRetire,
        writeEnabled, writeRd, writeData, trapping, fetchMisaligned, fetchFault, executeTrap,
        dataTrap, trapHasWord, Expr.eval]
      all_goals rfl
  | k+30 => omega

theorem arch_holds (i : Values Input) (s : Values Register) (hr : i reset = 0)
    (hw : writeEnabled.eval i s = 0) (ht : retiring.eval i s = 0) :
    arch (circuit.step i s) = arch s := by
  rw [arch_step]
  simp only [hr, hw, ht]
  rfl

theorem fetch_request_represents (i : Values Input) (raw : Values Register)
    (hr : i reset = 0) (hp : raw phase = 0) :
    Represents (circuit.step i raw) (CoreModel.step (decode i) ⟨arch raw, .fetchRequest⟩) := by
  have hw : writeEnabled.eval i raw = 0 := by
    simp [writeEnabled, immediateRetire, executing, dataSuccess, dataCompletion,
      atomicCompletion, deferredCompletion, dataOffer, dataWaiting, active, inPhase, Expr.eval, hr, hp]
  have ht : retiring.eval i raw = 0 := by
    simp [retiring, immediateRetire, executing, dataSuccess, dataCompletion,
      atomicCompletion, deferredCompletion, dataOffer, dataWaiting, fenceRetire, active, inPhase, Expr.eval, hr, hp]
  have ha := arch_holds i raw hr hw ht
  by_cases hal : CoreModel.aligned (arch raw)
  all_goals rcases BitVec.eq_zero_or_eq_one (i fetchReady) with hf | hf
  all_goals simp [CoreModel.step, CoreModel.tick, decode, hr, hf, hal, Represents, ha,
    nextPhase, trapping, fetchMisaligned, fetchFault, executeTrap, dataTrap, executing,
    dataCompletion, atomicCompletion, deferredCompletion, dataOffer, dataWaiting,
    active, inPhase, isLoad, isStore, ht, pcAligned_eval, newCause, newFaultAddress,
    trapHasWord, Expr.eval, hp, causeCode, CoreInterface.faultAddress]
  all_goals rfl

theorem fetch_response_represents (i : Values Input) (raw : Values Register)
    (hr : i reset = 0) (hp : raw phase = 1) :
    Represents (circuit.step i raw) (CoreModel.step (decode i) ⟨arch raw, .fetchResponse⟩) := by
  have hw : writeEnabled.eval i raw = 0 := by
    simp [writeEnabled, immediateRetire, executing, dataSuccess, dataCompletion,
      atomicCompletion, deferredCompletion, dataOffer, dataWaiting, active, inPhase, Expr.eval, hr, hp]
  have ht : retiring.eval i raw = 0 := by
    simp [retiring, immediateRetire, executing, dataSuccess, dataCompletion,
      atomicCompletion, deferredCompletion, dataOffer, dataWaiting, fenceRetire, active, inPhase, Expr.eval, hr, hp]
  have ha := arch_holds i raw hr hw ht
  rcases BitVec.eq_zero_or_eq_one (i fetchResponseValid) with hv | hv
  all_goals rcases BitVec.eq_zero_or_eq_one (i fetchResponseFault) with hf | hf
  all_goals simp [CoreModel.step, CoreModel.tick, decode, hr, hv, hf, Represents, ha,
    nextPhase, trapping, fetchMisaligned, fetchFault, executeTrap, dataTrap, executing,
    dataCompletion, atomicCompletion, deferredCompletion, dataOffer, dataWaiting,
    active, inPhase, isLoad, isStore, ht, newCause, newFaultAddress,
    trapHasWord, Expr.eval, hp, causeCode, CoreInterface.faultAddress]
  all_goals rfl

theorem terminal_represents (i : Values Input) (raw : Values Register) (f : CoreModel.Fault)
    (hr : i reset = 0) (h : Represents raw ⟨arch raw, .terminal f⟩) :
    Represents (circuit.step i raw) (CoreModel.step (decode i) ⟨arch raw, .terminal f⟩) := by
  obtain ⟨_, hp, hpc, hc, ha, hv, hw⟩ := h
  have hwr : writeEnabled.eval i raw = 0 := by
    simp [writeEnabled, immediateRetire, executing, dataSuccess, dataCompletion,
      atomicCompletion, deferredCompletion, dataOffer, dataWaiting, active, inPhase, Expr.eval, hr, hp]
  have ht : retiring.eval i raw = 0 := by
    simp [retiring, immediateRetire, executing, dataSuccess, dataCompletion,
      atomicCompletion, deferredCompletion, dataOffer, dataWaiting, fenceRetire, active, inPhase, Expr.eval, hr, hp]
  have har := arch_holds i raw hr hwr ht
  simp [CoreModel.step, CoreModel.tick, decode, hr, Represents, har,
    nextPhase, trapping, fetchMisaligned, fetchFault, executeTrap, dataTrap, executing,
    dataCompletion, atomicCompletion, deferredCompletion, dataOffer, dataWaiting,
    active, inPhase, isLoad, isStore, ht, Expr.eval, hp, hpc, hc, ha, hv]
  exact hw

theorem fence_represents (i : Values Input) (raw : Values Register) (c : RV32I.Semantics.Context)
    (hr : i reset = 0) (hp : raw phase = 5) (hs : c.state = arch raw) :
    Represents (circuit.step i raw) (CoreModel.step (decode i) ⟨arch raw, .fence c⟩) := by
  have hwr : writeEnabled.eval i raw = 0 := by
    simp [writeEnabled, immediateRetire, executing, dataSuccess, dataCompletion,
      atomicCompletion, deferredCompletion, dataOffer, dataWaiting, active, inPhase, Expr.eval, hr, hp]
  have ht : retiring.eval i raw = 1 := by
    simp [retiring, immediateRetire, executing, dataSuccess, dataCompletion,
      atomicCompletion, deferredCompletion, dataOffer, dataWaiting, fenceRetire, active, inPhase, Expr.eval, hr, hp]
  have hn : nextPC.eval i raw = raw pc + 4 := by
    simp [nextPC, immediateRetire, executing, active, inPhase, Expr.eval, hp, hr]
  have ha : arch (circuit.step i raw) = RV32I.Semantics.next (arch raw) := by
    rw [arch_step]
    simp [hr, hwr, ht, hn, RV32I.Semantics.next, arch, architecture]
  simp [CoreModel.step, CoreModel.tick, decode, hr, CoreModel.acceptOutcome, RV32I.Semantics.finish,
    hs, Represents, ha, nextPhase, trapping, fetchMisaligned, fetchFault, executeTrap, dataTrap,
    executing, dataCompletion, atomicCompletion, deferredCompletion, dataOffer, dataWaiting,
    active, inPhase, ht, Expr.eval, hp]

@[simp] theorem bit_one_or (x : BitVec 1) : (1#1) ||| x = 1 := BitVec.allOnes_or
@[simp] theorem bit_one_and (x : BitVec 1) : (1#1) &&& x = x := BitVec.allOnes_and

theorem immediate_arch (i : Values Input) (raw : Values Register)
    (hr : i reset = 0) (hp : raw phase = 2)
    (hc : (execution .classification).eval i raw = 0) :
    arch (circuit.step i raw) =
      (RV32I.ExecuteCircuit.Result.ofValues (fun f => (execution f).eval i raw)).commit (arch raw) := by
  have him : immediateRetire.eval i raw = 1 := by
    simp [immediateRetire, executing, active, inPhase, Expr.eval, hr, hp, hc]
  have ht : retiring.eval i raw = 1 := by
    simp [retiring, him]
  have hw : writeEnabled.eval i raw = (execution .writeEnable).eval i raw := by
    simp [writeEnabled, him, dataSuccess, dataCompletion, atomicCompletion, deferredCompletion,
      dataOffer, dataWaiting, active, inPhase, Expr.eval, hr, hp]
  rw [arch_step]
  by_cases he : (execution .writeEnable).eval i raw = (1#1)
  all_goals simp [RV32I.ExecuteCircuit.Result.commit, RV32I.ExecuteCircuit.Result.ofValues,
    hr, ht, hw, he, writeRd, writeData, nextPC, him, Expr.eval]

theorem execute_retired_represents (i : Values Input) (raw : Values Register)
    (hr : i reset = 0) (hp : raw phase = 2) (context : RV32I.Semantics.Context)
    (after : RV32I.Semantics.State)
    (he : RV32I.Semantics.step (arch raw) (raw instruction) = .retired context after) :
    Represents (circuit.step i raw) ⟨after, .fetchRequest⟩ := by
  have hc : (execution .classification).eval i raw = 0 := by
    rw [execution_eval, he]; rfl
  have ha := immediate_arch i raw hr hp hc
  simp only [execution_eval, he, RV32I.ExecuteCircuit.ofValues_values] at ha
  have hf := RV32I.ExecuteCircuit.step_faithful (arch raw) (raw instruction)
  rw [he] at hf
  change (RV32I.ExecuteCircuit.project (.retired context after)).commit (arch raw) = after at hf
  rw [hf] at ha
  refine ⟨ha, ?_⟩
  simp [nextPhase, trapping, fetchMisaligned, fetchFault, executeTrap, dataTrap, retiring,
    immediateRetire, executing, dataSuccess, dataCompletion, atomicCompletion, deferredCompletion,
    dataOffer, dataWaiting, fenceRetire, active, inPhase, Expr.eval, hr, hp, hc]

theorem execute_pending_represents (i : Values Input) (raw : Values Register)
    (hr : i reset = 0) (hp : raw phase = 2) (p : RV32I.Semantics.Pending)
    (he : RV32I.Semantics.step (arch raw) (raw instruction) = .pending p) :
    Represents (circuit.step i raw)
      (CoreModel.acceptOutcome ⟨arch raw, .execute (raw instruction)⟩ .execute (.pending p)).1 := by
  have hs := RV32I.Semantics.step_origin (arch raw) (raw instruction)
  have hw := RV32I.Semantics.step_word (arch raw) (raw instruction)
  have hi := RV32I.Semantics.step_pending_issued (arch raw) (raw instruction) p he
  rw [he] at hs hw
  cases p
  all_goals
    have hwr : writeEnabled.eval i raw = 0 := by
      simp [writeEnabled, immediateRetire, executing, dataSuccess, dataCompletion,
        atomicCompletion, deferredCompletion, dataOffer, dataWaiting, active, inPhase, Expr.eval,
        execution_eval, hr, hp, he, RV32I.ExecuteCircuit.project, RV32I.ExecuteCircuit.loading,
        RV32I.ExecuteCircuit.storing, RV32I.ExecuteCircuit.fencing, RV32I.ExecuteCircuit.Result.values]
    have ht : retiring.eval i raw = 0 := by
      simp [retiring, immediateRetire, executing, dataSuccess, dataCompletion,
        atomicCompletion, deferredCompletion, dataOffer, dataWaiting, fenceRetire, active, inPhase,
        Expr.eval, execution_eval, hr, hp, he, RV32I.ExecuteCircuit.project, RV32I.ExecuteCircuit.loading,
        RV32I.ExecuteCircuit.storing, RV32I.ExecuteCircuit.fencing, RV32I.ExecuteCircuit.Result.values]
    have ha := arch_holds i raw hr hwr ht
    simp [CoreModel.acceptOutcome, Represents, ha, nextPhase, trapping, fetchMisaligned,
      fetchFault, executeTrap, dataTrap, executing, dataCompletion, atomicCompletion, deferredCompletion,
      dataOffer, dataWaiting, active, inPhase, isLoad, isStore, ht, Expr.eval, execution_eval, hr, hp, he,
      RV32I.ExecuteCircuit.project, RV32I.ExecuteCircuit.loading, RV32I.ExecuteCircuit.storing,
      RV32I.ExecuteCircuit.fencing, RV32I.ExecuteCircuit.Result.values, CoreModel.DataRequest.context,
      CoreModel.DataRequest.pending, RV32I.Semantics.Pending.context] at *
    exact ⟨hs, hw, hi⟩

theorem execute_trapped_represents (i : Values Input) (raw : Values Register)
    (hr : i reset = 0) (hp : raw phase = 2) (origin : RV32I.Semantics.State)
    (value : RV32I.Word) (trap : RV32I.Semantics.Trap)
    (he : RV32I.Semantics.step (arch raw) (raw instruction) = .trapped origin value trap) :
    Represents (circuit.step i raw)
      (CoreModel.acceptOutcome ⟨arch raw, .execute (raw instruction)⟩ .execute (.trapped origin value trap)).1 := by
  obtain ⟨_, hc, hs, hw⟩ := RV32I.ExecuteCircuit.step_trap_projection (arch raw) (raw instruction) origin value trap he
  subst origin
  subst value
  cases trap
  all_goals try simp [RV32I.ExecuteCircuit.project] at hc
  all_goals
    have hwr : writeEnabled.eval i raw = 0 := by
      simp [writeEnabled, immediateRetire, executing, dataSuccess, dataCompletion,
        atomicCompletion, deferredCompletion, dataOffer, dataWaiting, active, inPhase, Expr.eval,
        execution_eval, hr, hp, he, RV32I.ExecuteCircuit.project, RV32I.ExecuteCircuit.trapped,
        RV32I.ExecuteCircuit.Result.values]
    have ht : retiring.eval i raw = 0 := by
      simp [retiring, immediateRetire, executing, dataSuccess, dataCompletion,
        atomicCompletion, deferredCompletion, dataOffer, dataWaiting, fenceRetire, active, inPhase,
        Expr.eval, execution_eval, hr, hp, he, RV32I.ExecuteCircuit.project,
        RV32I.ExecuteCircuit.trapped, RV32I.ExecuteCircuit.Result.values]
    have ha := arch_holds i raw hr hwr ht
    simp [CoreModel.acceptOutcome, Represents, ha, nextPhase, trapping, fetchMisaligned,
      fetchFault, executeTrap, dataTrap, executing, dataCompletion, atomicCompletion, deferredCompletion,
      dataOffer, dataWaiting, active, inPhase, Expr.eval, execution_eval, hr, hp, he,
      RV32I.ExecuteCircuit.project, RV32I.ExecuteCircuit.trapped, RV32I.ExecuteCircuit.Result.values,
      newCause, newFaultAddress, trapHasWord, causeCode, CoreInterface.faultAddress]

theorem execute_represents (i : Values Input) (raw : Values Register)
    (hr : i reset = 0) (hp : raw phase = 2) :
    Represents (circuit.step i raw) (CoreModel.step (decode i) ⟨arch raw, .execute (raw instruction)⟩) := by
  simp only [CoreModel.step, CoreModel.tick, decode, hr]
  change Represents _ (CoreModel.acceptOutcome _ _ (RV32I.Semantics.step (arch raw) (raw instruction))).1
  cases he : RV32I.Semantics.step (arch raw) (raw instruction) with
  | retired context after => exact execute_retired_represents i raw hr hp context after he
  | pending p => exact execute_pending_represents i raw hr hp p he
  | trapped origin value trap => exact execute_trapped_represents i raw hr hp origin value trap he

theorem request_step_eq (raw : Values Register) (q : CoreModel.DataRequest)
    (hs : q.context.state = arch raw) (hw : q.context.word = raw instruction) (hi : q.pending.Issued) :
    RV32I.Semantics.step (arch raw) (raw instruction) = .pending q.pending := by
  have he := issued_step q.pending hi
  change RV32I.Semantics.step q.context.state q.context.word = .pending q.pending at he
  simpa only [hs, hw] using he

theorem data_quiet_arch (i : Values Input) (raw : Values Register) (p : BitVec 3)
    (hr : i reset = 0) (hp : raw phase = p) (hphase : p = 3 ∨ p = 4)
    (hc : dataCompletion.eval i raw = 0) : arch (circuit.step i raw) = arch raw := by
  apply arch_holds i raw hr
  · rcases hphase with rfl | rfl <;>
      simp [writeEnabled, immediateRetire, executing, dataSuccess, hc, active, inPhase, Expr.eval, hp, hr]
  · rcases hphase with rfl | rfl <;>
      simp [retiring, immediateRetire, executing, dataSuccess, hc, fenceRetire, active, inPhase, Expr.eval, hp, hr]

theorem data_request_quiet (i : Values Input) (raw : Values Register) (q : CoreModel.DataRequest)
    (hr : i reset = 0) (hp : raw phase = 3)
    (hs : q.context.state = arch raw) (hw : q.context.word = raw instruction) (hi : q.pending.Issued)
    (hc : dataCompletion.eval i raw = 0) :
    Represents (circuit.step i raw) ⟨arch raw,
      if i dataServiceValid = 1 then .dataResponse q else .dataRequest q⟩ := by
  have ha := data_quiet_arch i raw 3 hr hp (Or.inl rfl) hc
  rcases BitVec.eq_zero_or_eq_one (i dataServiceValid) with hv | hv
  all_goals simp [Represents, ha, nextPhase, trapping, fetchMisaligned, fetchFault, executeTrap,
    dataTrap, retiring, immediateRetire, executing, dataSuccess, hc, fenceRetire,
    active, inPhase, Expr.eval, hr, hp, hv, CoreModel.DataRequest.context, CoreModel.DataRequest.pending] at *
  all_goals exact ⟨hs, hw, hi⟩

theorem data_response_quiet (i : Values Input) (raw : Values Register) (q : CoreModel.DataRequest)
    (hr : i reset = 0) (hp : raw phase = 4)
    (hs : q.context.state = arch raw) (hw : q.context.word = raw instruction) (hi : q.pending.Issued)
    (hc : dataCompletion.eval i raw = 0) :
    Represents (circuit.step i raw) ⟨arch raw, .dataResponse q⟩ := by
  have ha := data_quiet_arch i raw 4 hr hp (Or.inr rfl) hc
  simp [Represents, ha, nextPhase, trapping, fetchMisaligned, fetchFault, executeTrap,
    dataTrap, retiring, immediateRetire, executing, dataSuccess, hc, fenceRetire,
    active, inPhase, Expr.eval, hr, hp]
  exact ⟨hs, hw, hi⟩

theorem data_load_arch (i : Values Input) (raw : Values Register) (p : BitVec 3)
    (hr : i reset = 0) (hp : raw phase = p) (hphase : p = 3 ∨ p = 4)
    (context : RV32I.Semantics.Context) (op : RV32I.LoadOp) (dest : RV32I.Register) (address : BitVec 32)
    (he : RV32I.Semantics.step (arch raw) (raw instruction) = .pending (.load context op dest address))
    (hc : dataCompletion.eval i raw = 1) (hf : replyFault.eval i raw = 0) :
    arch (circuit.step i raw) = RV32I.Semantics.writeNext (arch raw) dest (RV32I.Semantics.loadValue op (replyData.eval i raw)) := by
  have hl := loadedValue_load i raw context op dest address he
  have hrw := RV32I.ExecuteCircuit.commit_retired (arch raw) ((arch raw).pc+4) dest
    (RV32I.Semantics.loadValue op (replyData.eval i raw))
  change _ = RV32I.Semantics.writeNext (arch raw) dest _ at hrw
  rw [← hrw, arch_step]
  rcases hphase with rfl | rfl
  all_goals by_cases hz : dest = (0#5)
  all_goals simp [RV32I.ExecuteCircuit.Result.commit, RV32I.ExecuteCircuit.retired,
    hr, hp, hz, retiring, immediateRetire, executing, dataSuccess, hc, hf, fenceRetire,
    writeEnabled, writeRd, writeData, isLoad, nextPC, active, inPhase, execution_eval, he,
    RV32I.ExecuteCircuit.project, RV32I.ExecuteCircuit.loading, RV32I.ExecuteCircuit.Result.values,
    Expr.eval, hl, RV32I.ExecuteCircuit.bool_beq, bne]
  all_goals rfl

theorem data_store_arch (i : Values Input) (raw : Values Register) (p : BitVec 3)
    (hr : i reset = 0) (hp : raw phase = p) (hphase : p = 3 ∨ p = 4)
    (context : RV32I.Semantics.Context) (op : RV32I.StoreOp) (address data : BitVec 32)
    (he : RV32I.Semantics.step (arch raw) (raw instruction) = .pending (.store context op address data))
    (hc : dataCompletion.eval i raw = 1) (hf : replyFault.eval i raw = 0) :
    arch (circuit.step i raw) = RV32I.Semantics.next (arch raw) := by
  rw [arch_step]
  rcases hphase with rfl | rfl
  all_goals simp [hr, hp, retiring, immediateRetire, executing, dataSuccess, hc, hf, fenceRetire,
    writeEnabled, isLoad, nextPC, active, inPhase, execution_eval, he,
    RV32I.ExecuteCircuit.project, RV32I.ExecuteCircuit.storing, RV32I.ExecuteCircuit.Result.values,
    Expr.eval, RV32I.Semantics.next]
  all_goals rfl

theorem data_fault_arch (i : Values Input) (raw : Values Register) (p : BitVec 3)
    (hr : i reset = 0) (hp : raw phase = p) (hphase : p = 3 ∨ p = 4)
    (hf : replyFault.eval i raw ≠ (0#2)) : arch (circuit.step i raw) = arch raw := by
  apply arch_holds i raw hr
  · rcases hphase with rfl | rfl <;>
      simp [writeEnabled, immediateRetire, executing, dataSuccess, hf, active, inPhase, Expr.eval, hp, hr]
  · rcases hphase with rfl | rfl <;>
      simp [retiring, immediateRetire, executing, dataSuccess, hf, fenceRetire, active, inPhase, Expr.eval, hp, hr]

theorem data_fault_represents (i : Values Input) (raw : Values Register) (p : BitVec 3)
    (hr : i reset = 0) (hp : raw phase = p) (hphase : p = 3 ∨ p = 4) (q : CoreModel.DataRequest)
    (hs : q.context.state = arch raw) (hw : q.context.word = raw instruction) (hi : q.pending.Issued)
    (hc : dataCompletion.eval i raw = 1) (hf : replyFault.eval i raw ≠ (0#2))
    (completion : CoreModel.Completion) :
    Represents (circuit.step i raw) (CoreModel.acceptOutcome ⟨arch raw, .dataRequest q⟩ completion
      (q.finish (reply (replyFault.eval i raw) (replyData.eval i raw)))).1 := by
  have he := request_step_eq raw q hs hw hi
  have ha := data_fault_arch i raw p hr hp hphase hf
  cases q
  all_goals rcases hphase with rfl | rfl
  all_goals by_cases hf1 : replyFault.eval i raw = (1#2)
  all_goals simp [CoreModel.DataRequest.context, CoreModel.DataRequest.pending, RV32I.Semantics.Pending.context] at hs hw he
  all_goals simp [CoreModel.acceptOutcome, CoreModel.DataRequest.finish, CoreModel.DataRequest.reply,
    CoreModel.DataRequest.pending, reply, hf, hf1, RV32I.Semantics.finish,
    Represents, ha, nextPhase, trapping, fetchMisaligned, fetchFault, executeTrap,
    dataTrap, executing, active, inPhase, Expr.eval, execution_eval, hr, hp, he,
    RV32I.ExecuteCircuit.project, RV32I.ExecuteCircuit.loading, RV32I.ExecuteCircuit.storing,
    RV32I.ExecuteCircuit.Result.values, isLoad, newCause, newFaultAddress, trapHasWord,
    causeCode, CoreInterface.faultAddress, hc, hw]

theorem data_success_phase (i : Values Input) (raw : Values Register) (p : BitVec 3)
    (hr : i reset = 0) (hp : raw phase = p) (hphase : p = 3 ∨ p = 4)
    (hc : dataCompletion.eval i raw = 1) (hf : replyFault.eval i raw = 0) :
    circuit.step i raw phase = 0 := by
  rcases hphase with rfl | rfl <;>
    simp [nextPhase, trapping, fetchMisaligned, fetchFault, executeTrap, dataTrap, executing,
      retiring, immediateRetire, dataSuccess, hc, hf, fenceRetire, active, inPhase, Expr.eval, hr, hp]

theorem data_success_represents (i : Values Input) (raw : Values Register) (p : BitVec 3)
    (hr : i reset = 0) (hp : raw phase = p) (hphase : p = 3 ∨ p = 4) (q : CoreModel.DataRequest)
    (hs : q.context.state = arch raw) (hw : q.context.word = raw instruction) (hi : q.pending.Issued)
    (hc : dataCompletion.eval i raw = 1) (hf : replyFault.eval i raw = 0)
    (completion : CoreModel.Completion) :
    Represents (circuit.step i raw) (CoreModel.acceptOutcome ⟨arch raw, .dataRequest q⟩ completion
      (q.finish (reply (replyFault.eval i raw) (replyData.eval i raw)))).1 := by
  have he := request_step_eq raw q hs hw hi
  have hn := data_success_phase i raw p hr hp hphase hc hf
  cases q with
  | load context op dest address =>
      have ha := data_load_arch i raw p hr hp hphase context op dest address he hc hf
      change context.state = arch raw at hs
      simpa [CoreModel.DataRequest.finish, CoreModel.DataRequest.reply, CoreModel.DataRequest.pending,
        reply, hf, RV32I.Semantics.finish, CoreModel.acceptOutcome, Represents, hs] using And.intro ha hn
  | store context op address data =>
      have ha := data_store_arch i raw p hr hp hphase context op address data he hc hf
      change context.state = arch raw at hs
      simpa [CoreModel.DataRequest.finish, CoreModel.DataRequest.reply, CoreModel.DataRequest.pending,
        reply, hf, RV32I.Semantics.finish, CoreModel.acceptOutcome, Represents, hs] using And.intro ha hn

theorem data_completed_represents (i : Values Input) (raw : Values Register) (p : BitVec 3)
    (hr : i reset = 0) (hp : raw phase = p) (hphase : p = 3 ∨ p = 4) (q : CoreModel.DataRequest)
    (hs : q.context.state = arch raw) (hw : q.context.word = raw instruction) (hi : q.pending.Issued)
    (hc : dataCompletion.eval i raw = 1) (completion : CoreModel.Completion) :
    Represents (circuit.step i raw) (CoreModel.acceptOutcome ⟨arch raw, .dataRequest q⟩ completion
      (q.finish (reply (replyFault.eval i raw) (replyData.eval i raw)))).1 := by
  by_cases hf : replyFault.eval i raw = (0#2)
  · exact data_success_represents i raw p hr hp hphase q hs hw hi hc hf completion
  · exact data_fault_represents i raw p hr hp hphase q hs hw hi hc hf completion

theorem data_request_represents (i : Values Input) (raw : Values Register) (q : CoreModel.DataRequest)
    (hr : i reset = 0) (hp : raw phase = 3)
    (hs : q.context.state = arch raw) (hw : q.context.word = raw instruction) (hi : q.pending.Issued) :
    Represents (circuit.step i raw) (CoreModel.step (decode i) ⟨arch raw, .dataRequest q⟩) := by
  rcases BitVec.eq_zero_or_eq_one (i dataServiceValid) with hv | hv
  · have hc : dataCompletion.eval i raw = 0 := by
      simp [dataCompletion, atomicCompletion, deferredCompletion, dataOffer, dataWaiting,
        active, inPhase, Expr.eval, hp, hr, hv]
    simpa [CoreModel.step, CoreModel.tick, decode, hr, hv] using data_request_quiet i raw q hr hp hs hw hi hc
  · rcases BitVec.eq_zero_or_eq_one (i dataServiceAtomic) with ha | ha
    · have hc : dataCompletion.eval i raw = 0 := by
        simp [dataCompletion, atomicCompletion, deferredCompletion, dataOffer, dataWaiting,
          active, inPhase, Expr.eval, hp, hr, hv, ha]
      simpa [CoreModel.step, CoreModel.tick, decode, hr, hv, ha] using data_request_quiet i raw q hr hp hs hw hi hc
    · have hc : dataCompletion.eval i raw = 1 := by
        simp [dataCompletion, atomicCompletion, deferredCompletion, dataOffer, dataWaiting,
          active, inPhase, Expr.eval, hp, hr, hv, ha]
      have h := data_completed_represents i raw 3 hr hp (Or.inl rfl) q hs hw hi hc
        (.data .atomic q.intent (reply (i dataServiceFault) (i dataServiceData)))
      simpa [CoreModel.step, CoreModel.tick, decode, hr, hv, ha, replyFault, replyData, inPhase, Expr.eval, hp] using h

theorem data_response_represents (i : Values Input) (raw : Values Register) (q : CoreModel.DataRequest)
    (hr : i reset = 0) (hp : raw phase = 4)
    (hs : q.context.state = arch raw) (hw : q.context.word = raw instruction) (hi : q.pending.Issued) :
    Represents (circuit.step i raw) (CoreModel.step (decode i) ⟨arch raw, .dataResponse q⟩) := by
  rcases BitVec.eq_zero_or_eq_one (i dataResponseValid) with hv | hv
  · have hc : dataCompletion.eval i raw = 0 := by
      simp [dataCompletion, atomicCompletion, deferredCompletion, dataOffer, dataWaiting,
        active, inPhase, Expr.eval, hp, hr, hv]
    simpa [CoreModel.step, CoreModel.tick, decode, hr, hv] using data_response_quiet i raw q hr hp hs hw hi hc
  · have hc : dataCompletion.eval i raw = 1 := by
      simp [dataCompletion, atomicCompletion, deferredCompletion, dataOffer, dataWaiting,
        active, inPhase, Expr.eval, hp, hr, hv]
    have h := data_completed_represents i raw 4 hr hp (Or.inr rfl) q hs hw hi hc
      (.data .deferred q.intent (reply (i dataResponseFault) (i dataResponseData)))
    simpa [CoreModel.step, CoreModel.tick, decode, hr, hv, replyFault, replyData, inPhase, Expr.eval, hp, CoreModel.acceptOutcome] using h

/-- Every represented raw state takes the exact logical next step, including
atomic completion on a request edge and deferred completion only after ownership. -/
theorem step_represents (i : Values Input) (raw : Values Register) (state : CoreModel.State)
    (h : Represents raw state) : Represents (circuit.step i raw) (CoreModel.step (decode i) state) := by
  rcases BitVec.eq_zero_or_eq_one (i reset) with hr | hr
  · rcases state with ⟨a, p⟩
    rcases h with ⟨ha, hp⟩
    dsimp only at ha hp
    subst a
    cases p with
    | fetchRequest => exact fetch_request_represents i raw hr hp
    | fetchResponse => exact fetch_response_represents i raw hr hp
    | execute w =>
        rcases hp with ⟨hp, hw⟩
        subst w
        exact execute_represents i raw hr hp
    | dataRequest q =>
        rcases hp with ⟨hp, hs, hw, hi⟩
        exact data_request_represents i raw q hr hp hs hw hi
    | dataResponse q =>
        rcases hp with ⟨hp, hs, hw, hi⟩
        exact data_response_represents i raw q hr hp hs hw hi
    | fence c =>
        rcases hp with ⟨hp, hs, _, _⟩
        exact fence_represents i raw c hr hp hs
    | terminal f => exact terminal_represents i raw f hr ⟨rfl, hp⟩
  · rw [reset_values i raw hr]
    simpa [CoreModel.step, CoreModel.tick, decode, hr] using zero_represents

theorem preserved (i : Values Input) (raw : Values Register) (h : Valid raw) : Valid (circuit.step i raw) := by
  obtain ⟨state, hv, hr⟩ := h
  exact ⟨CoreModel.step (decode i) state, CoreModel.preserved _ _ hv, step_represents i raw state hr⟩

theorem step_eq (i : Values Input) (raw : Values Register) (h : Valid raw) :
    view (circuit.step i raw) = CoreInterface.spec.step i (view raw) := by
  obtain ⟨state, _, hr⟩ := h
  rw [view_of_represents raw state hr]
  exact view_of_represents _ _ (step_represents i raw state hr)

/-- A canonical encoding supplies coverage of every valid logical controller
state; the refinement also admits arbitrary retained inactive metadata. -/
def phaseCode : CoreModel.Phase → BitVec 3
  | .fetchRequest => 0 | .fetchResponse => 1 | .execute _ => 2
  | .dataRequest _ => 3 | .dataResponse _ => 4 | .fence _ => 5 | .terminal _ => 6

def instructionWord : CoreModel.Phase → BitVec 32
  | .execute w => w
  | .dataRequest q | .dataResponse q => q.context.word
  | .fence c => c.word
  | .terminal f => f.word.getD 0
  | _ => 0

def encode (state : CoreModel.State) : Values Register
  | _, .left (.at k) => state.arch.registers k
  | _, .right (.at ⟨0,_⟩) => phaseCode state.phase
  | _, .right (.at ⟨1,_⟩) => state.arch.pc
  | _, .right (.at ⟨2,_⟩) => instructionWord state.phase
  | _, .right (.at ⟨3,_⟩) => match state.phase with | .terminal f => causeCode f.cause | _ => 0
  | _, .right (.at ⟨4,_⟩) => match state.phase with | .terminal f => CoreInterface.faultAddress f | _ => 0
  | _, .right (.at ⟨5,_⟩) => match state.phase with | .terminal f => BitVec.ofBool f.word.isSome | _ => 0
  | _, .right (.at ⟨k+6,h⟩) => False.elim (by change k+6 < 6 at h; omega)

@[simp] theorem arch_encode (state : CoreModel.State) : arch (encode state) = state.arch := rfl

theorem encode_represents (state : CoreModel.State) (h : CoreModel.Valid state) : Represents (encode state) state := by
  rcases state with ⟨a, p⟩
  refine ⟨rfl, ?_⟩
  cases p <;> simp only [CoreModel.Valid] at h
  all_goals try rfl
  case dataRequest q => exact ⟨rfl, h.2.1, rfl, h.2.2⟩
  case dataResponse q => exact ⟨rfl, h.2.1, rfl, h.2.2⟩
  case fence c => exact ⟨rfl, h.2.1, rfl, h.2.2⟩
  case execute w => exact ⟨rfl, rfl⟩
  case terminal f =>
    refine ⟨rfl, h, rfl, rfl, rfl, ?_⟩
    intro w hw
    change f.word.getD 0 = w
    simp [hw]

theorem view_encode (state : CoreModel.State) (h : CoreModel.Valid state) : view (encode state) = state :=
  view_of_represents _ _ (encode_represents state h)

theorem valid_encode (state : CoreModel.State) (h : CoreModel.Valid state) : Valid (encode state) :=
  ⟨state, h, encode_represents state h⟩

end Pinwheel.Hardware.Processor.CoreCircuit
