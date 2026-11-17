import Pinwheel.Hardware.Processor.CoreCircuitProofs
import Pinwheel.Hardware.Processor.CoreCircuitWriteback

/-! Exact observation correspondence for every represented processor state.
These proofs cover all 30 physical output ports, including atomic/deferred
completion, reset masking, traps, and held terminal metadata. Architectural
validity and provider truth remain distinct: this module proves the controller
against CoreInterface.spec and does not certify an instruction/data provider. -/
namespace Pinwheel.Hardware.Processor.CoreCircuit
open CoreInterface RV32I
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4000
set_option maxHeartbeats 4000000

macro "output_cases" o:ident : tactic => `(tactic| (
  rcases ($o) with ⟨⟨k,hk⟩⟩
  have bound : k < 30 := hk
  rcases k with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ |
    _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | k
  all_goals try (exfalso; omega)))

macro "output_simp" : tactic => `(tactic|
  simp_all [Circuit.observe,circuit,CoreInterface.outputValues,CoreModel.observe,CoreModel.event,CoreModel.tick,
    CoreInterface.decode,CoreInterface.eventWrite,CoreInterface.retired,CoreInterface.trapped,
    active,inPhase,pcAligned_eval,executing,dataOffer,dataWaiting,retiring,immediateRetire,
    dataSuccess,dataCompletion,atomicCompletion,deferredCompletion,fenceRetire,
    writeEnabled,writeRd,writeData,trapping,fetchMisaligned,fetchFault,executeTrap,dataTrap,trapHasWord,
    isLoad,isStore,nextPC,newCause,newFaultAddress,CoreModel.terminal,CoreModel.acceptOutcome,RV32I.Semantics.finish,RV32I.Semantics.next,
    Expr.eval,arch,architecture,CoreInterface.causeCode,CoreInterface.faultAddress])

theorem fetch_request_output (i : Values Input) (raw : Values Register)
    (hr : i reset = 0) (hp : raw phase = 0) (o : Output b) :
    circuit.observe i raw o = outputValues i ⟨arch raw,.fetchRequest⟩ o := by
  by_cases hal : CoreModel.aligned (arch raw)
  all_goals output_cases o
  all_goals output_simp
  all_goals rfl

theorem fetch_response_output (i : Values Input) (raw : Values Register)
    (hr : i reset = 0) (hp : raw phase = 1) (o : Output b) :
    circuit.observe i raw o = outputValues i ⟨arch raw,.fetchResponse⟩ o := by
  rcases BitVec.eq_zero_or_eq_one (i fetchResponseValid) with hv | hv
  all_goals rcases BitVec.eq_zero_or_eq_one (i fetchResponseFault) with hf | hf
  all_goals output_cases o
  all_goals output_simp
  all_goals rfl

def pendingDestination : Semantics.Pending → RV32I.Register
  | .load _ _ d _ => d | _ => 0

theorem issued_destination (p : Semantics.Pending) (hi : p.Issued) :
    CoreInterface.writeDestination p.context.instruction = pendingDestination p := by
  cases p with
  | load c op dest address =>
    cases hin : c.instruction <;>
      simp only [Semantics.Pending.Issued, Semantics.Pending.context, Semantics.executeContext, hin,
        CoreInterface.writeDestination, pendingDestination] at hi ⊢
    all_goals try (first | rfl | (cases hi <;> rfl))
    all_goals unfold Semantics.transfer at hi
    all_goals simp only at hi
    all_goals repeat' split at hi
    all_goals cases hi
  | store c op address value =>
    cases hin : c.instruction <;>
      simp only [Semantics.Pending.Issued, Semantics.Pending.context, Semantics.executeContext, hin,
        CoreInterface.writeDestination, pendingDestination] at hi ⊢
    all_goals try (first | rfl | (cases hi <;> rfl))
    all_goals unfold Semantics.transfer at hi
    all_goals simp only at hi
    all_goals repeat' split at hi
    all_goals cases hi
  | fence c =>
    cases hin : c.instruction <;>
      simp only [Semantics.Pending.Issued, Semantics.Pending.context, Semantics.executeContext, hin,
        CoreInterface.writeDestination, pendingDestination] at hi ⊢
    all_goals try (first | rfl | (cases hi <;> rfl))
    all_goals unfold Semantics.transfer at hi
    all_goals simp only at hi
    all_goals repeat' split at hi
    all_goals cases hi

theorem terminal_output (i : Values Input) (raw : Values Register) (f : CoreModel.Fault)
    (hr : i reset = 0) (h : Represents raw ⟨arch raw,.terminal f⟩) (o : Output b) :
    circuit.observe i raw o = outputValues i ⟨arch raw,.terminal f⟩ o := by
  obtain ⟨_,hp,hpc,hc,ha,hv,hw⟩ := h
  cases hf : f.word with
  | none =>
      output_cases o
      all_goals output_simp
      all_goals rfl
  | some value =>
      have hir := hw value hf
      output_cases o
      all_goals output_simp
      all_goals rfl

theorem fence_output (i : Values Input) (raw : Values Register) (c : RV32I.Semantics.Context)
    (hr : i reset = 0) (hp : raw phase = 5) (hs : c.state = arch raw)
    (hw : c.word = raw instruction) (hi : (RV32I.Semantics.Pending.fence c).Issued) (o : Output b) :
    circuit.observe i raw o = outputValues i ⟨arch raw,.fence c⟩ o := by
  have hd : RV32I.decode (raw instruction) = some c.instruction := hw ▸ c.decoded
  have dest := issued_destination (.fence c) hi
  change CoreInterface.writeDestination c.instruction = 0 at dest
  output_cases o
  all_goals output_simp
  all_goals rfl

macro "data_output_simp" : tactic => `(tactic|
  simp [*,Circuit.observe,circuit,CoreInterface.outputValues,CoreModel.observe,CoreModel.event,CoreModel.tick,
    CoreInterface.decode,CoreInterface.eventWrite,CoreInterface.retired,CoreInterface.trapped,
    active,inPhase,pcAligned_eval,executing,dataOffer,dataWaiting,retiring,immediateRetire,
    dataSuccess,dataCompletion,atomicCompletion,deferredCompletion,fenceRetire,
    writeEnabled,writeRd,writeData,trapping,fetchMisaligned,fetchFault,executeTrap,dataTrap,trapHasWord,
    isLoad,isStore,nextPC,newCause,newFaultAddress,CoreInterface.reply,replyFault,replyData,CoreModel.DataRequest.intent,CoreModel.DataRequest.pending,CoreModel.DataRequest.reply,CoreModel.DataRequest.finish,RV32I.Semantics.Pending.intent,CoreModel.terminal,CoreModel.acceptOutcome,RV32I.Semantics.finish,RV32I.Semantics.next,
    Expr.eval,CoreInterface.causeCode,CoreInterface.faultAddress])

macro "finish_store_outputs" o:ident : tactic => `(tactic| (
  rcases ($o) with ⟨⟨k,hk⟩⟩
  have bound : k < 30 := hk
  match k with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 |
    15 | 16 | 17 | 18 | 19 | 20 | 21 | 22 | 23 | 24 | 25 | 26 | 27 | 28 | 29 =>
    all_goals try data_output_simp
    all_goals rfl
  | k+30 => omega))

theorem data_store_output (i : Values Input) (raw : Values Register) (p : BitVec 3)
    (hr : i reset = 0) (hp : raw phase = p) (hphase : p = 3 ∨ p = 4)
    (c : RV32I.Semantics.Context) (op : RV32I.StoreOp) (address operand : BitVec 32)
    (hs : c.state = arch raw) (hw : c.word = raw instruction)
    (hi : (RV32I.Semantics.Pending.store c op address operand).Issued) (o : Output b) :
    circuit.observe i raw o = outputValues i ⟨arch raw,
      if p = 3 then .dataRequest (.store c op address operand) else .dataResponse (.store c op address operand)⟩ o := by
  have he := issued_step (.store c op address operand) hi
  change RV32I.Semantics.step c.state c.word = _ at he
  rw [hs,hw] at he
  have field0 : (execution .classification).eval i raw = 2 := by
    rw [execution_eval,he]
    rfl
  have field1 : (execution .address).eval i raw = address := by
    rw [execution_eval,he]
    rfl
  have field2 : (execution .size).eval i raw = RV32I.ExecuteCircuit.sizeCode (RV32I.Semantics.storeSize op) := by
    rw [execution_eval,he]
    rfl
  have field3 : (execution .signedLoad).eval i raw = 0 := by
    rw [execution_eval,he]
    rfl
  have field4 : (execution .storeData).eval i raw = operand := by
    rw [execution_eval,he]
    rfl
  have hd : RV32I.decode (raw instruction) = some c.instruction := hw ▸ c.decoded
  have dest := issued_destination (.store c op address operand) hi
  change CoreInterface.writeDestination c.instruction = 0 at dest
  clear he hi
  rcases hphase with rfl | rfl
  · rcases BitVec.eq_zero_or_eq_one (i dataServiceValid) with hv | hv
    · finish_store_outputs o
    · rcases BitVec.eq_zero_or_eq_one (i dataServiceAtomic) with ha | ha
      · finish_store_outputs o
      · by_cases hf : i dataServiceFault = (0#2)
        · finish_store_outputs o
        · by_cases hmis : i dataServiceFault = (1#2) <;> finish_store_outputs o
  · rcases BitVec.eq_zero_or_eq_one (i dataResponseValid) with hv | hv
    · finish_store_outputs o
    · by_cases hf : i dataResponseFault = (0#2)
      · finish_store_outputs o
      · by_cases hmis : i dataResponseFault = (1#2) <;> finish_store_outputs o

@[simp] theorem load_signed_match (address : BitVec 32) (size : Memory.ByteAccess.Size) (sign : Bool) :
    (match some (RV32I.Semantics.Intent.load address size sign) with
      | some (.load _ _ true) => true | _ => false) = sign := by
  cases sign <;> rfl

macro "finish_load_outputs" o:ident dest:ident : tactic => `(tactic| (
  rcases ($o) with ⟨⟨k,hk⟩⟩
  have bound : k < 30 := hk
  match k with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 |
    15 | 16 | 17 | 18 | 19 | 20 | 21 | 22 | 23 | 24 | 25 | 26 | 27 | 28 | 29 =>
    all_goals try data_output_simp
    all_goals by_cases hz : $dest = (0#5)
    all_goals try simp [*,RV32I.Semantics.writeNext,RV32I.Semantics.read_write_same,RV32I.ExecuteCircuit.bool_beq,bne]
    all_goals first | rfl | exact congrArg BitVec.ofBool (load_signed_match _ _ _).symm
  | k+30 => omega))

theorem data_load_output (i : Values Input) (raw : Values Register) (p : BitVec 3)
    (hr : i reset = 0) (hp : raw phase = p) (hphase : p = 3 ∨ p = 4)
    (c : RV32I.Semantics.Context) (op : RV32I.LoadOp) (dest : RV32I.Register) (address : BitVec 32)
    (hs : c.state = arch raw) (hw : c.word = raw instruction)
    (hi : (RV32I.Semantics.Pending.load c op dest address).Issued) (o : Output b) :
    circuit.observe i raw o = outputValues i ⟨arch raw,
      if p = 3 then .dataRequest (.load c op dest address) else .dataResponse (.load c op dest address)⟩ o := by
  have he := issued_step (.load c op dest address) hi
  change RV32I.Semantics.step c.state c.word = _ at he
  rw [hs,hw] at he
  have field0 : (execution .classification).eval i raw = 1 := by
    rw [execution_eval,he]
    rfl
  have field1 : (execution .address).eval i raw = address := by
    rw [execution_eval,he]
    rfl
  have field2 : (execution .size).eval i raw = RV32I.ExecuteCircuit.sizeCode (RV32I.Semantics.loadSize op) := by
    rw [execution_eval,he]
    rfl
  have field3 : (execution .signedLoad).eval i raw = BitVec.ofBool (RV32I.Semantics.loadSigned op) := by
    rw [execution_eval,he]
    rfl
  have field4 : (execution .storeData).eval i raw = 0 := by
    rw [execution_eval,he]
    rfl
  have field5 : (execution .loadRd).eval i raw = dest := by
    rw [execution_eval,he]
    rfl
  have hd : RV32I.decode (raw instruction) = some c.instruction := hw ▸ c.decoded
  have destination := issued_destination (.load c op dest address) hi
  change CoreInterface.writeDestination c.instruction = dest at destination
  have hl := loadedValue_load i raw c op dest address he
  clear he hi
  rcases hphase with rfl | rfl
  · rcases BitVec.eq_zero_or_eq_one (i dataServiceValid) with hv | hv
    · finish_load_outputs o dest
    · rcases BitVec.eq_zero_or_eq_one (i dataServiceAtomic) with ha | ha
      · finish_load_outputs o dest
      · by_cases hf : i dataServiceFault = (0#2)
        · finish_load_outputs o dest
        · by_cases hmis : i dataServiceFault = (1#2) <;> finish_load_outputs o dest
  · rcases BitVec.eq_zero_or_eq_one (i dataResponseValid) with hv | hv
    · finish_load_outputs o dest
    · by_cases hf : i dataResponseFault = (0#2)
      · finish_load_outputs o dest
      · by_cases hmis : i dataResponseFault = (1#2) <;> finish_load_outputs o dest

macro "execute_output_simp" : tactic => `(tactic|
  simp_all [Circuit.observe,circuit,CoreInterface.outputValues,CoreModel.observe,CoreModel.event,CoreModel.tick,
    CoreModel.acceptOutcome,CoreInterface.decode,CoreInterface.eventWrite,CoreInterface.retired,CoreInterface.trapped,
    active,inPhase,executing,dataOffer,dataWaiting,retiring,immediateRetire,
    dataSuccess,dataCompletion,atomicCompletion,deferredCompletion,fenceRetire,
    writeEnabled,writeRd,writeData,trapping,fetchMisaligned,fetchFault,executeTrap,dataTrap,trapHasWord,
    isLoad,isStore,nextPC,newCause,newFaultAddress,CoreModel.terminal,
    execution_eval,RV32I.ExecuteCircuit.project,RV32I.ExecuteCircuit.retired,RV32I.ExecuteCircuit.trapped,
    RV32I.ExecuteCircuit.loading,RV32I.ExecuteCircuit.storing,RV32I.ExecuteCircuit.fencing,
    RV32I.ExecuteCircuit.Result.values,Expr.eval,CoreInterface.causeCode,CoreInterface.faultAddress,
    RV32I.ExecuteCircuit.bool_beq,bne])

theorem execute_retired_output (i : Values Input) (raw : Values Register)
    (hr : i reset = 0) (hp : raw phase = 2) (context : RV32I.Semantics.Context)
    (after : RV32I.Semantics.State)
    (he : RV32I.Semantics.step (arch raw) (raw instruction) = .retired context after) (o : Output b) :
    circuit.observe i raw o = outputValues i ⟨arch raw,.execute (raw instruction)⟩ o := by
  have hw := RV32I.Semantics.step_word (arch raw) (raw instruction)
  rw [he] at hw
  change context.word = raw instruction at hw
  have hd : RV32I.decode (raw instruction) = some context.instruction := hw ▸ context.decoded
  have hdest := immediate_destination (arch raw) (raw instruction) context after he
  by_cases hz : RV32I.DecodeCircuit.instructionRd context.instruction = (0#5)
  all_goals
    rcases o with ⟨⟨k,hk⟩⟩
    have bound : k < 30 := hk
    match k with
    | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 |
      15 | 16 | 17 | 18 | 19 | 20 | 21 | 22 | 23 | 24 | 25 | 26 | 27 | 28 | 29 =>
        execute_output_simp
        all_goals rfl
    | k+30 => omega

theorem execute_pending_output (i : Values Input) (raw : Values Register)
    (hr : i reset = 0) (hp : raw phase = 2) (p : RV32I.Semantics.Pending)
    (he : RV32I.Semantics.step (arch raw) (raw instruction) = .pending p) (o : Output b) :
    circuit.observe i raw o = outputValues i ⟨arch raw,.execute (raw instruction)⟩ o := by
  cases p
  all_goals
    rcases o with ⟨⟨k,hk⟩⟩
    have bound : k < 30 := hk
    match k with
    | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 |
      15 | 16 | 17 | 18 | 19 | 20 | 21 | 22 | 23 | 24 | 25 | 26 | 27 | 28 | 29 =>
        execute_output_simp
        all_goals rfl
    | k+30 => omega

theorem execute_trapped_output (i : Values Input) (raw : Values Register)
    (hr : i reset = 0) (hp : raw phase = 2) (origin : RV32I.Semantics.State)
    (value : RV32I.Word) (trap : RV32I.Semantics.Trap)
    (he : RV32I.Semantics.step (arch raw) (raw instruction) = .trapped origin value trap) (o : Output b) :
    circuit.observe i raw o = outputValues i ⟨arch raw,.execute (raw instruction)⟩ o := by
  obtain ⟨_, hc, hs, hw⟩ := RV32I.ExecuteCircuit.step_trap_projection (arch raw) (raw instruction) origin value trap he
  subst origin
  subst value
  cases trap
  all_goals try simp [RV32I.ExecuteCircuit.project] at hc
  all_goals
    rcases o with ⟨⟨k,hk⟩⟩
    have bound : k < 30 := hk
    match k with
    | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 |
      15 | 16 | 17 | 18 | 19 | 20 | 21 | 22 | 23 | 24 | 25 | 26 | 27 | 28 | 29 =>
        execute_output_simp
        all_goals rfl
    | k+30 => omega

theorem execute_output (i : Values Input) (raw : Values Register)
    (hr : i reset = 0) (hp : raw phase = 2) (o : Output b) :
    circuit.observe i raw o = outputValues i ⟨arch raw,.execute (raw instruction)⟩ o := by
  cases he : RV32I.Semantics.step (arch raw) (raw instruction) with
  | retired context after => exact execute_retired_output i raw hr hp context after he o
  | pending p => exact execute_pending_output i raw hr hp p he o
  | trapped origin value trap => exact execute_trapped_output i raw hr hp origin value trap he o

theorem output_represents (i : Values Input) (raw : Values Register)
    (state : CoreModel.State) (h : Represents raw state) (_hv : CoreModel.Valid state) (o : Output b) :
    circuit.observe i raw o = CoreInterface.outputValues i state o := by
  rcases BitVec.eq_zero_or_eq_one (i reset) with hr | hr
  · rcases state with ⟨a,p⟩
    rcases h with ⟨ha,hp⟩
    dsimp only at ha hp
    subst a
    cases p with
    | fetchRequest => exact fetch_request_output i raw hr hp o
    | fetchResponse => exact fetch_response_output i raw hr hp o
    | execute value =>
      rcases hp with ⟨hp,hw⟩
      subst value
      exact execute_output i raw hr hp o
    | dataRequest q =>
      rcases hp with ⟨hp,hs,hw,hi⟩
      cases q with
      | load c op dest address =>
        simpa using data_load_output i raw 3 hr hp (Or.inl rfl) c op dest address hs hw hi o
      | store c op address operand =>
        simpa using data_store_output i raw 3 hr hp (Or.inl rfl) c op address operand hs hw hi o
    | dataResponse q =>
      rcases hp with ⟨hp,hs,hw,hi⟩
      cases q with
      | load c op dest address =>
        simpa using data_load_output i raw 4 hr hp (Or.inr rfl) c op dest address hs hw hi o
      | store c op address operand =>
        simpa using data_store_output i raw 4 hr hp (Or.inr rfl) c op address operand hs hw hi o
    | fence c =>
      rcases hp with ⟨hp,hs,hw,hi⟩
      exact fence_output i raw c hr hp hs hw hi o
    | terminal f => exact terminal_output i raw f hr ⟨rfl,hp⟩ o
  · exact reset_output_eq i raw state hr o

/-- Every actual output matches the typed cycle specification on valid raw
states. Inactive retained metadata is admitted by the existing projection. -/
theorem output_eq (i : Values Input) (raw : Values Register) (h : Valid raw) (o : Output b) :
    circuit.observe i raw o = CoreInterface.spec.observe i (view raw) o := by
  obtain ⟨state, hv, hr⟩ := h
  rw [view_of_represents raw state hr]
  exact output_represents i raw state hr hv o

end Pinwheel.Hardware.Processor.CoreCircuit
