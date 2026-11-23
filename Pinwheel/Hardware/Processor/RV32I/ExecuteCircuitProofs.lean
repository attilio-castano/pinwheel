import Pinwheel.Hardware.Processor.RV32I.ExecuteCircuit

namespace Pinwheel.Hardware.Processor.RV32I.ExecuteCircuit

set_option backward.isDefEq.respectTransparency false

@[simp] theorem values_ofValues (v : Values Field) (field : Field b) :
    (Result.ofValues v).values field = v field := by cases field <;> rfl

@[simp] theorem ofValues_values (r : Result) : Result.ofValues r.values = r := by cases r; rfl

theorem result_ext (a b : Result) (h : ∀ {n} (field : Field n), a.values field = b.values field) : a = b := by
  have hv : @a.values = @b.values := funext fun n => funext fun field => h field
  have he := congrArg (fun (v : Values Field) => Result.ofValues v) hv
  simpa using he

theorem bool_beq (x y : BitVec n) : (x == y) = decide (x = y) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, decide_eq_true_eq]

theorem bool_decide_one (p : Prop) [Decidable p] : BitVec.ofBool (decide p) = (1#1) ↔ p := by
  change BitVec.ofBool (decide p) = BitVec.ofBool true ↔ p
  simp only [BitVec.ofBool_eq_iff_eq, decide_eq_true_eq]

@[simp] theorem retireExpr_eval (pc : Expr I R 32) (dest : Expr I R 5) (data : Expr I R 32)
    (i : Values I) (s : Values R) (field : Field b) :
    (retireExpr pc dest data field).eval i s = (retired (pc.eval i s) (dest.eval i s) (data.eval i s)).values field := by
  cases field <;> simp [retireExpr, retired, Result.values, Expr.eval, bool_decide_one, bne, bool_beq]

@[simp] theorem trapExpr_eval (cause : BitVec 2) (target : Expr I R 32)
    (i : Values I) (s : Values R) (field : Field b) :
    (trapExpr cause target field).eval i s = (trapped cause (target.eval i s)).values field := by
  cases field <;> rfl

@[simp] theorem loadExpr_eval (op : LoadOp) (dest : Expr I R 5) (address : Expr I R 32)
    (i : Values I) (s : Values R) (field : Field b) :
    (loadExpr op dest address field).eval i s = (loading op (dest.eval i s) (address.eval i s)).values field := by
  cases field <;> rfl

@[simp] theorem storeExpr_eval (op : StoreOp) (address data : Expr I R 32)
    (i : Values I) (s : Values R) (field : Field b) :
    (storeExpr op address data field).eval i s = (storing op (address.eval i s) (data.eval i s)).values field := by
  cases field <;> rfl

@[simp] theorem constant_eval (value : Result) (i : Values I) (s : Values R) (field : Field b) :
    (constant value field).eval i s = value.values field := rfl

@[simp] theorem mux_eval (condition : Expr I R 1) (yes no : Bundle I R)
    (i : Values I) (s : Values R) (field : Field b) :
    (mux condition yes no field).eval i s =
      if condition.eval i s = 1 then (yes field).eval i s else (no field).eval i s := rfl

theorem low_two_zero (target : Word) : target.extractLsb' 0 2 = (0#2) ↔ target.toNat % 4 = 0 := by
  rw [← BitVec.toNat_inj]
  rfl

def jumping (target link : Word) (dest : Register) : Result :=
  if target.toNat % 4 = 0 then retired target dest link else trapped 3 target

@[simp] theorem jumpExpr_eval (target link : Expr I R 32) (dest : Expr I R 5)
    (i : Values I) (s : Values R) (field : Field b) :
    (jumpExpr target link dest field).eval i s =
      (jumping (target.eval i s) (link.eval i s) (dest.eval i s)).values field := by
  by_cases h : (target.eval i s).toNat % 4 = 0
  · simp [jumpExpr, jumping, mux_eval, Expr.eval, low_two_zero, h]
  · simp [jumpExpr, jumping, mux_eval, Expr.eval, low_two_zero, h]

@[simp] theorem branchExpr_eval (op : BranchOp) (left right : Expr I R 32)
    (i : Values I) (s : Values R) :
    (branchExpr op left right).eval i s = BitVec.ofBool (Semantics.branchTaken op (left.eval i s) (right.eval i s)) := by
  cases op <;> simp [branchExpr, Semantics.branchTaken, Semantics.signedLess, Expr.eval,
    BitVec.slt, BitVec.ult, bool_beq, bne]

def evaluate (instruction : Instruction) (pc left right : Word) : Result :=
  let next := pc+4
  match instruction with
  | .lui dest bits => retired next dest (upperImmediate bits)
  | .auipc dest bits => retired next dest (pc+upperImmediate bits)
  | .jal dest bits => jumping (pc+jumpOffset bits) next dest
  | .jalr dest _ bits => jumping (Semantics.jalrTarget left bits) next dest
  | .branch op _ _ bits =>
      if Semantics.branchTaken op left right then jumping (pc+branchOffset bits) 0 0 else retired next 0 0
  | .load op dest _ bits => loading op dest (left+signedImmediate bits)
  | .store op _ _ bits => storing op (left+signedImmediate bits) right
  | .aluImm op dest _ bits => retired next dest (Semantics.immediateALU op left bits)
  | .shiftImm op dest _ amount => retired next dest (Semantics.shift op left amount)
  | .aluReg op dest _ _ => retired next dest (Semantics.registerALU op left right)
  | .fence _ _ _ _ _ => fencing
  | .ecall => trapped 1
  | .ebreak => trapped 2

theorem project_written (context : Semantics.Context) (dest : Register) (pc data : Word)
    (hd : DecodeCircuit.instructionRd context.instruction = dest) :
    project (.retired context ⟨pc, Semantics.write context.state.registers dest data⟩) = retired pc dest data := by
  simp only [project, hd]
  by_cases hz : dest = 0
  · simp [retired, hz]
  · simp [Semantics.read_write_same _ _ _ hz]

theorem project_no_write (context : Semantics.Context) (pc : Word)
    (hd : DecodeCircuit.instructionRd context.instruction = 0) :
    project (.retired context ⟨pc, context.state.registers⟩) = retired pc 0 0 := by
  simp [project, hd, retired]

theorem project_transfer (context : Semantics.Context) (dest : Register) (target : Word)
    (hd : DecodeCircuit.instructionRd context.instruction = dest) :
    project (Semantics.transfer context target (some dest)) = jumping target (context.state.pc+4) dest := by
  by_cases ha : target.toNat % 4 = 0
  · simpa [Semantics.transfer, jumping, ha] using project_written context dest target (context.state.pc+4) hd
  · simp [Semantics.transfer, jumping, ha, project]

theorem project_branch_transfer (context : Semantics.Context) (target : Word)
    (hd : DecodeCircuit.instructionRd context.instruction = 0) :
    project (Semantics.transfer context target none) = jumping target 0 0 := by
  by_cases ha : target.toNat % 4 = 0
  · simpa [Semantics.transfer, jumping, ha] using project_no_write context target hd
  · simp [Semantics.transfer, jumping, ha, project]

/-- Source operands are read before any architectural write, including rd=rs1
or rd=rs2. The pure row specification is derived from the actual Semantics
outcome, rather than replacing the instruction semantics as the contract. -/
theorem evaluate_semantics (context : Semantics.Context) :
    evaluate context.instruction context.state.pc
      (Semantics.read context.state.registers (DecodeCircuit.instructionRs1 context.instruction))
      (Semantics.read context.state.registers (DecodeCircuit.instructionRs2 context.instruction)) =
      project (Semantics.executeContext context) := by
  cases hi : context.instruction <;> simp only [evaluate, Semantics.executeContext, hi,
    DecodeCircuit.instructionRs1, DecodeCircuit.instructionRs2]
  all_goals try exact (project_written context _ _ _ (by simp [hi, DecodeCircuit.instructionRd])).symm
  all_goals try exact (project_transfer context _ _ (by simp [hi, DecodeCircuit.instructionRd])).symm
  all_goals try rfl
  split
  · exact (project_branch_transfer context _ (by simp [hi, DecodeCircuit.instructionRd])).symm
  · exact (project_no_write context _ (by simp [hi, DecodeCircuit.instructionRd])).symm

@[simp] theorem immediateExpr_eval (word : Expr I R 32) (kind : DecodeCircuit.Kind)
    (i : Values I) (s : Values R) :
    (DecodeCircuit.immediateExpr word kind).eval i s =
      (DecodeCircuit.construct kind (word.eval i s)).immediate.getD 0 :=
  DecodeCircuit.fieldExpr_eval word kind .immediate i s

theorem bool_one (v : Bool) : BitVec.ofBool v = (1#1) ↔ v = true := by
  cases v <;> decide

@[simp] theorem row_eval (word pc left right : Expr I R 32) (kind : DecodeCircuit.Kind)
    (i : Values I) (s : Values R) (field : Field b) :
    (row word pc left right kind field).eval i s =
      (evaluate (DecodeCircuit.construct kind (word.eval i s))
        (pc.eval i s) (left.eval i s) (right.eval i s)).values field := by
  cases kind <;> simp only [row, retireExpr_eval, jumpExpr_eval, mux_eval,
    loadExpr_eval, storeExpr_eval, trapExpr_eval, constant_eval, ALU.immediate_eval,
    ALU.shiftImmediate_eval, ALU.register_eval, WordOps.add_eval, immediateExpr_eval,
    branchExpr_eval, DecodeCircuit.construct, evaluate, Instruction.immediate,
    Option.getD_some, Expr.eval]
  all_goals try simp only [rd, iBits, rs2, Semantics.jalrTarget]
  all_goals split <;> simp_all [bool_one]

/-- Total interpretation of arbitrary runtime operands; operand coherence with
an architectural register file is required only by `bundle_semantics`. -/
def expected (word pc left right : Word) : Result :=
  match decode word with
  | none => trapped 0
  | some instruction => evaluate instruction pc left right

@[simp] theorem bundle_eval (word pc left right : Expr I R 32)
    (i : Values I) (s : Values R) (field : Field b) :
    (bundle word pc left right field).eval i s =
      (expected (word.eval i s) (pc.eval i s) (left.eval i s) (right.eval i s)).values field := by
  cases hd : decode (word.eval i s) with
  | none => simp [bundle, Expr.eval, DecodeCircuit.bundle_eval, DecodeCircuit.expected, hd, expected]
  | some instruction =>
      simp only [bundle, Expr.eval, DecodeCircuit.bundle_eval, DecodeCircuit.expected, hd,
        DecodeCircuit.fields, ↓reduceIte, expected]
      rw [DecodeCircuit.select_some word _ DecodeCircuit.kinds i s instruction hd (DecodeCircuit.kind_mem _),
        row_eval, (DecodeCircuit.decoded_kind _ _ hd).2]

/-- The two operand pins are the pre-edge reads of the decoder's source indices.
Inactive decoded source indices are zero; FENCE's retained fields are harmless
because the execution row never uses their values. -/
def Operands (state : Semantics.State) (word left right : Word) : Prop :=
  left = Semantics.read state.registers (DecodeCircuit.expected word .rs1) ∧
  right = Semantics.read state.registers (DecodeCircuit.expected word .rs2)

theorem expected_semantics (state : Semantics.State) (word left right : Word)
    (h : Operands state word left right) :
    expected word state.pc left right = project (Semantics.step state word) := by
  cases hd : decode word with
  | none => rw [Semantics.step_illegal _ _ hd]; simp [expected, hd, project]
  | some instruction =>
      have hl := h.1
      have hr := h.2
      simp only [DecodeCircuit.expected, hd, DecodeCircuit.fields] at hl hr
      rw [expected, hd, hl, hr, Semantics.step_decoded _ _ _ hd]
      exact evaluate_semantics ⟨state, word, instruction, hd⟩

theorem bundle_semantics (word pc left right : Expr I R 32) (state : Semantics.State)
    (i : Values I) (s : Values R) (hp : pc.eval i s = state.pc)
    (ho : Operands state (word.eval i s) (left.eval i s) (right.eval i s)) (field : Field b) :
    (bundle word pc left right field).eval i s =
      (project (Semantics.step state (word.eval i s))).values field := by
  rw [bundle_eval, hp, expected_semantics _ _ _ _ ho]

theorem circuit_correct (i : Values Input) (s : Values NoRegisters)
    (state : Semantics.State) (hp : i .pc = state.pc)
    (ho : Operands state (i .instruction) (i .operand1) (i .operand2)) (field : Field b) :
    circuit.observe i s field = (project (Semantics.step state (i .instruction))).values field :=
  bundle_semantics (.input Input.instruction) (.input Input.pc) (.input Input.operand1) (.input Input.operand2) state i s hp ho field

/-- All raw input combinations produce one of the five specified result shapes. -/
def Canonical (r : Result) : Prop :=
  (∃ pc dest data, r = retired pc dest data) ∨
  (∃ op dest address, r = loading op dest address) ∨
  (∃ op address data, r = storing op address data) ∨
  r = fencing ∨ (∃ cause target, r = trapped cause target)

theorem jumping_canonical (target link : Word) (dest : Register) : Canonical (jumping target link dest) := by
  unfold jumping
  split
  · exact Or.inl ⟨_, _, _, rfl⟩
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨_, _, rfl⟩)))

theorem evaluate_canonical (instruction : Instruction) (pc left right : Word) :
    Canonical (evaluate instruction pc left right) := by
  cases instruction <;> simp only [evaluate]
  all_goals first
    | exact Or.inl ⟨_, _, _, rfl⟩
    | exact jumping_canonical _ _ _
    | exact Or.inr (Or.inl ⟨_, _, _, rfl⟩)
    | exact Or.inr (Or.inr (Or.inl ⟨_, _, _, rfl⟩))
    | exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
    | exact Or.inr (Or.inr (Or.inr (Or.inr ⟨_, _, rfl⟩)))
    | split
      · exact jumping_canonical _ _ _
      · exact Or.inl ⟨_, _, _, rfl⟩

theorem expected_canonical (word pc left right : Word) : Canonical (expected word pc left right) := by
  unfold expected
  split
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨_, _, rfl⟩)))
  · exact evaluate_canonical _ _ _ _

/-- Inactive-class and disabled-write constraints, independent of register-file
coherence. `bundle_trap_target_zero` also clears targets of non-address traps. -/
def InactiveZero (r : Result) : Prop :=
  (r.classification ≠ 0 → r.nextPC = 0 ∧ r.writeEnable = 0) ∧
  (r.writeEnable = 0 → r.writeRd = 0 ∧ r.writeData = 0) ∧
  (r.classification ≠ 1 → r.signedLoad = 0 ∧ r.loadRd = 0) ∧
  (r.classification ≠ 2 → r.storeData = 0) ∧
  (r.classification ≠ 1 → r.classification ≠ 2 → r.address = 0 ∧ r.size = 0) ∧
  (r.classification ≠ 4 → r.trapCause = 0 ∧ r.trapTarget = 0)

theorem canonical_class (r : Result) (h : Canonical r) : r.classification.toNat ≤ 4 := by
  rcases h with ⟨pc, dest, data, rfl⟩ | ⟨op, dest, address, rfl⟩ |
    ⟨op, address, data, rfl⟩ | rfl | ⟨cause, target, rfl⟩ <;> simp [retired, loading, storing, fencing, trapped]

theorem canonical_inactive (r : Result) (h : Canonical r) : InactiveZero r := by
  rcases h with ⟨pc, dest, data, rfl⟩ | ⟨op, dest, address, rfl⟩ |
    ⟨op, address, data, rfl⟩ | rfl | ⟨cause, target, rfl⟩ <;>
    simp [InactiveZero, retired, loading, storing, fencing, trapped, bne, bool_beq]
  by_cases hz : dest = (0#5) <;> simp [hz]

theorem bundle_class (word pc left right : Expr I R 32) (i : Values I) (s : Values R) :
    ((bundle word pc left right .classification).eval i s).toNat ≤ 4 := by
  rw [bundle_eval]
  exact canonical_class _ (expected_canonical _ _ _ _)

theorem bundle_inactive (word pc left right : Expr I R 32) (i : Values I) (s : Values R) :
    InactiveZero (Result.ofValues (fun field => (bundle word pc left right field).eval i s)) := by
  simp only [bundle_eval, ofValues_values]
  exact canonical_inactive _ (expected_canonical _ _ _ _)

/-- Decode the actual class, size, sign and operand fields as a memory/fence
intent. This never substitutes an expected semantic response or request. -/
def Result.intent (r : Result) : Option Semantics.Intent :=
  if r.classification = 3 then some .fenceAll
  else match Memory.ByteAccess.decodeSize r.size with
    | .error _ => none
    | .ok size =>
        if r.classification = 1 then some (.load r.address size (r.signedLoad == 1))
        else if r.classification = 2 then some (.store r.address size r.storeData)
        else none

/-- Precise traps recoverable from combinational result pins. Data and fetch
faults are produced by the later controller, not this datapath. -/
def Result.executionTrap (r : Result) : Option Semantics.Trap :=
  if r.classification = 4 then
    if r.trapCause = 0 then some .illegalInstruction
    else if r.trapCause = 1 then some .environmentCall
    else if r.trapCause = 2 then some .breakpoint
    else some (.instructionAddressMisaligned r.trapTarget)
  else none

/-- Apply actual write-enable/register/data and next-PC pins at a caller-owned
immediate retirement edge. Calling this on a pending or trap result is invalid. -/
def Result.commit (r : Result) (before : Semantics.State) : Semantics.State :=
  ⟨r.nextPC, if r.writeEnable = 1 then Semantics.write before.registers r.writeRd r.writeData else before.registers⟩

@[simp] theorem commit_retired (before : Semantics.State) (pc : Word) (dest : Register) (data : Word) :
    (retired pc dest data).commit before = ⟨pc, Semantics.write before.registers dest data⟩ := by
  by_cases hz : dest = (0#5) <;> simp [Result.commit, retired, hz, bne, bool_beq]
  exact (Semantics.write_zero _ _).symm

@[simp] theorem pending_intent (p : Semantics.Pending) : (project (.pending p)).intent = some p.intent := by
  cases p with
  | load context op dest address => cases op <;> rfl
  | store context op address data => cases op <;> rfl
  | fence context => rfl

/-- The complete pending result, including the x0 load destination. -/
theorem pending_projection (p : Semantics.Pending) :
    project (.pending p) = match p with
      | .load _ op dest address => loading op dest address
      | .store _ op address data => storing op address data
      | .fence _ => fencing := by cases p <;> rfl

/-- Complete output snapshot from the stateless typed circuit. -/
def observeResult (i : Values Input) (s : Values NoRegisters) : Result :=
  Result.ofValues (circuit.observe i s)

theorem observeResult_semantics (i : Values Input) (s : Values NoRegisters)
    (state : Semantics.State) (hp : i .pc = state.pc)
    (ho : Operands state (i .instruction) (i .operand1) (i .operand2)) :
    observeResult i s = project (Semantics.step state (i .instruction)) := by
  apply result_ext
  intro b field
  simpa only [observeResult, values_ofValues] using circuit_correct i s state hp ho field

theorem circuit_pending (i : Values Input) (s : Values NoRegisters)
    (state : Semantics.State) (hp : i .pc = state.pc)
    (ho : Operands state (i .instruction) (i .operand1) (i .operand2))
    (p : Semantics.Pending) (h : Semantics.step state (i .instruction) = .pending p) :
    observeResult i s = project (.pending p) ∧
      (observeResult i s).intent = some p.intent ∧
      (observeResult i s).nextPC = 0 ∧ (observeResult i s).writeEnable = 0 := by
  rw [observeResult_semantics i s state hp ho, h]
  refine ⟨rfl, pending_intent p, ?_⟩
  cases p <;> exact ⟨rfl, rfl⟩

/-- Immediate retirement reconstructs the entire architectural state, not only
its destination register or PC. This excludes hidden writes to other registers. -/
def RetirementFaithful (before : Semantics.State) : Semantics.Outcome → Prop
  | .retired context after => (project (.retired context after)).commit before = after
  | _ => True

theorem written_faithful (context : Semantics.Context) (dest : Register) (pc data : Word)
    (hd : DecodeCircuit.instructionRd context.instruction = dest) :
    RetirementFaithful context.state (.retired context ⟨pc, Semantics.write context.state.registers dest data⟩) := by
  change (project _).commit _ = _
  rw [project_written _ _ _ _ hd, commit_retired]

theorem unwritten_faithful (context : Semantics.Context) (pc : Word)
    (hd : DecodeCircuit.instructionRd context.instruction = 0) :
    RetirementFaithful context.state (.retired context ⟨pc, context.state.registers⟩) := by
  change (project _).commit _ = _
  rw [project_no_write _ _ hd, commit_retired, Semantics.write_zero]

theorem transfer_faithful (context : Semantics.Context) (target : Word) (link : Option Register)
    (hd : DecodeCircuit.instructionRd context.instruction = link.getD 0) :
    RetirementFaithful context.state (Semantics.transfer context target link) := by
  unfold Semantics.transfer
  split
  · cases link with
    | none => exact unwritten_faithful context target hd
    | some dest => exact written_faithful context dest target (context.state.pc+4) hd
  · trivial

theorem execute_faithful (context : Semantics.Context) :
    RetirementFaithful context.state (Semantics.executeContext context) := by
  cases hi : context.instruction <;> simp only [Semantics.executeContext, hi]
  all_goals first
    | exact written_faithful context _ _ _ (by simp [hi, DecodeCircuit.instructionRd])
    | exact transfer_faithful context _ _ (by simp [hi, DecodeCircuit.instructionRd])
    | trivial
    | split
      · exact transfer_faithful context _ _ (by simp [hi, DecodeCircuit.instructionRd])
      · exact unwritten_faithful context _ (by simp [hi, DecodeCircuit.instructionRd])

theorem step_faithful (state : Semantics.State) (word : Word) :
    RetirementFaithful state (Semantics.step state word) := by
  cases hd : decode word with
  | none => rw [Semantics.step_illegal _ _ hd]; trivial
  | some instruction =>
      rw [Semantics.step_decoded _ _ _ hd]
      exact execute_faithful ⟨state, word, instruction, hd⟩

theorem circuit_retirement (i : Values Input) (s : Values NoRegisters)
    (state : Semantics.State) (hp : i .pc = state.pc)
    (ho : Operands state (i .instruction) (i .operand1) (i .operand2))
    (context : Semantics.Context) (after : Semantics.State)
    (h : Semantics.step state (i .instruction) = .retired context after) :
    (observeResult i s).classification = 0 ∧ (observeResult i s).commit state = after := by
  rw [observeResult_semantics i s state hp ho, h]
  refine ⟨rfl, ?_⟩
  have hf := step_faithful state (i .instruction)
  rw [h] at hf
  exact hf

theorem step_project_canonical (state : Semantics.State) (word : Word) :
    Canonical (project (Semantics.step state word)) := by
  rw [← expected_semantics state word
    (Semantics.read state.registers (DecodeCircuit.expected word .rs1))
    (Semantics.read state.registers (DecodeCircuit.expected word .rs2)) ⟨rfl, rfl⟩]
  exact expected_canonical _ _ _ _

theorem step_trap_projection (state : Semantics.State) (word : Word)
    (unchanged : Semantics.State) (raw : Word) (trap : Semantics.Trap)
    (h : Semantics.step state word = .trapped unchanged raw trap) :
    (project (.trapped unchanged raw trap)).executionTrap = some trap ∧
    (project (.trapped unchanged raw trap)).classification = 4 ∧
    unchanged = state ∧ raw = word := by
  have hc := canonical_class _ (step_project_canonical state word)
  rw [h] at hc
  have hs := Semantics.step_origin state word
  have hw := Semantics.step_word state word
  rw [h] at hs hw
  cases trap <;> simp_all [project, trapped, Result.executionTrap, Semantics.Outcome.origin, Semantics.Outcome.word]

theorem circuit_trap (i : Values Input) (s : Values NoRegisters)
    (state : Semantics.State) (hp : i .pc = state.pc)
    (ho : Operands state (i .instruction) (i .operand1) (i .operand2))
    (unchanged : Semantics.State) (raw : Word) (trap : Semantics.Trap)
    (h : Semantics.step state (i .instruction) = .trapped unchanged raw trap) :
    (observeResult i s).executionTrap = some trap ∧
    (observeResult i s).classification = 4 ∧
    (observeResult i s).nextPC = 0 ∧ (observeResult i s).writeEnable = 0 ∧
    unchanged = state ∧ raw = i .instruction := by
  have ht := step_trap_projection state (i .instruction) unchanged raw trap h
  have hz := canonical_inactive _ (step_project_canonical state (i .instruction))
  rw [h] at hz
  rw [observeResult_semantics i s state hp ho, h]
  exact ⟨ht.1, ht.2.1, (hz.1 (by rw [ht.2.1]; decide)).1,
    (hz.1 (by rw [ht.2.1]; decide)).2, ht.2.2⟩

/-- Load destination is recovered directly from the actual output field,
including x0: zero never converts a load into an immediate retirement. -/
theorem circuit_load (i : Values Input) (s : Values NoRegisters)
    (state : Semantics.State) (hp : i .pc = state.pc)
    (ho : Operands state (i .instruction) (i .operand1) (i .operand2))
    (context : Semantics.Context) (op : LoadOp) (dest : Register) (address : Word)
    (h : Semantics.step state (i .instruction) = .pending (.load context op dest address)) :
    observeResult i s = loading op dest address ∧
    (observeResult i s).loadRd = dest ∧ (observeResult i s).classification = 1 := by
  rw [observeResult_semantics i s state hp ho, h]
  exact ⟨rfl, rfl, rfl⟩

/-- Binding the expression bundle into a larger datapath preserves its exact
raw-word interpretation for arbitrary input and register substitutions. -/
theorem bundle_bind_eval (word pc left right : Expr I R 32)
    (inputs : ∀ {n}, I n → Expr J S n) (registers : ∀ {n}, R n → Expr J S n)
    (i : Values J) (s : Values S) (field : Field b) :
    ((bundle word pc left right field).bind inputs registers).eval i s =
      (expected ((word.bind inputs registers).eval i s) ((pc.bind inputs registers).eval i s)
        ((left.bind inputs registers).eval i s) ((right.bind inputs registers).eval i s)).values field := by
  simp only [Expr.eval_bind, bundle_eval]

/-- Classification is exact in both directions, so a controller can branch on
actual pins without inventing a retirement or suppressing an outstanding load. -/
theorem project_retire_iff (outcome : Semantics.Outcome) :
    (project outcome).classification = 0 ↔ ∃ context after, outcome = .retired context after := by
  cases outcome with
  | retired context after => simp [project, retired]
  | pending pending => cases pending <;> simp [project, loading, storing, fencing]
  | trapped state word trap => cases trap <;> simp [project, trapped]

theorem project_load_iff (outcome : Semantics.Outcome) :
    (project outcome).classification = 1 ↔
      ∃ context op dest address, outcome = .pending (.load context op dest address) := by
  cases outcome with
  | retired context after => simp [project, retired]
  | pending pending => cases pending <;> simp [project, loading, storing, fencing]
  | trapped state word trap => cases trap <;> simp [project, trapped]

theorem project_store_iff (outcome : Semantics.Outcome) :
    (project outcome).classification = 2 ↔
      ∃ context op address data, outcome = .pending (.store context op address data) := by
  cases outcome with
  | retired context after => simp [project, retired]
  | pending pending => cases pending <;> simp [project, loading, storing, fencing]
  | trapped state word trap => cases trap <;> simp [project, trapped]

theorem project_fence_iff (outcome : Semantics.Outcome) :
    (project outcome).classification = 3 ↔ ∃ context, outcome = .pending (.fence context) := by
  cases outcome with
  | retired context after => simp [project, retired]
  | pending pending => cases pending <;> simp [project, loading, storing, fencing]
  | trapped state word trap => cases trap <;> simp [project, trapped]

theorem evaluate_trap_target_zero (instruction : Instruction) (pc left right : Word) :
    (evaluate instruction pc left right).trapCause ≠ 3 → (evaluate instruction pc left right).trapTarget = 0 := by
  cases instruction <;> simp only [evaluate]
  all_goals try simp [retired, loading, storing, fencing, trapped]
  all_goals unfold jumping
  all_goals split <;> simp_all [retired, trapped]
  split <;> simp

theorem bundle_trap_target_zero (word pc left right : Expr I R 32) (i : Values I) (s : Values R) :
    (bundle word pc left right .trapCause).eval i s ≠ 3 →
      (bundle word pc left right .trapTarget).eval i s = 0 := by
  simp only [bundle_eval]
  unfold expected
  split
  · simp [Result.values, trapped]
  · exact evaluate_trap_target_zero _ _ _ _

end Pinwheel.Hardware.Processor.RV32I.ExecuteCircuit
