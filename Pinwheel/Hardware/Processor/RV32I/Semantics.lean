import Pinwheel.Hardware.Processor.RV32I.Decode
import Pinwheel.Hardware.Memory.ByteAccess

/-! Pure RV32I architectural operations, against the pinned unprivileged ISA
release 20260120 chapter 2. No physical CPU, fetch mechanism, RAM, MMIO device,
or EEI is implemented here. Instruction target checks follow §2.5 with IALIGN=32.
Current-PC fetch alignment/access must be checked before supplying the fetched
word; these operations describe instruction execution after that external step.
-/
namespace Pinwheel.Hardware.Processor.RV32I.Semantics

/-- Only x1..x31 have storage. No fabricated register state can change x0. -/
abbrev Registers := Fin 31 → Word

def read (registers : Registers) (index : Register) : Word :=
  if h : index.toNat = 0 then 0 else registers ⟨index.toNat-1, by have := index.isLt; omega⟩

def write (registers : Registers) (index : Register) (value : Word) : Registers :=
  fun k => if index.toNat = k.val+1 then value else registers k

@[simp] theorem read_zero (registers : Registers) : read registers 0 = 0 := by simp [read]

@[simp] theorem write_zero (registers : Registers) (value : Word) : write registers 0 value = registers := by
  funext k
  simp [write]

theorem read_write_same (registers : Registers) (index : Register) (value : Word) (h : index ≠ 0) :
    read (write registers index value) index = value := by
  have hn : index.toNat ≠ 0 := by intro hz; apply h; exact BitVec.eq_of_toNat_eq hz
  simp only [read, dif_neg hn, write]
  exact if_pos (by omega)

theorem read_write_other (registers : Registers) (dest source : Register) (value : Word) (h : source ≠ dest) :
    read (write registers dest value) source = read registers source := by
  by_cases hz : source.toNat = 0
  · simp [read, hz]
  · have hn : dest.toNat ≠ source.toNat-1+1 := by
      intro he
      apply h
      apply BitVec.eq_of_toNat_eq
      omega
    simp [read, write, hz, hn]

theorem write_overwrite (registers : Registers) (index : Register) (first second : Word) :
    write (write registers index first) index second = write registers index second := by
  funext k
  by_cases h : index.toNat = k.val+1 <;> simp [write, h]

structure State where
  pc : Word
  registers : Registers

def next (state : State) : State := {state with pc := state.pc+4}
def writeNext (state : State) (dest : Register) (value : Word) : State :=
  ⟨state.pc+4, write state.registers dest value⟩

def bit (test : Bool) : Word := if test then 1 else 0
def signedLess (left right : Word) : Bool := decide (left.toInt < right.toInt)

def immediateALU (op : ImmediateOp) (left : Word) (immediate : BitVec 12) : Word :=
  let right := signedImmediate immediate
  match op with
  | .add => left+right
  | .slt => bit (signedLess left right)
  | .sltu => bit (left.ult right)
  | .bitXor => left ^^^ right
  | .bitOr => left ||| right
  | .bitAnd => left &&& right

def shift (op : ShiftOp) (value : Word) (amount : BitVec 5) : Word :=
  match op with
  | .left => value <<< amount.toNat
  | .rightLogical => value >>> amount.toNat
  | .rightArithmetic => value.sshiftRight amount.toNat

def registerALU (op : RegisterOp) (left right : Word) : Word :=
  match op with
  | .add => left+right
  | .sub => left-right
  | .sll => shift .left left (right.extractLsb' 0 5)
  | .slt => bit (signedLess left right)
  | .sltu => bit (left.ult right)
  | .bitXor => left ^^^ right
  | .srl => shift .rightLogical left (right.extractLsb' 0 5)
  | .sra => shift .rightArithmetic left (right.extractLsb' 0 5)
  | .bitOr => left ||| right
  | .bitAnd => left &&& right

def branchTaken (op : BranchOp) (left right : Word) : Bool :=
  match op with
  | .eq => left == right
  | .ne => left != right
  | .lt => signedLess left right
  | .ge => !signedLess left right
  | .ltu => left.ult right
  | .geu => !left.ult right

structure Context where
  state : State
  word : Word
  instruction : Instruction
  decoded : decode word = some instruction

inductive MemoryFault where
  | misaligned | accessFault
  deriving DecidableEq, Repr

inductive Trap where
  | illegalInstruction
  | environmentCall
  | breakpoint
  | instructionAddressMisaligned (target : Word)
  | loadFault (reason : MemoryFault) (address : Word)
  | storeFault (reason : MemoryFault) (address : Word)
  deriving DecidableEq, Repr

def loadSize : LoadOp → Memory.ByteAccess.Size
  | .byte | .byteUnsigned => .byte
  | .half | .halfUnsigned => .half
  | .word => .word

def storeSize : StoreOp → Memory.ByteAccess.Size
  | .byte => .byte | .half => .half | .word => .word

def loadSigned : LoadOp → Bool
  | .byte | .half => true
  | _ => false

def loadValue (op : LoadOp) (data : Word) : Word :=
  match op with
  | .byte => (data.extractLsb' 0 8).signExtend 32
  | .half => (data.extractLsb' 0 16).signExtend 32
  | .word => data
  | .byteUnsigned => (data.extractLsb' 0 8).setWidth 32
  | .halfUnsigned => (data.extractLsb' 0 16).setWidth 32

/-- No memory access or device effect occurs in this datatype. The provider
must perform an access exactly when its response is accepted. A load reply
contains the selected bytes in its low bits; architectural extension is local.
Data alignment/access policy is left to the EEI, which can return precise faults.
-/
inductive Intent where
  | load (address : Word) (size : Memory.ByteAccess.Size) (signed : Bool)
  | store (address : Word) (size : Memory.ByteAccess.Size) (operand : Word)
  | fenceAll
  deriving DecidableEq, Repr

inductive Pending where
  | load (origin : Context) (op : LoadOp) (dest : Register) (address : Word)
  | store (origin : Context) (op : StoreOp) (address operand : Word)
  | fence (origin : Context)

def Pending.context : Pending → Context
  | .load origin _ _ _ | .store origin _ _ _ | .fence origin => origin

def Pending.intent : Pending → Intent
  | .load _ op _ address => .load address (loadSize op) (loadSigned op)
  | .store _ op address operand => .store address (storeSize op) operand
  | .fence _ => .fenceAll

/-- Reply kinds are indexed by the pending request. The interface cannot
acknowledge a store with load data or attach a memory fault to a fence. -/
inductive Reply : Pending → Type
  | loaded (data : Word) : Reply (.load origin op dest address)
  | stored : Reply (.store origin op address operand)
  | fenced : Reply (.fence origin)
  | loadFault (reason : MemoryFault) : Reply (.load origin op dest address)
  | storeFault (reason : MemoryFault) : Reply (.store origin op address operand)

inductive Outcome where
  | retired (origin : Context) (state : State)
  | pending (request : Pending)
  | trapped (state : State) (word : Word) (reason : Trap)

def Outcome.state : Outcome → State
  | .retired _ state | .trapped state _ _ => state
  | .pending request => request.context.state

def Outcome.origin : Outcome → State
  | .retired context _ => context.state
  | .pending request => request.context.state
  | .trapped state _ _ => state

def Outcome.word : Outcome → Word
  | .retired context _ => context.word
  | .pending request => request.context.word
  | .trapped _ word _ => word

def effectiveAddress (state : State) (base : Register) (immediate : BitVec 12) : Word :=
  read state.registers base + signedImmediate immediate

/-- The least significant bit is cleared before the IALIGN=32 target check. -/
def jalrTarget (base : Word) (immediate : BitVec 12) : Word :=
  (base + signedImmediate immediate) &&& 0xfffffffe

def transfer (context : Context) (target : Word) (link : Option Register) : Outcome :=
  if target.toNat % 4 = 0 then .retired context ⟨target,
    match link with | none => context.state.registers | some dest => write context.state.registers dest (context.state.pc+4)⟩
  else .trapped context.state context.word (.instructionAddressMisaligned target)

/-- Typed execution uses a coherent instruction context. Aligned target
accessibility is not checked here: any access fault belongs to a later fetch.
Untaken branches do not call `transfer`, so they cannot fault on their unused
target. FENCE conservatively requests fence-all acknowledgement; a serialized
implementation may discharge it locally after earlier accesses are complete,
without waiting for unrelated physical device activity such as UART transmission.
-/
def executeContext (context : Context) : Outcome :=
  let s := context.state
  match context.instruction with
  | .lui dest upper => .retired context (writeNext s dest (upperImmediate upper))
  | .auipc dest upper => .retired context (writeNext s dest (s.pc+upperImmediate upper))
  | .jal dest offset => transfer context (s.pc+jumpOffset offset) (some dest)
  | .jalr dest source immediate => transfer context (jalrTarget (read s.registers source) immediate) (some dest)
  | .branch op first second offset =>
    if branchTaken op (read s.registers first) (read s.registers second) then
      transfer context (s.pc+branchOffset offset) none else .retired context (next s)
  | .load op dest source immediate => .pending (.load context op dest (effectiveAddress s source immediate))
  | .store op first second immediate =>
    .pending (.store context op (effectiveAddress s first immediate) (read s.registers second))
  | .aluImm op dest source immediate => .retired context (writeNext s dest (immediateALU op (read s.registers source) immediate))
  | .shiftImm op dest source amount => .retired context (writeNext s dest (shift op (read s.registers source) amount))
  | .aluReg op dest first second =>
    .retired context (writeNext s dest (registerALU op (read s.registers first) (read s.registers second)))
  | .fence _ _ _ _ _ => .pending (.fence context)
  | .ecall => .trapped s context.word .environmentCall
  | .ebreak => .trapped s context.word .breakpoint

def execute (state : State) (instruction : Instruction) : Outcome :=
  executeContext ⟨state, encode instruction, instruction, decode_encode instruction⟩

/-- Controller refinement must retain this issuance invariant: a fabricated
Pending value is kind-correct but its address/operand need not come from the
decoded instruction. Context alone proves only raw-word decoding coherence. -/
def Pending.Issued (pending : Pending) : Prop := executeContext pending.context = .pending pending

def step (state : State) (word : Word) : Outcome :=
  match hd : decode word with
  | none => .trapped state word .illegalInstruction
  | some instruction => executeContext ⟨state, word, instruction, hd⟩

/-- Call only on accepted response edges, or use `respond` below. Retirement
and writeback occur on the same edge as the provider's acknowledged effect. -/
def finish : (pending : Pending) → Reply pending → Outcome
  | .load origin op dest _, .loaded data => .retired origin (writeNext origin.state dest (loadValue op data))
  | .store origin _ _ _, .stored => .retired origin (next origin.state)
  | .fence origin, .fenced => .retired origin (next origin.state)
  | .load origin _ _ address, .loadFault reason => .trapped origin.state origin.word (.loadFault reason address)
  | .store origin _ address _, .storeFault reason => .trapped origin.state origin.word (.storeFault reason address)

def respond (pending : Pending) (ready : Bool) (offered : Option (Reply pending)) : Outcome :=
  match offered with
  | some reply => if ready then finish pending reply else .pending pending
  | none => .pending pending

@[simp] theorem outcome_x0 (outcome : Outcome) : read outcome.state.registers 0 = 0 := read_zero _
@[simp] theorem writeNext_pc (state : State) (dest : Register) (value : Word) :
    (writeNext state dest value).pc = state.pc+4 := rfl

theorem writeNext_other (state : State) (dest source : Register) (value : Word) (h : source ≠ dest) :
    read (writeNext state dest value).registers source = read state.registers source :=
  read_write_other _ _ _ _ h

theorem transfer_misaligned (context : Context) (target : Word) (link : Option Register)
    (h : target.toNat % 4 ≠ 0) :
    transfer context target link = .trapped context.state context.word (.instructionAddressMisaligned target) := by
  simp [transfer, h]

theorem transfer_aligned_pc (context : Context) (target : Word) (link : Option Register)
    (h : target.toNat % 4 = 0) : (transfer context target link).state.pc = target := by
  simp [transfer, h, Outcome.state]

theorem transfer_misaligned_no_link (context : Context) (target : Word) (dest : Register)
    (h : target.toNat % 4 ≠ 0) : (transfer context target (some dest)).state = context.state := by
  rw [transfer_misaligned context target (some dest) h]
  rfl

theorem branch_untaken (context : Context) (op : BranchOp) (first second : Register) (offset : BitVec 12)
    (hi : context.instruction = .branch op first second offset)
    (ht : branchTaken op (read context.state.registers first) (read context.state.registers second) = false) :
    executeContext context = .retired context (next context.state) := by simp [executeContext, hi, ht]

theorem jalr_clears_bit_zero (base : Word) (immediate : BitVec 12) :
    (jalrTarget base immediate).getLsbD 0 = false := by simp [jalrTarget]

theorem jalr_low_two (base : Word) (immediate : BitVec 12) :
    (jalrTarget base immediate).extractLsb' 0 2 =
      (base+signedImmediate immediate).extractLsb' 0 2 &&& 2 := BitVec.extractLsb'_and

/-- Sums ending in 00 or 01 both reach an aligned target; sums ending in 10 or
11 both fault. Thus bit zero is cleared before, rather than after, alignment. -/
theorem jalr_alignment (base : Word) (immediate : BitVec 12) :
    (jalrTarget base immediate).toNat % 4 = 0 ↔
      (base+signedImmediate immediate).toNat % 4 < 2 := by
  change ((jalrTarget base immediate).extractLsb' 0 2).toNat = 0 ↔
    ((base+signedImmediate immediate).extractLsb' 0 2).toNat < 2
  rw [jalr_low_two]
  rcases Memory.ByteAccess.raw_cases ((base+signedImmediate immediate).extractLsb' 0 2) with h | h | h | h
  all_goals simp [h]

@[simp] theorem transfer_origin (context : Context) (target : Word) (link : Option Register) :
    (transfer context target link).origin = context.state := by
  by_cases h : target.toNat % 4 = 0 <;> simp [transfer, h, Outcome.origin]

@[simp] theorem transfer_word (context : Context) (target : Word) (link : Option Register) :
    (transfer context target link).word = context.word := by
  by_cases h : target.toNat % 4 = 0 <;> simp [transfer, h, Outcome.word]

theorem executeContext_origin (context : Context) : (executeContext context).origin = context.state := by
  cases hi : context.instruction <;> simp only [executeContext, hi]
  all_goals try rfl
  all_goals try exact transfer_origin _ _ _
  split
  · exact transfer_origin _ _ _
  · rfl

theorem executeContext_word (context : Context) : (executeContext context).word = context.word := by
  cases hi : context.instruction <;> simp only [executeContext, hi]
  all_goals try rfl
  all_goals try exact transfer_word _ _ _
  split
  · exact transfer_word _ _ _
  · rfl

theorem step_origin (state : State) (word : Word) : (step state word).origin = state := by
  unfold step
  split
  · rfl
  · exact executeContext_origin _

theorem step_word (state : State) (word : Word) : (step state word).word = word := by
  unfold step
  split
  · rfl
  · exact executeContext_word _

theorem step_pending_identity (state : State) (word : Word) (pending : Pending)
    (h : step state word = .pending pending) :
    pending.context.state = state ∧ pending.context.word = word ∧
      decode word = some pending.context.instruction := by
  have hs := step_origin state word
  have hw := step_word state word
  rw [h] at hs hw
  change pending.context.state = state at hs
  change pending.context.word = word at hw
  exact ⟨hs, hw, hw ▸ pending.context.decoded⟩

theorem execute_pending_context (context : Context) (pending : Pending)
    (h : executeContext context = .pending pending) : pending.context = context := by
  cases hi : context.instruction <;> simp only [executeContext, hi] at h
  all_goals try (cases h <;> rfl)
  all_goals unfold transfer at h
  all_goals repeat' first | (cases h <;> rfl) | split at h

theorem step_pending_issued (state : State) (word : Word) (pending : Pending)
    (h : step state word = .pending pending) : pending.Issued := by
  unfold step at h
  split at h
  · cases h
  · rename_i instruction hd
    have hc := execute_pending_context ⟨state, word, instruction, hd⟩ pending h
    unfold Pending.Issued
    rw [hc]
    exact h

theorem nonretired_no_update (outcome : Outcome)
    (h : ∀ context after, outcome ≠ .retired context after) : outcome.state = outcome.origin := by
  cases outcome with
  | retired context after => exact False.elim (h context after rfl)
  | pending request => rfl
  | trapped state word reason => rfl

theorem step_no_partial_update (state : State) (word : Word)
    (h : ∀ context after, step state word ≠ .retired context after) : (step state word).state = state := by
  rw [nonretired_no_update _ h, step_origin]

theorem step_illegal (state : State) (word : Word) (h : decode word = none) :
    step state word = .trapped state word .illegalInstruction := by
  unfold step
  split
  · rfl
  · rename_i instruction hd
    cases h.symm.trans hd

theorem step_decoded (state : State) (word : Word) (instruction : Instruction)
    (h : decode word = some instruction) : step state word = executeContext ⟨state, word, instruction, h⟩ := by
  unfold step
  split
  · rename_i hd
    cases hd.symm.trans h
  · rename_i other hd
    have he : other = instruction := Option.some.inj (hd.symm.trans h)
    cases he
    rfl

theorem execute_ecall (state : State) :
    execute state .ecall = .trapped state (encode .ecall) .environmentCall := rfl
theorem execute_ebreak (state : State) :
    execute state .ebreak = .trapped state (encode .ebreak) .breakpoint := rfl

/-- Loading x0 still creates the full access, so it can fault or consume a
device response. Only the successful register write is discarded. -/
theorem load_x0_requests (context : Context) (op : LoadOp) (source : Register) (imm : BitVec 12)
    (h : context.instruction = .load op 0 source imm) :
    executeContext context = .pending (.load context op 0 (effectiveAddress context.state source imm)) := by
  simp [executeContext, h]

@[simp] theorem finish_origin (pending : Pending) (reply : Reply pending) :
    (finish pending reply).origin = pending.context.state := by cases reply <;> rfl
@[simp] theorem finish_word (pending : Pending) (reply : Reply pending) :
    (finish pending reply).word = pending.context.word := by cases reply <;> rfl

theorem load_x0_completion (context : Context) (op : LoadOp) (address data : Word) :
    finish (.load context op 0 address) (.loaded data) = .retired context (next context.state) := by
  simp [finish, writeNext, next]
  exact write_zero _ _

theorem load_fault_no_update (context : Context) (op : LoadOp) (dest : Register)
    (address : Word) (reason : MemoryFault) :
    (finish (.load context op dest address) (.loadFault reason)).state = context.state := rfl

theorem store_fault_no_update (context : Context) (op : StoreOp) (address operand : Word) (reason : MemoryFault) :
    (finish (.store context op address operand) (.storeFault reason)).state = context.state := rfl

theorem store_completion_registers (context : Context) (op : StoreOp) (address operand : Word) :
    (finish (.store context op address operand) .stored).state.registers = context.state.registers := rfl

theorem load_completion_writeback (context : Context) (op : LoadOp) (dest : Register)
    (address data : Word) (h : dest ≠ 0) :
    read (finish (.load context op dest address) (.loaded data)).state.registers dest = loadValue op data :=
  read_write_same _ _ _ h

theorem successful_response_pc (pending : Pending) (reply : Reply pending) (context : Context) (after : State)
    (h : finish pending reply = .retired context after) : after.pc = pending.context.state.pc+4 := by
  cases reply <;> simp [finish, Outcome.retired.injEq] at h
  all_goals obtain ⟨rfl, rfl⟩ := h
  all_goals rfl

@[simp] theorem respond_stalled (pending : Pending) (offered : Option (Reply pending)) :
    respond pending false offered = .pending pending := by cases offered <;> rfl
@[simp] theorem respond_absent (pending : Pending) (ready : Bool) : respond pending ready none = .pending pending := rfl
@[simp] theorem respond_accepted (pending : Pending) (reply : Reply pending) :
    respond pending true (some reply) = finish pending reply := rfl

theorem respond_origin (pending : Pending) (ready : Bool) (offered : Option (Reply pending)) :
    (respond pending ready offered).origin = pending.context.state := by
  cases offered with
  | none => rfl
  | some reply =>
    cases ready
    · rfl
    · exact finish_origin pending reply

theorem respond_no_partial_update (pending : Pending) (ready : Bool) (offered : Option (Reply pending))
    (h : ∀ context after, respond pending ready offered ≠ .retired context after) :
    (respond pending ready offered).state = pending.context.state := by
  rw [nonretired_no_update _ h, respond_origin]

theorem accepted_response_terminal (pending : Pending) (reply : Reply pending) :
    (∃ context after, respond pending true (some reply) = .retired context after) ∨
      (∃ state word reason, respond pending true (some reply) = .trapped state word reason) := by
  cases reply <;> simp only [respond_accepted, finish]
  all_goals first | exact .inl ⟨_, _, rfl⟩ | exact .inr ⟨_, _, _, rfl⟩

theorem register_add_modular (left right : Word) :
    (registerALU .add left right).toNat = (left.toNat+right.toNat) % 2^32 := rfl

theorem register_sub_modular (left right : Word) :
    (registerALU .sub left right).toNat = (2^32-right.toNat+left.toNat) % 2^32 := rfl

theorem signed_compare (left right : Word) :
    registerALU .slt left right = 1 ↔ left.toInt < right.toInt := by
  simp [registerALU, bit, signedLess]

theorem unsigned_compare (left right : Word) :
    registerALU .sltu left right = 1 ↔ left.toNat < right.toNat := by
  simp [registerALU, bit, BitVec.ult]

theorem shift_amount_low_five (word : Word) : (word.extractLsb' 0 5).toNat = word.toNat % 32 := rfl

theorem register_shifts_low_five (left right other : Word)
    (h : right.toNat % 32 = other.toNat % 32) :
    registerALU .sll left right = registerALU .sll left other ∧
    registerALU .srl left right = registerALU .srl left other ∧
    registerALU .sra left right = registerALU .sra left other := by
  simp [registerALU, shift, h]

theorem arithmetic_shift_signed (value : Word) (amount : BitVec 5) :
    (shift .rightArithmetic value amount).toInt = value.toInt >>> amount.toNat :=
  BitVec.toInt_sshiftRight

theorem loadValue_idempotent (op : LoadOp) (data : Word) : loadValue op (loadValue op data) = loadValue op data := by
  cases op <;> simp only [loadValue]
  all_goals try rfl
  all_goals apply BitVec.eq_of_getLsbD_eq
  all_goals intro k hk
  all_goals grind (gen := 20) [BitVec.msb_eq_getLsbD_last]

theorem store_intent_operand (context : Context) (op : StoreOp) (first second : Register) (imm : BitVec 12)
    (h : context.instruction = .store op first second imm) :
    executeContext context = .pending (.store context op (effectiveAddress context.state first imm)
      (read context.state.registers second)) := by simp [executeContext, h]

theorem fence_serialized (context : Context) (dest source : Register) (mode pred succ : BitVec 4)
    (h : context.instruction = .fence dest source mode pred succ) :
    executeContext context = .pending (.fence context) ∧ (.fence context : Pending).intent = .fenceAll := by
  simp [executeContext, h, Pending.intent]

end Pinwheel.Hardware.Processor.RV32I.Semantics
