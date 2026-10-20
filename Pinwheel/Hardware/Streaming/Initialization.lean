import Pinwheel.Hardware.Streaming.SourceRefinement
import Pinwheel.Hardware.Streaming.HostCorrespondence

/-! Actual cold initialization and certified source installation. Loader clocks
advance both sampler stages; no initial register/image agreement is assumed. -/
namespace Pinwheel.Hardware.Streaming.Initialization
open Pinwheel.Hardware Pinwheel.Program.Streaming

structure Metadata where
  words : BitVec 6 → BitVec 64 := fun _ => 0
  written : BitVec 64 := 0
  pending : BitVec 1 := 0
  valid : BitVec 1 := 0
  count : BitVec 7 := 0
  idle : Pinwheel.Engine.Reactive.Pins := {}

def values (metadata : Metadata) (s : State a) : Values (Core.Register a) := fun r =>
  match r with
  | .word k => metadata.words k
  | .txWord k => (s.tx.memory[k.toNat]'k.isLt).data
  | .txBits k => BitVec.ofNat 6 (s.tx.memory[k.toNat]'k.isLt).validBits
  | .rxWord k => (s.rx.memory[k.toNat]'k.isLt).data
  | .rxBits k => BitVec.ofNat 6 (s.rx.memory[k.toNat]'k.isLt).validBits
  | .written => metadata.written | .pending => metadata.pending | .valid => metadata.valid
  | .count => metadata.count | .idleLevels => metadata.idle.levels | .idleEnabled => metadata.idle.enabled
  | .generation => s.generation | .transfer => s.transfer
  | .phase => s.phase.code | .pc => s.pc | .currentWord => encode s.current
  | .total => s.total | .remaining => s.remaining | .countdown => s.countdown
  | .cellBit => BitVec.ofBool s.cellBit | .levels => s.pins.levels | .enabled => s.pins.enabled
  | .txHead => BitVec.ofNat a s.tx.head.val | .txTail => BitVec.ofNat a s.tx.tail.val
  | .txCount => BitVec.ofNat 4 s.tx.count.val
  | .rxHead => BitVec.ofNat a s.rx.head.val | .rxTail => BitVec.ofNat a s.rx.tail.val
  | .rxCount => BitVec.ofNat 4 s.rx.count.val
  | .txShift => s.txShift | .txValid => s.txValid | .rxPartial => s.rxPartial | .rxUsed => s.rxUsed
  | .txAccepted => s.txAccepted | .txConsumed => s.txConsumed
  | .rxProduced => s.rxProduced | .rxPopped => s.rxPopped
  | .stage1 => s.samplerFirst | .stage2 => s.samplerSecond

theorem cold_resetting (i : Values Core.Input) (r : Values (Core.Register a))
    (cold : i .initialize = 1) : Core.resetting.eval i r = 1 := by
  simp [Core.resetting,Core.cold,Core.warm,Core.both,Core.either,Expr.eval,cold]

theorem cold_step (i : Values Core.Input) (r : Values (Core.Register a))
    (cold : i .initialize = 1) (port : Core.Register a w) :
    (Core.circuit a).step i r port = values {} ({} : State a) port := by
  have reset := cold_resetting i r cold
  have cleared : Core.clearedRuntime.eval i r = 1 := by
    simp [Core.clearedRuntime,Core.either,Expr.eval,reset]
  cases port <;>
    simp [Core.circuit,Circuit.step,Core.next,Core.nextRaw,Core.cold,Core.both,Core.either,Expr.eval,cold,reset,cleared,
      values,Queue.empty,Chunk.validBits,Phase.code,encode,BitVec.ofNat_eq_ofNat]
  all_goals rfl
  done


def Metadata.write (metadata : Metadata) (address : BitVec 6) (word : BitVec 64) : Metadata :=
  { metadata with words := fun k => if address = k then word else metadata.words k
                  written := metadata.written ||| (1#64 <<< address.toNat)
                  pending := 1, valid := 0 }

theorem pack_selected_bit (n : Nat) (f : Fin n → Core.E a 1) (i : Values Core.Input)
    (r : Values (Core.Register a)) (k : Fin n) :
    ((Core.pack f).eval i r).getLsbD k.val = ((f k).eval i r).getLsbD 0 := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    cases n with
    | zero => exact Fin.elim0 k
    | succ n =>
      cases n with
      | zero => have hk : k = 0 := Fin.ext (by omega); subst k; rfl
      | succ n =>
        cases k using Fin.cases with
        | zero => simp only [Core.pack,Expr.eval,Fin.val_zero,BitVec.getLsbD_append]; rfl
        | succ k =>
          have hnot : ¬ (k.val+1 < 1) := by omega
          simpa only [Core.pack,Expr.eval,BitVec.getLsbD_append,Fin.val_succ,
            hnot,if_false,Nat.add_sub_cancel] using
            ih (n+1) (by omega) (fun j => f j.succ) k

theorem mark_bit (old : BitVec 64) (address : BitVec 6) (k : Fin 64) :
    (old ||| (1#64 <<< address.toNat)).getLsbD k.val =
      (old.getLsbD k.val || decide (address = BitVec.ofNat 6 k.val)) := by
  have addressEq : (address = BitVec.ofNat 6 k.val) ↔ address.toNat = k.val := by
    constructor
    · intro h
      have same := congrArg BitVec.toNat h
      simpa only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt k.isLt] using same
    · intro h
      apply BitVec.eq_of_toNat_eq
      exact h.trans (Nat.mod_eq_of_lt k.isLt).symm
  simp only [BitVec.getLsbD_or,BitVec.getLsbD_shiftLeft,BitVec.getLsbD_one,k.isLt,
    decide_true,Bool.true_and,addressEq]
  by_cases equal : address.toNat = k.val
  · simp [equal]
  · by_cases less : k.val < address.toNat
    · simp [equal,less]
    · have different : k.val - address.toNat ≠ 0 := by omega
      simp [equal,less,different]

theorem written_write (i : Values Core.Input) (r : Values (Core.Register a)) :
    (Core.pack (fun k => Core.either (.slice k.val 1 (by omega) (.reg .written))
      (.equal (.input .address) (.lit (BitVec.ofNat 6 k.val))))).eval i r =
      r .written ||| (1#64 <<< (i .address).toNat) := by
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro k within
  rw [pack_selected_bit 64 _ i r ⟨k,within⟩,mark_bit _ _ ⟨k,within⟩]
  simp [Core.either,Expr.eval,BitVec.not_and]
  rfl

structure Write (i : Values Core.Input) (address : BitVec 6) (word : BitVec 64) : Prop where
  cold : i .initialize = 0
  command : i .command = 1
  address : i .address = address
  word : i .word = word

theorem write_step (metadata : Metadata) (s : State a) (i : Values Core.Input)
    (address : BitVec 6) (word : BitVec 64) (input : Write i address word)
    (phase : s.phase = .free) (port : Core.Register a w) :
    (Core.circuit a).step i (values metadata s) port =
      values (metadata.write address word) (s.sample (i .rawInputs)) port := by
  have reset : Core.resetting.eval i (values metadata s) = 0 := by
    simp [Core.resetting,Core.cold,Core.warm,Core.cmd,Core.both,Core.either,Expr.eval,input.cold,input.command]
  have free : Core.free.eval i (values metadata s) = 1 := by
    simp [Core.free,Core.both,Expr.eval,reset,values,phase,Phase.code]
  have writing : Core.writing.eval i (values metadata s) = 1 := by
    simp [Core.writing,Core.both,Core.cmd,Expr.eval,free,input.command]
  have committing : Core.committing.eval i (values metadata s) = 0 := by
    simp [Core.committing,Core.both,Core.cmd,Expr.eval,input.command]
  have starting : Core.starting.eval i (values metadata s) = 0 := by
    simp [Core.starting,Core.both,Core.cmd,Expr.eval,input.command]
  have owner : Core.hostOwner.eval i (values metadata s) = 0 := by
    simp [Core.hostOwner,Core.owned,Core.busy,Core.retained,Core.isPhase,Core.both,Core.either,
      Expr.eval,values,phase,Phase.code]
  have releasing : Core.releasing.eval i (values metadata s) = 0 := by
    simp [Core.releasing,Core.both,Expr.eval,owner]
  cases port
  case written =>
    simp only [Core.circuit,Circuit.step,Core.next,Core.nextRaw,Expr.eval,reset,writing]
    change (Core.pack (fun k => Core.either (.slice k.val 1 (by omega) (.reg .written))
      (.equal (.input .address) (.lit (BitVec.ofNat 6 k.val))))).eval i (values metadata s) = _
    simpa only [values,Metadata.write,input.address] using written_write i (values metadata s)
  all_goals
    simp [Core.circuit,Circuit.step,Core.next,Core.nextRaw,Core.nextPins,Core.clearedRuntime,
      Core.cold,Core.both,Core.either,Core.pushing,Core.popping,Core.reserving,Core.takingTX,
      Core.loadingTX,Core.capture,Core.capturingRX,Core.emittingRX,Core.highEnd,Core.fetching,
      Core.enteringCell,Core.advancing,Core.isPhase,Core.queueCount,Expr.eval,reset,writing,committing,starting,
      owner,releasing,values,phase,Phase.code,Metadata.write,State.sample,
      input.cold,input.address,input.word,BitVec.ofNat_eq_ofNat]
  case word k =>
    have gate (x y : BitVec 6) (yes no : BitVec 64) :
        (if (1#1 &&& BitVec.ofBool (decide (x=y))) = 1#1 then yes else no) =
          if x=y then yes else no := by
      by_cases h : x=y <;> simp [h]
    exact gate address k word (metadata.words k)
  all_goals rfl
  done


private theorem band_one : ∀ x y : BitVec 1, x &&& y = 1 ↔ x = 1 ∧ y = 1 := by
  decide +kernel

private theorem foldl_one (xs : List α) (f : α → Core.E a 1) (acc : Core.E a 1)
    (i : Values Core.Input) (r : Values (Core.Register a)) :
    (xs.foldl (fun current k => Core.both current (f k)) acc).eval i r = 1 ↔
      acc.eval i r = 1 ∧ ∀ k ∈ xs, (f k).eval i r = 1 := by
  induction xs generalizing acc with
  | nil => simp
  | cons item rest ih =>
    rw [List.foldl_cons,ih]
    simp only [Core.both,Expr.eval,band_one,List.mem_cons,forall_eq_or_imp,and_assoc]

theorem covered_prefix (p : Program) (i : Values Core.Input) (r : Values (Core.Register a))
    (count : i .count = BitVec.ofNat 7 p.length)
    (covered : ∀ k : Fin 64, k.val < p.length → (r .written).getLsbD k.val = true) :
    Core.covered.eval i r = 1 := by
  rw [Core.covered_eval_fold]
  rw [foldl_one]
  refine ⟨rfl,?_⟩
  intro k _
  have wide : (BitVec.ofNat 7 k.val).toNat = k.val := Nat.mod_eq_of_lt (by have := k.isLt; omega)
  have countNat : (BitVec.ofNat 7 p.length).toNat = p.length :=
    Nat.mod_eq_of_lt (by have := SourceRefinement.length_le p; omega)
  by_cases live : k.val < p.length
  · have bit := covered k live
    have slice : (r .written).extractLsb' k.val 1 = 1#1 := by
      apply eq_of_beq
      exact (BitVec.getLsbD_eq_extractLsb' _ _).symm.trans bit
    simp [Core.either,Expr.eval,count,wide,countNat,live,slice]
  · simp [Core.either,Expr.eval,count,wide,countNat,live]

structure Commit (p : Program) (i : Values Core.Input) : Prop where
  cold : i .initialize = 0
  command : i .command = 2
  count : i .count = BitVec.ofNat 7 p.length
  levels : i .idleLevels = p.idle.levels
  enabled : i .idleEnabled = p.idle.enabled

theorem count_valid (p : Program) (i : Values Core.Input) (r : Values (Core.Register a))
    (count : i .count = BitVec.ofNat 7 p.length) : Core.countValid.eval i r = 1 := by
  have size : (BitVec.ofNat 7 p.length).toNat = p.length :=
    Nat.mod_eq_of_lt (by have := SourceRefinement.length_le p; omega)
  have nonzero : BitVec.ofNat 7 p.length ≠ 0#7 := by
    intro same
    have equal := congrArg BitVec.toNat same
    rw [size] at equal
    have positive := SourceRefinement.length_positive p
    change p.length = 0 at equal
    omega
  have bound := SourceRefinement.length_le p
  simp [Core.countValid,Core.both,Expr.eval,count,size,nonzero,show ¬ 64 < p.length from by omega]

theorem commit_accepted (p : Program) (metadata : Metadata) (s : State a) (i : Values Core.Input)
    (input : Commit p i) (phase : s.phase = .free) (pending : metadata.pending = 1)
    (space : s.generation ≠ 65535#16)
    (covered : ∀ k : Fin 64, k.val < p.length → metadata.written.getLsbD k.val = true) :
    Core.committing.eval i (values metadata s) = 1 := by
  have reset : Core.resetting.eval i (values metadata s) = 0 := by
    simp [Core.resetting,Core.cold,Core.warm,Core.cmd,Core.both,Core.either,Expr.eval,input.cold,input.command]
  have free : Core.free.eval i (values metadata s) = 1 := by
    simp [Core.free,Core.both,Expr.eval,reset,values,phase,Phase.code]
  have checked := count_valid p i (values metadata s) input.count
  have coverage := covered_prefix p i (values metadata s) input.count covered
  simp [Core.committing,Core.both,Core.cmd,Core.space,Expr.eval,free,input.command,checked,coverage,
    values,pending,space]


def Metadata.commit (metadata : Metadata) (p : Program) : Metadata :=
  { metadata with pending := 0, valid := 1, count := BitVec.ofNat 7 p.length, idle := p.idle }

def committed (s : State a) (raw : BitVec 2) : State a :=
  { s.sample raw with generation := s.generation + 1 }

theorem commit_step (p : Program) (metadata : Metadata) (s : State a) (i : Values Core.Input)
    (input : Commit p i) (phase : s.phase = .free) (pending : metadata.pending = 1)
    (space : s.generation ≠ 65535#16)
    (covered : ∀ k : Fin 64, k.val < p.length → metadata.written.getLsbD k.val = true)
    (port : Core.Register a w) :
    (Core.circuit a).step i (values metadata s) port =
      values (metadata.commit p) (committed s (i .rawInputs)) port := by
  have reset : Core.resetting.eval i (values metadata s) = 0 := by
    simp [Core.resetting,Core.cold,Core.warm,Core.cmd,Core.both,Core.either,Expr.eval,input.cold,input.command]
  have writing : Core.writing.eval i (values metadata s) = 0 := by
    simp [Core.writing,Core.both,Core.cmd,Expr.eval,input.command]
  have accepted := commit_accepted p metadata s i input phase pending space covered
  have starting : Core.starting.eval i (values metadata s) = 0 := by
    simp [Core.starting,Core.both,Core.cmd,Expr.eval,input.command]
  have owner : Core.hostOwner.eval i (values metadata s) = 0 := by
    simp [Core.hostOwner,Core.owned,Core.busy,Core.retained,Core.isPhase,Core.both,Core.either,
      Expr.eval,values,phase,Phase.code]
  have releasing : Core.releasing.eval i (values metadata s) = 0 := by
    simp [Core.releasing,Core.both,Expr.eval,owner]
  cases port <;>
    simp [Core.circuit,Circuit.step,Core.next,Core.nextRaw,Core.nextPins,Core.clearedRuntime,
      Core.cold,Core.both,Core.either,Core.pushing,Core.popping,Core.reserving,Core.takingTX,
      Core.loadingTX,Core.capture,Core.capturingRX,Core.emittingRX,Core.highEnd,Core.fetching,
      Core.enteringCell,Core.advancing,Core.isPhase,Core.queueCount,Expr.eval,reset,writing,accepted,starting,
      owner,releasing,values,phase,Phase.code,Metadata.commit,committed,State.sample,
      input.cold,input.count,input.levels,input.enabled,SourceRefinement.inc_eval,BitVec.ofNat_eq_ofNat]
  all_goals rfl
  done


theorem idle_step (metadata : Metadata) (s : State a) (i : Values Core.Input)
    (cold : i .initialize = 0) (command : i .command = 0) (phase : s.phase = .free)
    (port : Core.Register a w) :
    (Core.circuit a).step i (values metadata s) port = values metadata (s.sample (i .rawInputs)) port := by
  have reset : Core.resetting.eval i (values metadata s) = 0 := by
    simp [Core.resetting,Core.cold,Core.warm,Core.cmd,Core.both,Core.either,Expr.eval,cold,command]
  have writing : Core.writing.eval i (values metadata s) = 0 := by
    simp [Core.writing,Core.both,Core.cmd,Expr.eval,command]
  have committing : Core.committing.eval i (values metadata s) = 0 := by
    simp [Core.committing,Core.both,Core.cmd,Expr.eval,command]
  have starting : Core.starting.eval i (values metadata s) = 0 := by
    simp [Core.starting,Core.both,Core.cmd,Expr.eval,command]
  have owner : Core.hostOwner.eval i (values metadata s) = 0 := by
    simp [Core.hostOwner,Core.owned,Core.busy,Core.retained,Core.isPhase,Core.both,Core.either,
      Expr.eval,values,phase,Phase.code]
  have releasing : Core.releasing.eval i (values metadata s) = 0 := by
    simp [Core.releasing,Core.both,Expr.eval,owner]
  cases port <;>
    simp [Core.circuit,Circuit.step,Core.next,Core.nextRaw,Core.nextPins,Core.clearedRuntime,
      Core.cold,Core.both,Core.either,Core.pushing,Core.popping,Core.reserving,Core.takingTX,
      Core.loadingTX,Core.capture,Core.capturingRX,Core.emittingRX,Core.highEnd,Core.fetching,
      Core.enteringCell,Core.advancing,Core.isPhase,Core.queueCount,Expr.eval,reset,writing,committing,starting,
      owner,releasing,values,phase,Phase.code,State.sample,cold,BitVec.ofNat_eq_ofNat]
  all_goals rfl
  done

def rowWord (p : Program) (k : Nat) : BitVec 64 := encode (p.memory[k % 64]'(Nat.mod_lt _ (by decide)))

def metadataAfter (p : Program) : Nat → Metadata
  | 0 => {}
  | k+1 => (metadataAfter p k).write (BitVec.ofNat 6 k) (rowWord p k)

theorem metadata_word (p : Program) (n : Nat) (bound : n ≤ 64) (k : BitVec 6)
    (live : k.toNat < n) :
    (metadataAfter p n).words k = encode (p.memory[k.toNat]'k.isLt) := by
  induction n with
  | zero => omega
  | succ n ih =>
    have previous : n ≤ 64 := by omega
    have addressBound : n < 64 := by omega
    by_cases last : k.toNat = n
    · have address : BitVec.ofNat 6 n = k := by
        apply BitVec.eq_of_toNat_eq
        exact (Nat.mod_eq_of_lt addressBound).trans last.symm
      simp only [metadataAfter,Metadata.write,address,ite_true,rowWord,Nat.mod_eq_of_lt addressBound,last]
    · have priorLive : k.toNat < n := by omega
      have distinct : BitVec.ofNat 6 n ≠ k := by
        intro same
        have equal := congrArg BitVec.toNat same
        rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt addressBound] at equal
        exact last equal.symm
      simpa only [metadataAfter,Metadata.write,distinct,ite_false] using ih previous priorLive

theorem metadata_covered (p : Program) (n : Nat) (bound : n ≤ 64) (k : Fin 64)
    (live : k.val < n) : (metadataAfter p n).written.getLsbD k.val = true := by
  induction n with
  | zero => omega
  | succ n ih =>
    have addressBound : n < 64 := by omega
    have previous : n ≤ 64 := by omega
    simp only [metadataAfter,Metadata.write,mark_bit]
    by_cases last : k.val = n
    · have address : BitVec.ofNat 6 n = BitVec.ofNat 6 k.val := by rw [last]
      simp [address]
    · have priorLive : k.val < n := by omega
      simp [ih previous priorLive]

theorem metadata_pending (p : Program) (n : Nat) (positive : 0 < n) :
    (metadataAfter p n).pending = 1 := by
  cases n with
  | zero => omega
  | succ n => rfl

def sampled (s : State a) (samples : List (Values Core.Input)) : State a :=
  samples.foldl (fun s i => s.sample (i .rawInputs)) s

theorem sampled_snoc (s : State a) (samples : List (Values Core.Input)) (i : Values Core.Input) :
    sampled s (samples ++ [@i]) = (sampled s samples).sample (i .rawInputs) := by
  simp [sampled,List.foldl_append]

theorem sampled_phase (s : State a) (samples : List (Values Core.Input)) : (sampled s samples).phase = s.phase := by
  induction samples generalizing s with
  | nil => rfl
  | cons i rest ih =>
    change (sampled (s.sample (i .rawInputs)) rest).phase = s.phase
    exact (ih _).trans rfl

def rawRun (r : Values (Core.Register a)) (samples : List (Values Core.Input)) : Values (Core.Register a) :=
  samples.foldl (α := Values (Core.Register a)) (fun r i => @Circuit.step _ _ _ (Core.circuit a) i r) r

theorem rawRun_snoc (r : Values (Core.Register a)) (samples : List (Values Core.Input)) (i : Values Core.Input) :
    @rawRun a r (samples ++ [@i]) = @Circuit.step _ _ _ (Core.circuit a) i (rawRun r samples) := by
  unfold rawRun
  rw [List.foldl_append]
  rfl

/-- A raw sampled command grammar: quiet clocks may occur anywhere between
ordered source-bound writes. Every non-constrained input field remains arbitrary. -/
inductive Upload (p : Program) : Nat → List (Values Core.Input) → Prop
  | nil : Upload p 0 []
  | idle {n samples} (before : Upload p n samples) (i : Values Core.Input)
      (cold : i .initialize = 0) (command : i .command = 0) : Upload p n (samples ++ [@i])
  | write {n samples} (before : Upload p n samples) (within : n < p.length) (i : Values Core.Input)
      (input : Write i (BitVec.ofNat 6 n) (rowWord p n)) : Upload p (n+1) (samples ++ [@i])

theorem Upload.run (upload : Upload p n samples) (s : State a) (phase : s.phase = .free) :
    @rawRun a (values {} s) samples = @values a (metadataAfter p n) (sampled s samples) := by
  induction upload with
  | nil => rfl
  | @idle n samples before i cold command ih =>
    rw [rawRun_snoc,ih,sampled_snoc]
    funext w port
    exact idle_step _ _ i cold command ((sampled_phase s samples).trans phase) port
  | @write n samples before within i input ih =>
    rw [rawRun_snoc,ih,sampled_snoc]
    funext w port
    exact write_step _ _ i _ _ input ((sampled_phase s samples).trans phase) port


theorem sampled_generation (s : State a) (samples : List (Values Core.Input)) :
    (sampled s samples).generation = s.generation := by
  induction samples generalizing s with
  | nil => rfl
  | cons i rest ih =>
    change (sampled (s.sample (i .rawInputs)) rest).generation = s.generation
    exact (ih _).trans rfl

def CanonicalProgram (p : Program) : Prop :=
  ∀ k : Fin 64, k.val < p.length → (p.memory[k.val]).Canonical

def installedImage (p : Program)
    (canonical : CanonicalProgram p) : SourceRefinement.Image p where
  words := (metadataAfter p p.length).words
  written := (metadataAfter p p.length).written
  pending := 0
  source k live := metadata_word p p.length (SourceRefinement.length_le p) k live
  canonical := canonical

theorem values_installed (p : Program)
    (canonical : CanonicalProgram p) (s : State a) :
    @values a ((metadataAfter p p.length).commit p) s = @SourceRefinement.values p a (installedImage p canonical) s := by
  funext w port
  cases port <;> rfl

theorem compiled_canonical (image : Compiled source idle) (k : Fin 64)
    (live : k.val < image.program.length) : (image.program.memory[k.val]).Canonical := by
  have within : k.val < source.length := by simpa only [image.program_length] using live
  have canonical := image.sourceValid.2.2.2.2 (source[k.val]) (List.getElem_mem within)
  simpa only [Compiled.program,Vector.getElem_ofFn,List.getElem?_eq_getElem within,Option.getD_some] using canonical

theorem compiledCanonical (image : Compiled source idle) : CanonicalProgram image.program :=
  @compiled_canonical source idle image

def compiledImage (image : Compiled source idle) : SourceRefinement.Image image.program :=
  @installedImage image.program (@compiledCanonical source idle image)

theorem compiled_row (image : Compiled source idle) (k : Nat) (within : k < source.length) :
    rowWord image.program k = (image.words[k]'(by simpa only [image.wordsEqual,List.length_map] using within)) := by
  have bound : k < 64 := by have := image.sourceValid.2.1; omega
  simp only [rowWord,Compiled.program,Nat.mod_eq_of_lt bound,Vector.getElem_ofFn,
    List.getElem?_eq_getElem within,Option.getD_some,image.wordsEqual,List.getElem_map]

theorem cold_values (i : Values Core.Input) (r : Values (Core.Register a)) (cold : i .initialize = 1) :
    @Circuit.step _ _ _ (Core.circuit a) i r = @values a {} ({} : State a) := by
  funext w port
  exact cold_step i r cold port


/-- The actual cold edge, every sampled upload clock and the actual COMMIT
produce a certified installed source state, from arbitrary startup registers. -/
theorem initialized_upload_correct (p : Program) (canonical : CanonicalProgram p)
    (startup : Values (Core.Register a)) (coldInput : Values Core.Input) (cold : coldInput .initialize = 1)
    (samples : List (Values Core.Input)) (upload : Upload p p.length samples)
    (commitInput : Values Core.Input) (commit : Commit p commitInput) :
    @rawRun a startup (@coldInput :: (samples ++ [@commitInput])) =
      @SourceRefinement.values p a (installedImage p canonical)
        (committed (sampled ({} : State a) samples) (commitInput .rawInputs)) := by
  change @rawRun a (@Circuit.step _ _ _ (Core.circuit a) coldInput startup) (samples ++ [@commitInput]) = _
  rw [cold_values coldInput startup cold,rawRun_snoc,upload.run ({} : State a) rfl]
  have phase : (sampled ({} : State a) samples).phase = .free := (sampled_phase _ samples).trans rfl
  have pending := metadata_pending p p.length (SourceRefinement.length_positive p)
  have room : (sampled ({} : State a) samples).generation ≠ 65535#16 := by
    rw [sampled_generation]
    change 0#16 ≠ 65535#16
    decide
  have coverage := metadata_covered p p.length (SourceRefinement.length_le p)
  have finished : @Circuit.step _ _ _ (Core.circuit a) commitInput
      (values (metadataAfter p p.length) (sampled ({} : State a) samples)) =
      @values a ((metadataAfter p p.length).commit p)
        (committed (sampled ({} : State a) samples) (commitInput .rawInputs)) := by
    funext w port
    exact commit_step p _ _ commitInput commit phase pending room coverage port
  exact finished.trans (values_installed p canonical _)

/-- Compilation supplies canonicality automatically. The upload grammar binds
each delivered row to that compiled source, rather than assuming bank agreement. -/
theorem compiled_upload_correct (image : Compiled source idle)
    (startup : Values (Core.Register a)) (coldInput : Values Core.Input) (cold : coldInput .initialize = 1)
    (samples : List (Values Core.Input)) (upload : Upload image.program image.program.length samples)
    (commitInput : Values Core.Input) (commit : Commit image.program commitInput) :
    @rawRun a startup (@coldInput :: (samples ++ [@commitInput])) =
      @SourceRefinement.values image.program a (compiledImage image)
        (committed (sampled ({} : State a) samples) (commitInput .rawInputs)) :=
  initialized_upload_correct image.program (@compiledCanonical source idle image)
    startup coldInput cold samples upload commitInput commit

theorem sample_structural (s : State a) (raw : BitVec 2) (invariant : s.Structural) :
    (s.sample raw).Structural := by
  exact ⟨invariant.accepted, invariant.txValid, invariant.rxUsed, invariant.lowCredit⟩

theorem sampled_structural (s : State a) (samples : List (Values Core.Input))
    (invariant : s.Structural) : (sampled s samples).Structural := by
  induction samples generalizing s with
  | nil => exact invariant
  | cons i rest ih => exact ih (s.sample (i .rawInputs)) (sample_structural s _ invariant)

theorem committed_structural (s : State a) (raw : BitVec 2) (invariant : s.Structural) :
    (committed s raw).Structural := by
  exact ⟨invariant.accepted, invariant.txValid, invariant.rxUsed, invariant.lowCredit⟩

theorem initial_structural (a : Nat) : ({} : State a).Structural := by
  constructor <;> simp [State.LowCredit]

theorem initialized_structural (samples : List (Values Core.Input)) (raw : BitVec 2) :
    (committed (sampled ({} : State a) samples) raw).Structural :=
  committed_structural _ _ (sampled_structural _ _ (initial_structural a))

/-- The concrete delivered host commands keep their inactive payload fields
ordinary. These witnesses concern sampled core commands, not frontend pins. -/
def writeCommand (p : Program) (k : Nat) (raw : BitVec 2) : Host.Command :=
  { runtime := { command := 1, rawInputs := raw }
    address := BitVec.ofNat 6 k, word := rowWord p k }

def commitCommand (p : Program) (raw : BitVec 2) : Host.Command :=
  { runtime := { command := 2, rawInputs := raw }
    count := BitVec.ofNat 7 p.length, idle := p.idle }

def coldCommand (raw : BitVec 2) : Host.Command :=
  { runtime := { «initialize» := true, rawInputs := raw } }

theorem writeCommand_correct (p : Program) (k : Nat) (raw : BitVec 2) :
    Write (HostCorrespondence.commandValues (writeCommand p k raw)) (BitVec.ofNat 6 k) (rowWord p k) := by
  constructor <;> rfl

theorem commitCommand_correct (p : Program) (raw : BitVec 2) :
    Commit p (HostCorrespondence.commandValues (commitCommand p raw)) := by
  constructor <;> rfl

def concreteSamples (p : Program) (raw : BitVec 2) : Nat → List (Values Core.Input)
  | 0 => []
  | k+1 => concreteSamples p raw k ++ [@HostCorrespondence.commandValues (writeCommand p k raw)]

theorem concrete_upload (p : Program) (raw : BitVec 2) (n : Nat) (within : n ≤ p.length) :
    Upload p n (concreteSamples p raw n) := by
  induction n with
  | zero => exact .nil
  | succ n ih =>
    exact .write (ih (by omega)) (by omega) _ (writeCommand_correct p n raw)

theorem concrete_initialized (image : Compiled source idle)
    (startup : Values (Core.Register a)) (raw : BitVec 2) :
    @rawRun a startup
      (@HostCorrespondence.commandValues (coldCommand raw) ::
        (concreteSamples image.program raw image.program.length ++
          [@HostCorrespondence.commandValues (commitCommand image.program raw)])) =
    @SourceRefinement.values image.program a (compiledImage image)
      (committed (sampled ({} : State a) (concreteSamples image.program raw image.program.length)) raw) :=
  compiled_upload_correct image startup _ rfl _
    (concrete_upload image.program raw image.program.length (Nat.le_refl _)) _
    (commitCommand_correct image.program raw)

end Pinwheel.Hardware.Streaming.Initialization
