import Pinwheel.Hardware.StreamingReady.LoaderEquivalence
import Pinwheel.Hardware.StreamingReady.SourceRefinement
import Pinwheel.Hardware.Streaming.Initialization
import Pinwheel.Program.StreamingReadySafety

/-! Arbitrary-startup installation for Ready words. Existing free loader laws are
reused over a legacy free carrier; the final handoff binds the new encoder and
all runtime fields, including the samples accumulated during upload. -/
namespace Pinwheel.Hardware.StreamingReady.Initialization
open Pinwheel.Hardware Pinwheel.Program.StreamingReady
set_option linter.unusedSimpArgs false

abbrev Metadata := Streaming.Initialization.Metadata
abbrev Carrier (a : Nat) := Pinwheel.Program.Streaming.State a
def values (metadata : Metadata) (s : Carrier a) : Values (Core.Register a) := Streaming.Initialization.values metadata s
abbrev Write := Streaming.Initialization.Write
abbrev mark_bit := Streaming.Initialization.mark_bit

/-- Only length and idle are used by the reused COMMIT theorem. This stub is
never claimed as the installed instruction source. -/
def loaderGeometry (p : Program) : Pinwheel.Program.Streaming.Program :=
  {memory := Vector.replicate 64 .halt,lengthMinusOne := p.lengthMinusOne,idle := p.idle}

abbrev Commit (p : Program) := Streaming.Initialization.Commit (loaderGeometry p)

theorem length_positive (p : Program) : 0 < p.length := by simp [Program.length]
theorem length_le (p : Program) : p.length ≤ 64 := by
  have := p.lengthMinusOne.isLt
  simp only [Program.length]
  omega

theorem write_step (metadata : Metadata) (s : Carrier a) (i : Values Core.Input)
    (address : BitVec 6) (word : BitVec 64) (input : Write i address word)
    (phase : s.phase = .free) (port : Core.Register a w) :
    (Core.circuit a).step i (values metadata s) port =
      values (metadata.write address word) (s.sample (i .rawInputs)) port := by
  rw [LoaderEquivalence.free_step_equal i (values metadata s) (by change s.phase.code = 0; rw [phase]; rfl)]
  exact Streaming.Initialization.write_step metadata s i address word input phase port

theorem idle_step (metadata : Metadata) (s : Carrier a) (i : Values Core.Input)
    (cold : i .initialize = 0) (command : i .command = 0) (phase : s.phase = .free)
    (port : Core.Register a w) :
    (Core.circuit a).step i (values metadata s) port = values metadata (s.sample (i .rawInputs)) port := by
  rw [LoaderEquivalence.free_step_equal i (values metadata s) (by change s.phase.code = 0; rw [phase]; rfl)]
  exact Streaming.Initialization.idle_step metadata s i cold command phase port

theorem commit_step (p : Program) (metadata : Metadata) (s : Carrier a) (i : Values Core.Input)
    (input : Commit p i) (phase : s.phase = .free) (pending : metadata.pending = 1)
    (space : s.generation ≠ 65535#16)
    (covered : ∀ k : Fin 64, k.val < p.length → metadata.written.getLsbD k.val = true)
    (port : Core.Register a w) :
    (Core.circuit a).step i (values metadata s) port =
      values (metadata.commit (loaderGeometry p)) (Streaming.Initialization.committed s (i .rawInputs)) port := by
  rw [LoaderEquivalence.free_step_equal i (values metadata s) (by change s.phase.code = 0; rw [phase]; rfl)]
  exact Streaming.Initialization.commit_step (loaderGeometry p) metadata s i input phase pending space covered port

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
      simp only [metadataAfter,Streaming.Initialization.Metadata.write,address,ite_true,rowWord,Nat.mod_eq_of_lt addressBound,last]
    · have priorLive : k.toNat < n := by omega
      have distinct : BitVec.ofNat 6 n ≠ k := by
        intro same
        have equal := congrArg BitVec.toNat same
        rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt addressBound] at equal
        exact last equal.symm
      simpa only [metadataAfter,Streaming.Initialization.Metadata.write,distinct,ite_false] using ih previous priorLive

theorem metadata_covered (p : Program) (n : Nat) (bound : n ≤ 64) (k : Fin 64)
    (live : k.val < n) : (metadataAfter p n).written.getLsbD k.val = true := by
  induction n with
  | zero => omega
  | succ n ih =>
    have addressBound : n < 64 := by omega
    have previous : n ≤ 64 := by omega
    simp only [metadataAfter,Streaming.Initialization.Metadata.write,mark_bit]
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

def sampled (s : Carrier a) (samples : List (Values Core.Input)) : Carrier a :=
  Streaming.Initialization.sampled s samples

theorem sampled_snoc (s : Carrier a) (samples : List (Values Core.Input)) (i : Values Core.Input) :
    sampled s (samples ++ [@i]) = (sampled s samples).sample (i .rawInputs) := by
  simp [sampled,Streaming.Initialization.sampled,List.foldl_append]

theorem sampled_phase (s : Carrier a) (samples : List (Values Core.Input)) :
    (sampled s samples).phase = s.phase := Streaming.Initialization.sampled_phase s samples

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

theorem Upload.run (upload : Upload p n samples) (s : Carrier a) (phase : s.phase = .free) :
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


theorem sampled_generation (s : Carrier a) (samples : List (Values Core.Input)) :
    (sampled s samples).generation = s.generation := Streaming.Initialization.sampled_generation s samples

def phaseLift : Pinwheel.Program.Streaming.Phase → Phase
  | .free => .free | .fetch => .fetch | .boundary => .boundary | .low => .low
  | .high => .high | .completed => .completed | .fault => .fault

/-- Loader carrier conversion copies every runtime field. It does not supply
an agreement premise: the carrier itself is derived by the actual loader run. -/
def ofCarrier (s : Carrier a) : State a :=
  {phase := phaseLift s.phase,pc := s.pc,current := liftInstruction s.current,
   total := s.total,remaining := s.remaining,countdown := s.countdown,cellBit := s.cellBit,
   tx := s.tx,rx := s.rx,txShift := s.txShift,txValid := s.txValid,
   rxPartial := s.rxPartial,rxUsed := s.rxUsed,
   samplerFirst := s.samplerFirst,samplerSecond := s.samplerSecond,pins := s.pins,
   generation := s.generation,transfer := s.transfer,txAccepted := s.txAccepted,
   txConsumed := s.txConsumed,rxProduced := s.rxProduced,rxPopped := s.rxPopped}

def CanonicalProgram (p : Program) : Prop :=
  ∀ k : Fin 64, k.val < p.length → (p.memory[k.val]).Canonical

def installedImage (p : Program) (canonical : CanonicalProgram p) : SourceRefinement.Image p where
  words := (metadataAfter p p.length).words
  written := (metadataAfter p p.length).written
  pending := 0
  source k live := metadata_word p p.length (length_le p) k live
  canonical := canonical

theorem values_installed (p : Program) (canonical : CanonicalProgram p) (s : Carrier a) :
    @values a ((metadataAfter p p.length).commit (loaderGeometry p)) s =
      @SourceRefinement.values p a (installedImage p canonical) (ofCarrier s) := by
  funext w port
  cases port <;> try rfl
  case phase =>
    change s.phase.code = (phaseLift s.phase).code
    cases s.phase <;> rfl
  case currentWord => exact (encode_lift s.current).symm
  done

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
    @Circuit.step _ _ _ (Core.circuit a) i r = @values a {} ({} : Carrier a) := by
  funext w port
  exact (LoaderEquivalence.cold_step_equal i r cold port).trans (Streaming.Initialization.cold_step i r cold port)

def installedState (samples : List (Values Core.Input)) (raw : BitVec 2) : State a :=
  ofCarrier (Streaming.Initialization.committed (sampled ({} : Carrier a) samples) raw)

/-- Actual cold, ordered source-bound writes with arbitrary quiet samples, and
COMMIT derive VALID and every installed Ready register from arbitrary startup. -/
theorem initialized_upload_correct (p : Program) (canonical : CanonicalProgram p)
    (startup : Values (Core.Register a)) (coldInput : Values Core.Input) (cold : coldInput .initialize = 1)
    (samples : List (Values Core.Input)) (upload : Upload p p.length samples)
    (commitInput : Values Core.Input) (commit : Commit p commitInput) :
    @rawRun a startup (@coldInput :: (samples ++ [@commitInput])) =
      @SourceRefinement.values p a (installedImage p canonical) (installedState samples (commitInput .rawInputs)) := by
  change @rawRun a (@Circuit.step _ _ _ (Core.circuit a) coldInput startup) (samples ++ [@commitInput]) = _
  rw [cold_values coldInput startup cold,rawRun_snoc,upload.run ({} : Carrier a) rfl]
  have phase : (sampled ({} : Carrier a) samples).phase = .free := (sampled_phase _ samples).trans rfl
  have pending := metadata_pending p p.length (length_positive p)
  have room : (sampled ({} : Carrier a) samples).generation ≠ 65535#16 := by
    rw [sampled_generation]
    change 0#16 ≠ 65535#16
    decide
  have coverage := metadata_covered p p.length (length_le p)
  have finished : @Circuit.step _ _ _ (Core.circuit a) commitInput
      (values (metadataAfter p p.length) (sampled ({} : Carrier a) samples)) =
      @values a ((metadataAfter p p.length).commit (loaderGeometry p))
        (Streaming.Initialization.committed (sampled ({} : Carrier a) samples) (commitInput .rawInputs)) := by
    funext w port
    exact commit_step p _ _ commitInput commit phase pending room coverage port
  exact finished.trans (values_installed p canonical _)

theorem compiled_upload_correct (image : Compiled source idle)
    (startup : Values (Core.Register a)) (coldInput : Values Core.Input) (cold : coldInput .initialize = 1)
    (samples : List (Values Core.Input)) (upload : Upload image.program image.program.length samples)
    (commitInput : Values Core.Input) (commit : Commit image.program commitInput) :
    @rawRun a startup (@coldInput :: (samples ++ [@commitInput])) =
      @SourceRefinement.values image.program a (@compiledImage source idle image)
        (installedState samples (commitInput .rawInputs)) :=
  initialized_upload_correct image.program (@compiledCanonical source idle image)
    startup coldInput cold samples upload commitInput commit

theorem ofCarrier_sample_structural (s : Carrier a) (raw : BitVec 2)
    (invariant : (ofCarrier s).Structural) : (ofCarrier (s.sample raw)).Structural :=
  ⟨invariant.accepted,invariant.txValid,invariant.rxUsed,invariant.reservationCredit,invariant.partialCredit⟩

theorem sampled_structural (s : Carrier a) (samples : List (Values Core.Input))
    (invariant : (ofCarrier s).Structural) : (ofCarrier (sampled s samples)).Structural := by
  induction samples generalizing s with
  | nil => exact invariant
  | cons i rest ih =>
    change (ofCarrier (sampled (s.sample (i .rawInputs)) rest)).Structural
    exact ih _ (ofCarrier_sample_structural s _ invariant)

theorem initialized_structural (samples : List (Values Core.Input)) (raw : BitVec 2) :
    (@installedState a samples raw).Structural := by
  have initial : (ofCarrier ({} : Carrier a)).Structural := initial_structural a
  have invariant := sampled_structural ({} : Carrier a) samples initial
  exact ⟨invariant.accepted,invariant.txValid,invariant.rxUsed,invariant.reservationCredit,invariant.partialCredit⟩

theorem initialized_free (samples : List (Values Core.Input)) (raw : BitVec 2) :
    (@installedState a samples raw).phase = .free := by
  change phaseLift (sampled ({} : Carrier a) samples).phase = .free
  rw [sampled_phase]
  rfl

theorem initialized_generation (samples : List (Values Core.Input)) (raw : BitVec 2) :
    (@installedState a samples raw).generation = 1 := by
  change (sampled ({} : Carrier a) samples).generation + 1 = 1
  rw [sampled_generation]
  rfl

theorem sampled_transfer (s : Carrier a) (samples : List (Values Core.Input)) :
    (sampled s samples).transfer = s.transfer := by
  induction samples generalizing s with
  | nil => rfl
  | cons i rest ih =>
    change (sampled (s.sample (i .rawInputs)) rest).transfer = s.transfer
    exact (ih _).trans rfl

theorem initialized_transfer (samples : List (Values Core.Input)) (raw : BitVec 2) :
    (@installedState a samples raw).transfer = 0 := by
  change (sampled ({} : Carrier a) samples).transfer = 0
  rw [sampled_transfer]

theorem initialized_samples (samples : List (Values Core.Input)) (raw : BitVec 2) :
    (@installedState a samples raw).samplerFirst = raw ∧
    (@installedState a samples raw).samplerSecond = (sampled ({} : Carrier a) samples).samplerFirst :=
  ⟨rfl,rfl⟩

end Pinwheel.Hardware.StreamingReady.Initialization
