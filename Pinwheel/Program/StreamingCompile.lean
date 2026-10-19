import Pinwheel.Program.Streaming

/-! A finite source compiler for the separate streaming ISA. Its certificate
contains only source shape and exact canonical words, never runtime agreement. -/
namespace Pinwheel.Program.Streaming
set_option maxRecDepth 4096

def Cell.PulseCanonical (c : Cell) : Prop :=
  c.txOutput = 0 ∧ c.rxInput = 0 ∧ c.transmit = false ∧ c.receive = false ∧
  c.lastLowLevels = 0 ∧ c.lastHighLevels = 0 ∧ c.txInvert = false ∧
  c.txEnableMode = false ∧ c.lastLowEnabled = 0 ∧ c.lastHighEnabled = 0

instance (c : Cell) : Decidable c.PulseCanonical := inferInstanceAs (Decidable (_ ∧ _))

def cellWord (c : Cell) (opcode : BitVec 3) : BitVec 64 :=
  (0 : BitVec 14) ++ c.lastHighEnabled ++ c.lastLowEnabled ++
  BitVec.ofBool c.txEnableMode ++ BitVec.ofBool c.txInvert ++
  c.lastHighLevels ++ c.lastLowLevels ++ BitVec.ofBool c.receive ++
  BitVec.ofBool c.transmit ++ BitVec.ofNat 1 c.rxInput.val ++
  BitVec.ofNat 2 c.txOutput.val ++ c.highPins.enabled ++ c.highPins.levels ++
  c.lowPins.enabled ++ c.lowPins.levels ++ BitVec.ofNat 8 c.highDuration.val ++
  BitVec.ofNat 8 c.lowDuration.val ++ opcode

def encode : Instruction → BitVec 64
  | .pulse c => cellWord c 0
  | .stream c => cellWord c 1
  | .halt => 2
  | .fault => 3

theorem cellWord_lowDuration (c : Cell) (opcode : BitVec 3) :
    (cellWord c opcode).extractLsb' 3 8 = BitVec.ofNat 8 c.lowDuration.val := by
  unfold cellWord
  rw [BitVec.extractLsb'_append_eq_of_le (by decide),
    BitVec.extractLsb'_append_eq_of_add_le (by decide)]
  simp
  done

theorem cellWord_highDuration (c : Cell) (opcode : BitVec 3) :
    (cellWord c opcode).extractLsb' 11 8 = BitVec.ofNat 8 c.highDuration.val := by
  unfold cellWord
  repeat first
    | rw [BitVec.extractLsb'_append_eq_of_le (by decide)]
    | rw [BitVec.extractLsb'_append_eq_of_add_le (by decide)]
  simp
  done

structure WordFields (word : BitVec 64) (c : Cell) (opcode : BitVec 3) : Prop where
  operation : word.extractLsb' 0 3 = opcode
  lowDuration : word.extractLsb' 3 8 = BitVec.ofNat 8 c.lowDuration.val
  highDuration : word.extractLsb' 11 8 = BitVec.ofNat 8 c.highDuration.val
  lowLevels : word.extractLsb' 19 3 = c.lowPins.levels
  lowEnabled : word.extractLsb' 22 3 = c.lowPins.enabled
  highLevels : word.extractLsb' 25 3 = c.highPins.levels
  highEnabled : word.extractLsb' 28 3 = c.highPins.enabled
  txOutput : word.extractLsb' 31 2 = BitVec.ofNat 2 c.txOutput.val
  rxInput : word.extractLsb' 33 1 = BitVec.ofNat 1 c.rxInput.val
  transmit : word.extractLsb' 34 1 = BitVec.ofBool c.transmit
  receive : word.extractLsb' 35 1 = BitVec.ofBool c.receive
  lastLowLevels : word.extractLsb' 36 3 = c.lastLowLevels
  lastHighLevels : word.extractLsb' 39 3 = c.lastHighLevels
  txInvert : word.extractLsb' 42 1 = BitVec.ofBool c.txInvert
  txEnableMode : word.extractLsb' 43 1 = BitVec.ofBool c.txEnableMode
  lastLowEnabled : word.extractLsb' 44 3 = c.lastLowEnabled
  lastHighEnabled : word.extractLsb' 47 3 = c.lastHighEnabled
  reserved : word.extractLsb' 50 14 = 0

theorem cellWord_fields (c : Cell) (opcode : BitVec 3) : WordFields (cellWord c opcode) c opcode := by
  constructor
  all_goals unfold cellWord
  all_goals repeat first
    | rw [BitVec.extractLsb'_append_eq_of_le (by decide)]
    | rw [BitVec.extractLsb'_append_eq_of_add_le (by decide)]
  all_goals simp
  done

def Instruction.Canonical : Instruction → Prop
  | .pulse c => c.PulseCanonical
  | _ => True

instance (i : Instruction) : Decidable i.Canonical := by
  cases i <;> simp only [Instruction.Canonical] <;> infer_instance

def wordCanonical (word : BitVec 64) : Bool :=
  let opcode := word.extractLsb' 0 3
  if opcode == 0 then word.extractLsb' 31 33 == 0
  else if opcode == 1 then word.extractLsb' 50 14 == 0 &&
    decide ((word.extractLsb' 31 2).toNat < 3)
  else word == 2 || word == 3

theorem cellWord_pulse_upper (c : Cell) (h : c.PulseCanonical) :
    (cellWord c 0).extractLsb' 31 33 = 0 := by
  rcases h with ⟨ho,hi,ht,hr,hl,hh,hv,hm,hle,hhe⟩
  unfold cellWord
  repeat first
    | rw [BitVec.extractLsb'_append_eq_of_le (by decide)]
    | rw [BitVec.extractLsb'_append_eq_of_add_le (by decide)]
  simp [ho,hi,ht,hr,hl,hh,hv,hm,hle,hhe]
  done

theorem encode_canonical (i : Instruction) (h : i.Canonical) : wordCanonical (encode i) = true := by
  cases i with
  | pulse c =>
      simp only [encode,wordCanonical,(cellWord_fields c 0).operation,beq_self_eq_true,↓reduceIte]
      exact beq_iff_eq.mpr (cellWord_pulse_upper c h)
  | stream c =>
      simp only [encode,wordCanonical,(cellWord_fields c 1).operation,
        show ((1 : BitVec 3) == 0) = false from rfl,↓reduceIte,beq_self_eq_true,
        (cellWord_fields c 1).reserved,(cellWord_fields c 1).txOutput,Bool.true_and]
      simp only [Bool.false_eq_true,↓reduceIte,BitVec.toNat_ofNat]
      have bound : c.txOutput.val < 2 ^ 2 := by have := c.txOutput.isLt; omega
      simpa only [Nat.mod_eq_of_lt bound] using decide_eq_true c.txOutput.isLt
      done
  | halt => decide
  | fault => decide
  done

/-- A finite scan admits pulse prefixes/suffixes around exactly one stream,
followed by one terminal. It inspects no transfer data or runtime state. -/
def supportedFrom (seen : Bool) : List Instruction → Bool
  | [] => false
  | .pulse _ :: rest => supportedFrom seen rest
  | .stream _ :: rest => !seen && supportedFrom true rest
  | [.halt] | [.fault] => seen
  | .halt :: _ | .fault :: _ => false

def Supported (source : List Instruction) : Prop :=
  0 < source.length ∧ source.length ≤ 64 ∧ supportedFrom false source = true ∧
    source.countP Instruction.isStream = 1 ∧ ∀ i ∈ source, i.Canonical

instance (source : List Instruction) : Decidable (Supported source) := by
  unfold Supported
  infer_instance

structure Compiled (source : List Instruction) (idle : Engine.Reactive.Pins) where
  words : List (BitVec 64)
  sourceValid : Supported source
  wordsEqual : words = source.map encode

def compile (source : List Instruction) (idle : Engine.Reactive.Pins := {}) :
    Except String (Compiled source idle) :=
  if h : Supported source then .ok ⟨source.map encode,h,rfl⟩
  else .error "Unsupported streaming source: require 1..64 rows, canonical pulses, one stream and final halt/fault"

theorem compile_accepts (source : List Instruction) (idle : Engine.Reactive.Pins)
    (h : Supported source) : ∃ image, compile source idle = .ok image := by
  simp only [compile,dif_pos h]
  exact ⟨_,rfl⟩

theorem compile_rejects (source : List Instruction) (idle : Engine.Reactive.Pins)
    (h : ¬ Supported source) : ∃ error, compile source idle = .error error := by
  simp only [compile,dif_neg h]
  exact ⟨_,rfl⟩

theorem Compiled.rows (image : Compiled source idle) : 0 < image.words.length ∧ image.words.length ≤ 64 := by
  simpa only [image.wordsEqual,List.length_map] using
    And.intro image.sourceValid.1 image.sourceValid.2.1

theorem Compiled.canonical (image : Compiled source idle) (word : BitVec 64)
    (member : word ∈ image.words) : wordCanonical word = true := by
  rw [image.wordsEqual] at member
  obtain ⟨instruction,hinstruction,rfl⟩ := List.mem_map.mp member
  exact encode_canonical instruction (image.sourceValid.2.2.2.2 instruction hinstruction)

def Compiled.program (image : Compiled source idle) : Program :=
  {memory := Vector.ofFn fun k => source[k.val]?.getD .halt
   lengthMinusOne := ⟨source.length - 1, by have := image.sourceValid.2.1; omega⟩
   idle := idle}

theorem Compiled.program_length (image : Compiled source idle) : image.program.length = source.length := by
  simp only [Compiled.program,Program.length]
  have := image.sourceValid.1
  omega

theorem Compiled.program_fetch (image : Compiled source idle) (k : Nat) (hk : k < source.length) :
    image.program.fetch k = source[k]? := by
  have hkp : k < image.program.length := by simpa only [image.program_length] using hk
  unfold Program.fetch
  rw [dif_pos hkp]
  simp only [Compiled.program,Vector.getElem_ofFn]
  simp [List.getElem?_eq_getElem hk]
  done

theorem Compiled.installed (image : Compiled source idle) :
    image.program.memory.toList.take image.program.length = source := by
  apply List.ext_getElem
  · simp only [List.length_take,Vector.length_toList,image.program_length]
    exact Nat.min_eq_left image.sourceValid.2.1
  · intro k hk hs
    simp only [List.getElem_take,Vector.getElem_toList,Compiled.program,Vector.getElem_ofFn]
    simp [List.getElem?_eq_getElem hs]
  done

theorem Compiled.wellFormed (image : Compiled source idle) : image.program.WellFormed := by
  unfold Program.WellFormed
  rw [image.installed,image.sourceValid.2.2.2.1]
  decide

def spiCell (duration : Fin 256) : Cell :=
  {lowDuration := duration, highDuration := duration, lowPins := ⟨0,7⟩,
   highPins := ⟨2,7⟩, transmit := true, receive := true}

/-- The finishing pulse holds CS asserted/SCK low through both phases and
the pulse's return to LOW. Only HALT releases CS into the declared idle pins. -/
def spiSource (duration : Fin 256) : List Instruction :=
  [.pulse {lowDuration := duration,highDuration := duration,lowPins := ⟨0,7⟩,highPins := ⟨0,7⟩},
   .stream (spiCell duration),
   .pulse {lowDuration := duration,highDuration := duration,lowPins := ⟨0,7⟩,highPins := ⟨0,7⟩},
   .halt]

theorem spi_supported (duration : Fin 256) : Supported (spiSource duration) := by
  simp [Supported,spiSource,supportedFrom,List.countP_cons,Instruction.isStream,
    Instruction.Canonical,Cell.PulseCanonical]
  done

def spiImage (duration : Fin 256) : Compiled (spiSource duration) (Engine.Reactive.Pins.mk 4 7) :=
  ⟨(spiSource duration).map encode,spi_supported duration,rfl⟩

def jtagPulse (duration : Fin 256) (tms : Bool) : Instruction :=
  .pulse {
    lowDuration := duration,highDuration := duration,
    lowPins := ⟨(if tms then 4 else 0),7⟩,highPins := ⟨(if tms then 6 else 2),7⟩}

def jtagCell (duration : Fin 256) : Cell :=
  {lowDuration := duration,highDuration := duration,lowPins := ⟨0,7⟩,highPins := ⟨2,7⟩,
   transmit := true,receive := true,lastLowLevels := 4,lastHighLevels := 4}

def jtagSource (duration : Fin 256) : List Instruction :=
  [jtagPulse duration true,jtagPulse duration true,jtagPulse duration true,
   jtagPulse duration true,jtagPulse duration true,jtagPulse duration false,
   jtagPulse duration true,jtagPulse duration false,jtagPulse duration false,
   .stream (jtagCell duration),jtagPulse duration true,jtagPulse duration false,.halt]

theorem jtag_supported (duration : Fin 256) : Supported (jtagSource duration) := by
  simp [Supported,jtagSource,jtagPulse,supportedFrom,List.countP_cons,Instruction.isStream,
    Instruction.Canonical,Cell.PulseCanonical]
  done

def jtagImage (duration : Fin 256) : Compiled (jtagSource duration) (Engine.Reactive.Pins.mk 0 7) :=
  ⟨(jtagSource duration).map encode,jtag_supported duration,rfl⟩

/-- These pin equations, rather than a protocol tag in hardware, expose the
safe low-clock park state and JTAG's final-bit TMS override. -/
theorem spi_park (duration : Fin 256) :
    (spiCell duration).lowPins = ⟨0,7⟩ ∧ (spiCell duration).highPins = ⟨2,7⟩ ∧
    (spiCell duration).lastLowLevels = 0 ∧ (spiCell duration).lastHighLevels = 0 := by
  exact ⟨rfl,rfl,rfl,rfl⟩

theorem jtag_park (duration : Fin 256) :
    (jtagCell duration).lowPins = ⟨0,7⟩ ∧ (jtagCell duration).highPins = ⟨2,7⟩ ∧
    (jtagCell duration).lastLowLevels = 4 ∧ (jtagCell duration).lastHighLevels = 4 := by
  exact ⟨rfl,rfl,rfl,rfl⟩

end Pinwheel.Program.Streaming
