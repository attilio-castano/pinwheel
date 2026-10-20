import Pinwheel.Program.StreamingReady
import Pinwheel.Program.StreamingCompile

/-! Static compilation for the separate sampled-ready target. Certificates bind
source shape and every encoded word; they contain no execution-agreement premise. -/
namespace Pinwheel.Program.StreamingReady
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false

def Guard.Canonical (g : Guard) : Prop := g.expected &&& ~~~g.mask = 0
instance (g : Guard) : Decidable g.Canonical := inferInstanceAs (Decidable (_ = _))

def guardWord (g : Guard) (high : Bool) : BitVec 14 :=
  (0 : BitVec 1) ++ BitVec.ofBool high ++ g.limit.budget ++ g.expected ++ g.mask

def cellWord (c : Cell) (opcode : BitVec 3) (g : Guard := {}) (high : Bool := false) : BitVec 64 :=
  guardWord g high ++ c.lastHighEnabled ++ c.lastLowEnabled ++
  BitVec.ofBool c.txEnableMode ++ BitVec.ofBool c.txInvert ++
  c.lastHighLevels ++ c.lastLowLevels ++ BitVec.ofBool c.receive ++
  BitVec.ofBool c.transmit ++ BitVec.ofNat 1 c.rxInput.val ++
  BitVec.ofNat 2 c.txOutput.val ++ c.highPins.enabled ++ c.highPins.levels ++
  c.lowPins.enabled ++ c.lowPins.levels ++ BitVec.ofNat 8 c.highDuration.val ++
  BitVec.ofNat 8 c.lowDuration.val ++ opcode

def encode : Instruction → BitVec 64
  | .pulse c => cellWord c 0
  | .stream c none => cellWord c 1
  | .stream c (some g) => cellWord c 1 g true
  | .driveWait pins g => cellWord {lowPins := pins} 4 g
  | .halt => 2
  | .fault => 3

def operation : Instruction → BitVec 3
  | .pulse _ => 0 | .stream _ _ => 1 | .halt => 2 | .fault => 3 | .driveWait _ _ => 4

structure WordFields (word : BitVec 64) (c : Cell) (opcode : BitVec 3) (g : Guard) (high : Bool) : Prop where
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
  guardMask : word.extractLsb' 50 2 = g.mask
  guardExpected : word.extractLsb' 52 2 = g.expected
  guardBudget : word.extractLsb' 54 8 = g.limit.budget
  highGuard : word.extractLsb' 62 1 = BitVec.ofBool high
  reserved : word.extractLsb' 63 1 = 0

theorem cellWord_fields (c : Cell) (opcode : BitVec 3) (g : Guard) (high : Bool) :
    WordFields (cellWord c opcode g high) c opcode g high := by
  constructor
  all_goals unfold cellWord guardWord
  all_goals repeat first
    | rw [BitVec.extractLsb'_append_eq_of_le (by decide)]
    | rw [BitVec.extractLsb'_append_eq_of_add_le (by decide)]
  all_goals simp
  done

theorem cellWord_legacy (c : Cell) (opcode : BitVec 3) :
    cellWord c opcode = Streaming.cellWord c opcode := rfl

theorem encode_fields (instruction : Instruction) :
    WordFields (encode instruction) instruction.cell (operation instruction)
      instruction.guard instruction.hasHighGuard := by
  cases instruction with
  | pulse c => exact cellWord_fields c 0 {} false
  | stream c guard =>
    cases guard with
    | none => exact cellWord_fields c 1 {} false
    | some g => exact cellWord_fields c 1 g true
  | driveWait pins guard => exact cellWord_fields {lowPins := pins} 4 guard false
  | halt => constructor <;> rfl
  | fault => constructor <;> rfl
  done

def Instruction.Canonical : Instruction → Prop
  | .pulse c => Streaming.Cell.PulseCanonical c
  | .stream _ none | .halt | .fault => True
  | .stream _ (some g) | .driveWait _ g => g.Canonical

instance (i : Instruction) : Decidable i.Canonical := by
  cases i with
  | stream c guard => cases guard <;> simp only [Instruction.Canonical] <;> infer_instance
  | _ => simp only [Instruction.Canonical] <;> infer_instance

def wordCanonical (word : BitVec 64) : Bool :=
  let opcode := word.extractLsb' 0 3
  let guardCanonical := word.extractLsb' 52 2 &&& ~~~(word.extractLsb' 50 2) == 0
  if opcode == 0 then word.extractLsb' 31 33 == 0
  else if opcode == 1 then word.extractLsb' 63 1 == 0 &&
    (if (word.extractLsb' 62 1).getLsbD 0 then guardCanonical else word.extractLsb' 50 12 == 0) &&
    decide ((word.extractLsb' 31 2).toNat < 3)
  else if opcode == 4 then guardCanonical && word.extractLsb' 3 16 == 0 &&
    word.extractLsb' 25 25 == 0 && word.extractLsb' 62 2 == 0
  else word == 2 || word == 3

theorem driveWait_unused (pins : Pins) (g : Guard) :
    (encode (.driveWait pins g)).extractLsb' 3 16 = 0 ∧
    (encode (.driveWait pins g)).extractLsb' 25 25 = 0 ∧
    (encode (.driveWait pins g)).extractLsb' 62 2 = 0 := by
  constructor
  · unfold encode cellWord guardWord
    repeat (rw [BitVec.extractLsb'_append_eq_ite]; simp)
  · constructor
    all_goals unfold encode cellWord guardWord
    all_goals repeat (rw [BitVec.extractLsb'_append_eq_ite]; simp)
  done

theorem encode_canonical (instruction : Instruction) (canonical : instruction.Canonical) :
    wordCanonical (encode instruction) = true := by
  cases instruction with
  | driveWait pins g =>
    have fields := cellWord_fields ({lowPins := pins} : Cell) 4 g false
    simp only [encode,wordCanonical,fields.operation,show ((4 : BitVec 3) == 0) = false from rfl,
      show ((4 : BitVec 3) == 1) = false from rfl,beq_self_eq_true,↓reduceIte,
      fields.guardMask,fields.guardExpected]
    have unused := driveWait_unused pins g
    change (g.expected &&& ~~~g.mask == 0 &&
      (encode (.driveWait pins g)).extractLsb' 3 16 == 0 &&
      (encode (.driveWait pins g)).extractLsb' 25 25 == 0 &&
      (encode (.driveWait pins g)).extractLsb' 62 2 == 0) = true
    simp only [show g.expected &&& ~~~g.mask = 0 from canonical,unused.1,unused.2.1,unused.2.2,
      beq_self_eq_true,Bool.and_self]
  | pulse c =>
    unfold encode wordCanonical
    rw [(cellWord_fields c 0 {} false).operation]
    simp only [beq_self_eq_true,↓reduceIte,cellWord_legacy,
      Streaming.cellWord_pulse_upper c canonical]
  | stream c guard =>
    cases guard with
    | none =>
      have fields := cellWord_fields c 1 {} false
      have upper : (cellWord c 1).extractLsb' 50 12 = 0 := by
        unfold cellWord guardWord
        repeat first
          | rw [BitVec.extractLsb'_append_eq_of_le (by decide)]
          | rw [BitVec.extractLsb'_append_eq_of_add_le (by decide)]
        rfl
      have bound : c.txOutput.val < 2^2 := by have := c.txOutput.isLt; omega
      unfold encode wordCanonical
      rw [fields.operation]
      simp only [show ((1 : BitVec 3) == 0) = false from rfl,beq_self_eq_true,
        Bool.false_eq_true,↓reduceIte,fields.reserved,fields.highGuard,
        BitVec.getLsbD_ofBool,upper,fields.txOutput,BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt bound,Bool.true_and]
      exact decide_eq_true c.txOutput.isLt
    | some g =>
      have fields := cellWord_fields c 1 g true
      have guard : g.expected &&& ~~~g.mask = 0 := canonical
      have bound : c.txOutput.val < 2^2 := by have := c.txOutput.isLt; omega
      unfold encode wordCanonical
      rw [fields.operation]
      simp only [show ((1 : BitVec 3) == 0) = false from rfl,beq_self_eq_true,
        Bool.false_eq_true,↓reduceIte,fields.reserved,fields.highGuard,
        BitVec.getLsbD_ofBool,fields.guardMask,fields.guardExpected,
        fields.txOutput,guard,BitVec.toNat_ofNat,Nat.mod_eq_of_lt bound,Bool.true_and]
      exact decide_eq_true c.txOutput.isLt
  | halt => decide
  | fault => decide
  done


def supportedFrom (seen : Bool) : List Instruction → Bool
  | [] => false
  | .pulse _ :: rest | .driveWait _ _ :: rest => supportedFrom seen rest
  | .stream _ _ :: rest => !seen && supportedFrom true rest
  | [.halt] | [.fault] => seen
  | .halt :: _ | .fault :: _ => false

def Program.WellFormed (p : Program) : Prop :=
  (p.memory.toList.take p.length).countP Instruction.isStream ≤ 1

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
  else .error "Unsupported Ready source: require 1..64 rows, canonical operands, one stream and final halt/fault"

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

def liftInstruction : Streaming.Instruction → Instruction
  | .pulse c => .pulse c | .stream c => .stream c none | .halt => .halt | .fault => .fault

theorem encode_lift (instruction : Streaming.Instruction) :
    encode (liftInstruction instruction) = Streaming.encode instruction := by
  cases instruction <;> rfl

/-- These digital peer assumptions are explicit profile evidence. They are not
electrical timing claims, and generic Ready programs need not satisfy them. -/
structure I2cProfile where
  lowDuration : Fin 256
  highDuration : Fin 256
  budgetMinusOne : Fin 255
  peerTco : Nat
  stretchBound : Nat
  lowMin : 2 ≤ lowDuration.val
  highMin : 2 ≤ highDuration.val
  lowMargin : peerTco + 3 ≤ lowDuration.val + 1
  waitMargin : stretchBound + 3 ≤ budgetMinusOne.val + 1

def I2cProfile.standard : I2cProfile :=
  ⟨3,3,30,1,28,by decide,by decide,by decide,by decide⟩

def i2cGuard (profile : I2cProfile) (mask expected : BitVec 2) : Guard :=
  ⟨mask,expected,.misses profile.budgetMinusOne⟩

def i2cHold (profile : I2cProfile) (enabled : BitVec 3) : Instruction :=
  .pulse {
    lowDuration := profile.highDuration,highDuration := profile.highDuration,
    lowPins := ⟨0,enabled⟩,highPins := ⟨0,enabled⟩}

/-- STOP preparation keeps both open-drain outputs low. Its LOW segment
uses the declared LOW duration even when LOW and HIGH are asymmetric. -/
def i2cStopLow (profile : I2cProfile) : Instruction :=
  .pulse {
    lowDuration := profile.lowDuration,highDuration := profile.highDuration,
    lowPins := ⟨0,3⟩,highPins := ⟨0,3⟩}

def i2cCell (profile : I2cProfile) : Cell :=
  {lowDuration := profile.lowDuration,highDuration := profile.highDuration,
   lowPins := ⟨0,1⟩,highPins := ⟨0,0⟩,txOutput := 1,rxInput := 1,
   transmit := true,receive := true,txEnableMode := true}

/-- SCL output0/raw0 and SDA output1/raw1 match the existing physical board links.
One address plus64 data bytes use585 external host-packed slots under one START.
The same image supports read or write; no byte/ACK selector occurs in hardware. -/
def i2cSource (profile : I2cProfile) : List Instruction :=
  [.driveWait ⟨0,0⟩ (i2cGuard profile 3 3),
   i2cHold profile 2,
   .stream (i2cCell profile) (some (i2cGuard profile 1 1)),
   i2cStopLow profile,
   .driveWait ⟨0,2⟩ (i2cGuard profile 1 1),
   i2cHold profile 2,
   .halt]

theorem i2c_supported (profile : I2cProfile) : Supported (i2cSource profile) := by
  simp [Supported,i2cSource,i2cHold,i2cStopLow,supportedFrom,List.countP_cons,Instruction.isStream,
    Instruction.Canonical,Streaming.Cell.PulseCanonical,i2cGuard,Guard.Canonical]
  done

def i2cImage (profile : I2cProfile := .standard) : Compiled (i2cSource profile) (Engine.Reactive.Pins.mk 0 0) :=
  ⟨(i2cSource profile).map encode,i2c_supported profile,rfl⟩

theorem i2c_rows (profile : I2cProfile) : (i2cImage profile).words.length = 7 := rfl

theorem i2c_budget_positive (profile : I2cProfile) :
    0 < (i2cGuard profile 1 1).limit.budget.toNat := by
  change 0 < (BitVec.ofNat 8 (profile.budgetMinusOne.val + 1)).toNat
  rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by have := profile.budgetMinusOne.isLt; omega)]
  omega

theorem i2c_timing (profile : I2cProfile) :
    3 ≤ profile.lowDuration.val + 1 ∧ 3 ≤ profile.highDuration.val + 1 ∧
    profile.peerTco + 3 ≤ profile.lowDuration.val + 1 ∧
    profile.stretchBound + 3 ≤ profile.budgetMinusOne.val + 1 := by
  have low := profile.lowMin
  have high := profile.highMin
  exact ⟨by omega,by omega,profile.lowMargin,profile.waitMargin⟩

theorem i2c_stop_low_fields (profile : I2cProfile) :
    (i2cSource profile)[3]? = some (i2cStopLow profile) ∧
    (i2cStopLow profile).cell.lowDuration = profile.lowDuration ∧
    (i2cStopLow profile).cell.highDuration = profile.highDuration ∧
    (i2cStopLow profile).cell.lowPins = Engine.Reactive.Pins.mk 0 3 ∧
    (i2cStopLow profile).cell.highPins = Engine.Reactive.Pins.mk 0 3 := by
  exact ⟨rfl,rfl,rfl,rfl,rfl⟩

theorem i2c_stop_low_cycles (profile : I2cProfile) :
    profile.lowDuration.val + 1 ≤
      (i2cStopLow profile).cell.lowDuration.val + 1 +
        ((i2cStopLow profile).cell.highDuration.val + 1) := by
  change profile.lowDuration.val + 1 ≤
    profile.lowDuration.val + 1 + (profile.highDuration.val + 1)
  omega

end Pinwheel.Program.StreamingReady
