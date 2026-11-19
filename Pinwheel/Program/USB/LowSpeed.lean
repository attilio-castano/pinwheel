import Pinwheel.Program.StreamingBitTrace
import Std
namespace Pinwheel.USBPacketFeasibility
open BitVec

def usbCrcStep (r : BitVec 16) (b : Bool) : BitVec 16 :=
  (r >>> 1) ^^^ (if r.getLsbD 0 != b then 0xA001#16 else 0#16)

theorem usbCrcStep_xor (r s : BitVec 16) (a b : Bool) :
    usbCrcStep (r ^^^ s) (a ^^ b) = (usbCrcStep r a ^^^ usbCrcStep s b) := by
  ext i h
  cases a <;> cases b <;> cases hr : r[0] <;> cases hs : s[0] <;>
    simp [usbCrcStep, hr, hs, Bool.xor_left_comm, Bool.xor_comm]
  done

theorem usbCrcFold_xor (xs ys : List Bool) (sameLength : xs.length = ys.length)
    (r s : BitVec 16) :
    (List.zipWith Bool.xor xs ys).foldl usbCrcStep (r ^^^ s) =
      (xs.foldl usbCrcStep r ^^^ ys.foldl usbCrcStep s) := by
  induction xs generalizing ys r s with
  | nil => cases ys <;> simp_all
  | cons x xs ih =>
    cases ys with
    | nil => simp at sameLength
    | cons y ys =>
      simpa [usbCrcStep_xor] using ih ys (by simpa using sameLength)
        (usbCrcStep r x) (usbCrcStep s y)
  done

def usbCrcResult (xs : List Bool) : BitVec 16 :=
  xs.foldl usbCrcStep 0xFFFF#16 ^^^ 0xFFFF#16

theorem usbCrcAdjacentImpulse :
    ∀ i : Fin 63,
      ((List.range 64).map (fun j => j == i.val || j == i.val+1)).foldl usbCrcStep 0 ≠ 0 := by
  decide +kernel
  done

theorem usbCrcResult_difference (xs ys : List Bool) (h : xs.length = ys.length) :
    usbCrcResult xs ^^^ usbCrcResult ys =
      (List.zipWith Bool.xor xs ys).foldl usbCrcStep 0 := by
  unfold usbCrcResult
  calc
    _ = (xs.foldl usbCrcStep 0xFFFF#16 ^^^ ys.foldl usbCrcStep 0xFFFF#16) ^^^
        (0xFFFF#16 ^^^ 0xFFFF#16) := by ac_rfl
    _ = _ := by
      rw [← usbCrcFold_xor xs ys h]
      simp
  done

theorem usbCrcRejectsAdjacentChanges (xs ys : List Bool) (h : xs.length = ys.length)
    (i : Fin 63)
    (delta : List.zipWith Bool.xor xs ys =
      (List.range 64).map (fun j => j == i.val || j == i.val+1)) :
    usbCrcResult xs ≠ usbCrcResult ys := by
  intro equal
  have zero : usbCrcResult xs ^^^ usbCrcResult ys = 0 := by simp [equal]
  rw [usbCrcResult_difference xs ys h, delta] at zero
  exact usbCrcAdjacentImpulse i zero
  done

def crcLowBits : Nat → BitVec 16 → List Bool
  | 0, _ => []
  | n + 1, state => state.getLsbD 0 :: crcLowBits n (state >>> 1)

theorem crc_low_bits_length (n : Nat) (state : BitVec 16) :
    (crcLowBits n state).length = n := by
  induction n generalizing state with
  | zero => rfl
  | succ n ih => simp [crcLowBits, ih]
  done

theorem crc_feed_own_remainder (n : Nat) (state : BitVec 16) :
    (crcLowBits n state).foldl usbCrcStep state = state >>> n := by
  induction n generalizing state with
  | zero => simp [crcLowBits, BitVec.ushiftRight_zero]
  | succ n ih =>
    simp only [crcLowBits, List.foldl_cons, usbCrcStep, bne_self_eq_false,
      Bool.false_eq_true, if_false, BitVec.xor_zero]
    rw [ih, ← BitVec.shiftRight_add, Nat.add_comm 1 n]
  done

theorem crc_xor_with_one_bits (n : Nat) (state : BitVec 16) :
    List.zipWith Bool.xor (crcLowBits n state) (List.replicate n true) =
      (crcLowBits n state).map Bool.not := by
  induction n generalizing state with
  | zero => rfl
  | succ n ih => simp [crcLowBits, List.replicate_succ, ih]
  done

theorem crc_residue (state : BitVec 16) :
    ((crcLowBits 16 state).map Bool.not).foldl usbCrcStep state = 0xB001#16 := by
  have lengthMatch : (crcLowBits 16 state).length = (List.replicate 16 true).length := by
    simp [crc_low_bits_length]
  have xorResult := usbCrcFold_xor (crcLowBits 16 state) (List.replicate 16 true) lengthMatch
    state 0#16
  rw [crc_xor_with_one_bits, BitVec.xor_zero, crc_feed_own_remainder,
    BitVec.ushiftRight_eq_zero (by decide), BitVec.zero_xor] at xorResult
  exact xorResult.trans (by decide +kernel)
  done

theorem zero_step_msb (state : BitVec 16) :
    (usbCrcStep state false).getLsbD 15 = state.getLsbD 0 := by
  cases bit : state[0] <;> simp [usbCrcStep, bit]
  done

theorem crc_zero_step_injective (l r : BitVec 16)
    (same : usbCrcStep l false = usbCrcStep r false) : l = r := by
  have low : l.getLsbD 0 = r.getLsbD 0 := by
    simpa only [zero_step_msb] using congrArg (fun x : BitVec 16 => x.getLsbD 15) same
  have high : l >>> (1 : Nat) = r >>> (1 : Nat) := by
    unfold usbCrcStep at same
    rw [low] at same
    exact (BitVec.xor_left_inj _).mp same
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  cases i with
  | zero => exact low
  | succ i =>
    simpa [BitVec.getLsbD_ushiftRight, Nat.add_comm] using
      congrArg (fun x : BitVec 16 => x.getLsbD i) high
  done

theorem crc_zero_run_injective (n : Nat) (l r : BitVec 16)
    (same : (List.replicate n false).foldl usbCrcStep l =
      (List.replicate n false).foldl usbCrcStep r) : l = r := by
  induction n generalizing l r with
  | zero => exact same
  | succ n ih =>
    apply crc_zero_step_injective
    apply ih
    simpa only [List.replicate_succ, List.foldl_cons] using same
  done

theorem crc_zip_zeros (bits : List Bool) :
    List.zipWith Bool.xor bits (List.replicate bits.length false) = bits := by
  induction bits with
  | nil => rfl
  | cons bit rest ih => simp [List.replicate_succ, ih]
  done

theorem crc_trailer_transform (state trailer : BitVec 16) :
    (crcLowBits 16 trailer).foldl usbCrcStep state =
      (List.replicate 16 false).foldl usbCrcStep (state ^^^ trailer) := by
  let bits := crcLowBits 16 trailer
  have count : bits.length = 16 := crc_low_bits_length _ _
  have masked : trailer ^^^ (state ^^^ trailer) = state := by
    rw [← BitVec.xor_assoc, BitVec.xor_comm trailer state, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
  have zip : List.zipWith Bool.xor bits (List.replicate 16 false) = bits := by
    simpa [count] using crc_zip_zeros bits
  have h := usbCrcFold_xor bits (List.replicate 16 false) (by simp [count])
    trailer (state ^^^ trailer)
  rw [zip, masked] at h
  change bits.foldl usbCrcStep state = _
  have own : bits.foldl usbCrcStep trailer = 0#16 := by
    rw [show bits = crcLowBits 16 trailer by rfl, crc_feed_own_remainder]
    exact BitVec.ushiftRight_eq_zero (by decide)
  rw [own, BitVec.zero_xor] at h
  exact h
  done

theorem crc_trailer_injective (state a b : BitVec 16)
    (same : (crcLowBits 16 a).foldl usbCrcStep state =
      (crcLowBits 16 b).foldl usbCrcStep state) : a = b := by
  rw [crc_trailer_transform, crc_trailer_transform] at same
  exact (BitVec.xor_right_inj state).mp (crc_zero_run_injective 16 _ _ same)
  done

theorem crc_low_bits_nth (n i : Nat) (state : BitVec 16) (index : i < (crcLowBits n state).length) :
    (crcLowBits n state)[i] = state.getLsbD i := by
  induction n generalizing i state with
  | zero => simp [crcLowBits] at index
  | succ n ih =>
    cases i with
    | zero => rfl
    | succ i =>
      simpa [crcLowBits, BitVec.getLsbD_ushiftRight, Nat.add_comm] using
        ih i (state >>> (1 : Nat)) (by simpa [crcLowBits] using index)
  done

theorem crc_low_bits_complement (state : BitVec 16) :
    crcLowBits 16 (~~~state) = (crcLowBits 16 state).map Bool.not := by
  apply List.ext_getElem
  · simp [crc_low_bits_length]
  · intro i ha hb
    have inRange : i < 16 := by simpa [crc_low_bits_length] using ha
    simp [crc_low_bits_nth, inRange]
  done

theorem crc_residue_iff_correct_trailer (state trailer : BitVec 16) :
    (crcLowBits 16 trailer).foldl usbCrcStep state = 0xB001#16 ↔ trailer = ~~~state := by
  have correct : (crcLowBits 16 (~~~state)).foldl usbCrcStep state = 0xB001#16 := by
    rw [crc_low_bits_complement]
    exact crc_residue state
  constructor
  · intro accepted
    exact crc_trailer_injective state trailer _ (accepted.trans correct.symm)
  · intro exactTrailer
    rw [exactTrailer]
    exact correct
  done

def insertStuff : List Bool → Nat → List Bool
  | [], _ => []
  | false :: bits, _ => false :: insertStuff bits 0
  | true :: bits, run =>
    if run == 5 then true :: false :: insertStuff bits 0
    else true :: insertStuff bits (run + 1)

def removeStuff : List Bool → Nat → Option (List Bool)
  | [], run => if run == 6 then none else some []
  | bit :: bits, run =>
    if run == 6 then
      if bit then none else removeStuff bits 0
    else
      (removeStuff bits (if bit then run + 1 else 0)).map (bit :: ·)

theorem remove_insert_stuff (message : List Bool) (run : Nat) (supported : run ≤ 5) :
    removeStuff (insertStuff message run) run = some message := by
  induction message generalizing run with
  | nil =>
    have noBoundary : run ≠ 6 := by omega
    simp [insertStuff, removeStuff, noBoundary]
  | cons bit message ih =>
    have noBoundary : run ≠ 6 := by omega
    cases bit with
    | false =>
      simp [insertStuff, removeStuff, noBoundary, ih 0 (by decide)]
    | true =>
      by_cases full : run = 5
      · simp [full, insertStuff, removeStuff, ih 0 (by decide)]
      · have bound : run + 1 ≤ 5 := by omega
        simp [insertStuff, removeStuff, noBoundary, full, ih _ bound]
  done

def onesBound : List Bool → Nat → Bool
  | [], run => decide (run ≤ 6)
  | false :: bits, _ => onesBound bits 0
  | true :: bits, run => decide (run < 6) && onesBound bits (run + 1)

theorem stuffed_gap_bound (message : List Bool) (run : Nat) (supported : run ≤ 5) :
    onesBound (insertStuff message run) run = true := by
  induction message generalizing run with
  | nil =>
    simp [insertStuff, onesBound, show run ≤ 6 by omega]
  | cons bit message ih =>
    cases bit with
    | false =>
      simpa [insertStuff, onesBound] using ih 0 (by decide)
    | true =>
      by_cases full : run = 5
      · simpa [full, insertStuff, onesBound] using ih 0 (by decide)
      · have bound : run + 1 ≤ 5 := by omega
        have room : run < 6 := by omega
        simp [insertStuff, onesBound, room, full, ih _ bound]
  done

theorem invalid_stuffed_prefix :
    removeStuff [] 6 = none ∧ ∀ suffix, removeStuff (true :: suffix) 6 = none := by
  simp [removeStuff]
  done

def emitNRZI (previous : Bool) : List Bool → List Bool
  | [] => []
  | bit :: bits =>
    let level := if bit then previous else !previous
    level :: emitNRZI level bits

def readNRZI (previous : Bool) : List Bool → List Bool
  | [] => []
  | level :: levels => (level == previous) :: readNRZI level levels

theorem read_emit_nrzi (bits : List Bool) (previous : Bool) :
    readNRZI previous (emitNRZI previous bits) = bits := by
  induction bits generalizing previous with
  | nil => rfl
  | cons bit bits ih =>
    cases bit <;> cases previous <;> simp [emitNRZI, readNRZI, ih]
  done

theorem emit_read_nrzi (levels : List Bool) (previous : Bool) :
    emitNRZI previous (readNRZI previous levels) = levels := by
  induction levels generalizing previous with
  | nil => rfl
  | cons level levels ih =>
    cases level <;> cases previous <;> simp [emitNRZI, readNRZI, ih]
  done

def serialBits (width value : Nat) : List Bool :=
  (List.range width).map value.testBit

def header (pid : Nat) : List Bool := serialBits 8 0x80 ++ serialBits 8 pid

@[simp] theorem header_length (pid : Nat) : (header pid).length = 16 := by
  simp [header, serialBits]
  done

inductive Outcome where
  | data (bits : List Bool)
  | nak | stall
  | noReply | eop | stuff | header | length | crc
  deriving DecidableEq, Repr

def classifyBits (bits : List Bool) : Outcome :=
  if bits = header 0x5A then .nak
  else if bits = header 0x1E then .stall
  else if bits.take 16 ≠ header 0x4B then .header
  else if bits.length ≠ 96 then .length
  else
    let body := bits.drop 16
    if body.foldl usbCrcStep 0xFFFF#16 = 0xB001#16 then .data (body.take 64)
    else .crc

structure PinFrame where
  symbols : List Bool
  se0Clocks : Nat
  endsInJ : Bool

def decodePinFrame (reply : Option PinFrame) : Outcome :=
  match reply with
  | none => .noReply
  | some frame =>
    if frame.endsInJ && decide (31 ≤ frame.se0Clocks ∧ frame.se0Clocks ≤ 33) then
      match removeStuff (readNRZI false frame.symbols) 0 with
      | none => .stuff
      | some bits => classifyBits bits
    else .eop

def wireFrame (logical : List Bool) (width : Nat) : PinFrame :=
  ⟨emitNRZI false (insertStuff logical 0), width, true⟩

theorem decode_canonical_symbols (logical : List Bool) (width : Nat)
    (eopWidth : 31 ≤ width ∧ width ≤ 33) :
    decodePinFrame (some (wireFrame logical width)) = classifyBits logical := by
  simp [decodePinFrame, wireFrame, eopWidth, read_emit_nrzi, remove_insert_stuff]
  done

theorem observe_data_trailer (payload : List Bool) (size : payload.length = 64)
    (trailer : BitVec 16) :
    classifyBits (header 0x4B ++ (payload ++ crcLowBits 16 trailer)) =
      (if trailer = ~~~(payload.foldl usbCrcStep 0xFFFF#16) then .data payload else .crc) := by
  have packetSize : (header 0x4B ++ (payload ++ crcLowBits 16 trailer)).length = 96 := by
    simp [size, crc_low_bits_length]
  have neHand (pid : Nat) : header 0x4B ++ (payload ++ crcLowBits 16 trailer) ≠ header pid := by
    intro equal
    have lens := congrArg List.length equal
    simp [packetSize] at lens
  simp [classifyBits, neHand, List.take_left', List.drop_left', packetSize, size,
    List.foldl_append, crc_residue_iff_correct_trailer]
  done

def canonicalFrom (message : List Bool) (run : Nat) : List Bool :=
  if run = 6 then false :: insertStuff message 0 else insertStuff message run

theorem canonical_of_remove (wire message : List Bool) (run : Nat)
    (bounded : run ≤ 6) (parsed : removeStuff wire run = some message) :
    canonicalFrom message run = wire := by
  induction wire generalizing run message with
  | nil =>
    by_cases owed : run = 6
    · simp [removeStuff, owed] at parsed
    · have empty : [] = message := by simpa [removeStuff, owed] using parsed
      simp [← empty, canonicalFrom, owed, insertStuff]
  | cons first rest ih =>
    by_cases owed : run = 6
    · subst run
      cases first
      · have tailParsed : removeStuff rest 0 = some message := by
          simpa [removeStuff] using parsed
        have tailCanonical := ih message 0 (by decide) tailParsed
        simpa [canonicalFrom] using congrArg (List.cons false) tailCanonical
      · simp [removeStuff] at parsed
    · have stepped : (removeStuff rest (if first then run+1 else 0)).map (first :: ·) = some message := by
        simpa [removeStuff, owed] using parsed
      obtain ⟨tail, tailParsed, headEq⟩ := Option.map_eq_some_iff.mp stepped
      subst message
      cases first
      · have tailCanonical := ih tail 0 (by decide) tailParsed
        simpa [canonicalFrom, owed, insertStuff] using congrArg (List.cons false) tailCanonical
      · have nextBound : run+1 ≤ 6 := by omega
        have tailCanonical := ih tail (run+1) nextBound tailParsed
        by_cases inserts : run = 5
        · subst run
          simpa [canonicalFrom, insertStuff] using congrArg (List.cons true) tailCanonical
        · have notOwed : run+1 ≠ 6 := by omega
          simpa [canonicalFrom, owed, notOwed, inserts, insertStuff] using congrArg (List.cons true) tailCanonical
  done

theorem decode_only_canonical_wire (frame : PinFrame) (bits : List Bool)
    (parsed : removeStuff (readNRZI false frame.symbols) 0 = some bits) :
    frame.symbols = emitNRZI false (insertStuff bits 0) := by
  have enc := canonical_of_remove _ _ 0 (by decide) parsed
  have onWire := congrArg (emitNRZI false) enc
  simpa [canonicalFrom, emit_read_nrzi] using onWire.symm
  done

def DataReply (logical payload : List Bool) : Prop :=
  logical.take 16 = header 0x4B ∧ logical.length = 96 ∧
    (logical.drop 16).foldl usbCrcStep 0xFFFF#16 = 0xB001#16 ∧
    (logical.drop 16).take 64 = payload

theorem classify_data_iff (logical payload : List Bool) :
    classifyBits logical = .data payload ↔ DataReply logical payload := by
  by_cases nak : logical = header 0x5A
  · simp [classifyBits, nak, DataReply]
  by_cases stall : logical = header 0x1E
  · have different : header 0x1E ≠ header 0x5A := by decide +kernel
    simp [classifyBits, stall, different, DataReply]
  by_cases pid : logical.take 16 = header 0x4B
  · by_cases size : logical.length = 96
    · by_cases crc : (logical.drop 16).foldl usbCrcStep 0xFFFF#16 = 0xB001#16
      · simp [classifyBits, nak, stall, pid, size, crc, DataReply]
      · simp [classifyBits, nak, stall, pid, size, crc, DataReply]
    · simp [classifyBits, nak, stall, pid, size, DataReply]
  · simp [classifyBits, nak, stall, pid, DataReply]
  done

def dataFraming (frame : PinFrame) : Prop :=
  frame.endsInJ = true ∧ 31 ≤ frame.se0Clocks ∧ frame.se0Clocks ≤ 33

theorem decode_data_iff (frame : PinFrame) (payload : List Bool) :
    decodePinFrame (some frame) = .data payload ↔
      dataFraming frame ∧ ∃ logical,
        frame.symbols = emitNRZI false (insertStuff logical 0) ∧ DataReply logical payload := by
  constructor
  · intro accepted
    by_cases framing : dataFraming frame
    · have eqAtEop := framing
      unfold dataFraming at eqAtEop
      simp [decodePinFrame, eqAtEop.1, eqAtEop.2.1, eqAtEop.2.2] at accepted
      cases parsed : removeStuff (readNRZI false frame.symbols) 0 with
      | none => simp [parsed] at accepted
      | some logical =>
        have outcome : classifyBits logical = .data payload := by simpa [parsed] using accepted
        exact ⟨framing, logical, decode_only_canonical_wire _ _ parsed, (classify_data_iff _ _).mp outcome⟩
    · have fail : ¬ (frame.endsInJ = true ∧ 31 ≤ frame.se0Clocks ∧ frame.se0Clocks ≤ 33) := framing
      simp [decodePinFrame, fail] at accepted
  · rintro ⟨⟨ends, lo, hi⟩, logical, wire, data⟩
    simp [decodePinFrame, ends, lo, hi, wire, read_emit_nrzi, remove_insert_stuff,
      (classify_data_iff _ _).mpr data]
  done

def scheduledAck (edge : Nat) (result : Outcome) : Option Nat :=
  match result with
  | .data _ => some (edge + 46)
  | _ => none

theorem scheduled_ack_iff (edge : Nat) (reply : Option PinFrame) (time : Nat) :
    scheduledAck edge (decodePinFrame reply) = some time ↔
      time = edge + 46 ∧ ∃ frame payload, reply = some frame ∧
        dataFraming frame ∧ ∃ logical,
          frame.symbols = emitNRZI false (insertStuff logical 0) ∧ DataReply logical payload := by
  cases candidate : decodePinFrame reply with
  | data payload =>
    cases reply with
    | none => simp [decodePinFrame] at candidate
    | some frame =>
      have exactData := (decode_data_iff _ _).mp candidate
      constructor
      · intro outputAt
        exact ⟨(by simpa [scheduledAck, candidate] using outputAt.symm),
          frame, payload, rfl, exactData⟩
      · intro conditions
        simp [scheduledAck, conditions.1]
  | nak | stall | noReply | eop | stuff | header | length | crc =>
    constructor
    · simp [scheduledAck]
    · rintro ⟨_, frame, payload, bound, valid⟩
      have good := (decode_data_iff _ _).mpr valid
      rw [bound, good] at candidate
      cases candidate
  done

def packLSB : (bits : List Bool) → BitVec bits.length
  | [] => 0#0
  | bit :: rest => packLSB rest ++ BitVec.ofBool bit

theorem pack_lsb_nth (bits : List Bool) (i : Nat) (h : i < bits.length) :
    (packLSB bits).getLsbD i = bits[i] := by
  induction bits generalizing i with
  | nil => simp at h
  | cons bit tail ih =>
    cases i with
    | zero =>
      change (packLSB tail ++ BitVec.ofBool bit).getLsbD 0 = bit
      rw [BitVec.getLsbD_append]
      simp
    | succ i =>
      have before : i < tail.length := by simpa using h
      simpa [packLSB, BitVec.getLsbD_append, Nat.succ_sub] using ih i before
  done

theorem low_bits_pack16 (bits : List Bool) (h : bits.length = 16) :
    crcLowBits 16 ((packLSB bits).cast h) = bits := by
  apply List.ext_getElem
  · simp [crc_low_bits_length, h]
  · intro i hlo hhi
    simp [crc_low_bits_nth]
    exact pack_lsb_nth bits i hhi
  done

def canonicalDATA1 (payload : List Bool) : List Bool :=
  header 0x4B ++ (payload ++ crcLowBits 16 (~~~ (payload.foldl usbCrcStep 0xFFFF#16)))

theorem data_reply_exact (logical payload : List Bool) :
    DataReply logical payload ↔ payload.length = 64 ∧ logical = canonicalDATA1 payload := by
  constructor
  · rintro ⟨headCorrect, length, checksum, content⟩
    have payloadSize : payload.length = 64 := by simp [← content, length]
    let body := logical.drop 16
    let footer := body.drop 64
    have footerSize : footer.length = 16 := by simp [footer, body, length]
    let trailer := (packLSB footer).cast footerSize
    have trailerWire : crcLowBits 16 trailer = footer := low_bits_pack16 footer footerSize
    have receiveParts : payload ++ footer = body := by
      exact (congrArg (· ++ footer) content.symm).trans (List.take_append_drop 64 body)
    have crcEnd : (crcLowBits 16 trailer).foldl usbCrcStep (payload.foldl usbCrcStep 0xFFFF#16) = 0xB001#16 := by
      rw [trailerWire, ← List.foldl_append, receiveParts]
      exact checksum
    have trailerCorrect := (crc_residue_iff_correct_trailer _ _).mp crcEnd
    have allParts : header 0x4B ++ body = logical := by
      exact (congrArg (· ++ body) headCorrect.symm).trans (List.take_append_drop 16 logical)
    refine ⟨payloadSize, ?_⟩
    unfold canonicalDATA1
    rw [← trailerCorrect, trailerWire, receiveParts, allParts]
  · rintro ⟨size, logicalIs⟩
    rw [← classify_data_iff, logicalIs]
    simp [canonicalDATA1, observe_data_trailer, size]
  done

open Pinwheel.Program.Streaming

def fullChunk (bits : List Bool) : Chunk := ⟨Packing.rxWord bits, 31⟩

def commitDecoded (outcome : Outcome) : Queue 1 :=
  match outcome with
  | .data bits =>
    ((Queue.empty 1).tick (some (fullChunk (bits.take 32))) false).tick
      (some (fullChunk (bits.drop 32))) false
  | _ => Queue.empty 1

theorem accepted_two_word_contents (payload : List Bool) :
    (commitDecoded (.data payload)).Contents
      [fullChunk (payload.take 32), fullChunk (payload.drop 32)] := by
  let first := fullChunk (payload.take 32)
  let second := fullChunk (payload.drop 32)
  let filledOne := (Queue.empty 1).tick (some first) false
  have h₁ : filledOne.Contents [first] := by
    simpa using (Queue.empty_contents 1).push _ [] first (by decide)
  have one : filledOne.count.val = 1 := h₁.length.symm
  have again : filledOne.count.val < queueDepth 1 := by
    rw [one]
    decide
  exact h₁.push _ [first] second again
  done

theorem chunk_roundtrip (bits : List Bool) (size : bits.length = 32) :
    (fullChunk bits).rxBits = bits := by
  have valid : (fullChunk bits).validBits = 32 := rfl
  rw [Chunk.rxBits, valid, ← size]
  exact Packing.rxWord_roundtrip bits (by omega)
  done

theorem accepted_payload_drains_in_order (payload : List Bool) (length : payload.length = 64) :
    let q := commitDecoded (.data payload)
    let halfway := q.tick none true
    let empty := halfway.tick none true
    q.peek.rxBits ++ halfway.peek.rxBits = payload ∧ empty.count.val = 0 := by
  let q := commitDecoded (.data payload)
  let first := fullChunk (payload.take 32)
  let second := fullChunk (payload.drop 32)
  have full : q.Contents [first, second] := accepted_two_word_contents payload
  have firstRoom : 0 < q.count.val := by
    rw [← full.length]
    simp
  let halfway := q.tick none true
  have half : halfway.Contents [second] := full.pop _ _ firstRoom
  have secondRoom : 0 < halfway.count.val := by
    rw [← half.length]
    simp
  have drained : (halfway.tick none true).Contents [] := half.pop _ _ secondRoom
  refine ⟨?_, drained.length.symm⟩
  have firstPeek : q.peek = first := full.peek _ _ (by simp)
  have secondPeek : halfway.peek = second := half.peek _ _ (by simp)
  change q.peek.rxBits ++ halfway.peek.rxBits = payload
  rw [firstPeek, secondPeek]
  change (fullChunk (payload.take 32)).rxBits ++ (fullChunk (payload.drop 32)).rxBits = payload
  rw [chunk_roundtrip _ (by simp [length]), chunk_roundtrip _ (by simp [length])]
  exact List.take_append_drop 32 payload
  done

theorem reject_publishes_no_words (result : Outcome)
    (noData : ¬ ∃ bits, result = .data bits) :
    (commitDecoded result).count.val = 0 := by
  cases result <;> simp_all [commitDecoded, Queue.empty]
  done

theorem data_pins_exact (frame : PinFrame) (payload : List Bool) :
    decodePinFrame (some frame) = .data payload ↔
      dataFraming frame ∧ payload.length = 64 ∧
        frame.symbols = emitNRZI false (insertStuff (canonicalDATA1 payload) 0) := by
  rw [decode_data_iff]
  constructor
  · rintro ⟨framing, bits, levels, checked⟩
    obtain ⟨size, legal⟩ := (data_reply_exact _ _).mp checked
    exact ⟨framing, size, levels.trans (congrArg (fun b => emitNRZI false (insertStuff b 0)) legal)⟩
  · rintro ⟨framing, size, levels⟩
    exact ⟨framing, canonicalDATA1 payload, levels, (data_reply_exact _ _).mpr ⟨size, rfl⟩⟩
  done

theorem canonical_packet_publishes_and_acks (payload : List Bool) (length : payload.length = 64)
    (eopClocks eopEdge : Nat) (framing : 31 ≤ eopClocks ∧ eopClocks ≤ 33) :
    let decision := decodePinFrame (some (wireFrame (canonicalDATA1 payload) eopClocks))
    let queue := commitDecoded decision
    scheduledAck eopEdge decision = some (eopEdge + 46) ∧
      queue.peek.rxBits ++ (queue.tick none true).peek.rxBits = payload ∧
      ((queue.tick none true).tick none true).count.val = 0 := by
  have accepted : decodePinFrame (some (wireFrame (canonicalDATA1 payload) eopClocks)) = .data payload :=
    (data_pins_exact _ _).mpr ⟨⟨rfl, framing⟩, length, rfl⟩
  dsimp only
  rw [accepted]
  exact ⟨rfl, accepted_payload_drains_in_order payload length⟩
  done

theorem nonmatching_crc_leaves_queue_empty (payload : List Bool) (length : payload.length = 64)
    (trailer : BitVec 16) (bad : trailer ≠ ~~~(payload.foldl usbCrcStep 0xFFFF#16))
    (eopClocks eopEdge : Nat) (framing : 31 ≤ eopClocks ∧ eopClocks ≤ 33) :
    let decision := decodePinFrame (some
      (wireFrame (header 0x4B ++ (payload ++ crcLowBits 16 trailer)) eopClocks))
    decision = .crc ∧ scheduledAck eopEdge decision = none ∧ (commitDecoded decision).count.val = 0 := by
  dsimp only
  rw [decode_canonical_symbols _ _ framing, observe_data_trailer payload length trailer, if_neg bad]
  exact ⟨rfl, rfl, rfl⟩
  done

structure LogicalRegs where
  consumed : Nat := 0
  headerWord : BitVec 16 := 0
  payloadFirst : BitVec 32 := 0
  payloadSecond : BitVec 32 := 0
  checksum : BitVec 16 := 0xFFFF#16
  deriving Repr

def pushBit (word : BitVec w) (bit : Bool) : BitVec w :=
  (word <<< 1) ||| BitVec.ofNat w (if bit then 1 else 0)

def ingestLogical (state : LogicalRegs) (bit : Bool) : LogicalRegs :=
  { consumed := min 97 (state.consumed + 1)
    headerWord := if state.consumed < 16 then pushBit state.headerWord bit else state.headerWord
    payloadFirst := if 16 ≤ state.consumed ∧ state.consumed < 48 then
      pushBit state.payloadFirst bit else state.payloadFirst
    payloadSecond := if 48 ≤ state.consumed ∧ state.consumed < 80 then
      pushBit state.payloadSecond bit else state.payloadSecond
    checksum := if 16 ≤ state.consumed ∧ state.consumed < 96 then
      usbCrcStep state.checksum bit else state.checksum }

def wordFor (width : Nat) (bits : List Bool) : BitVec width :=
  (BitVec.ofBoolListBE bits).setWidth width

theorem wordFor_eq_packing (bits : List Bool) : wordFor 32 bits = Packing.rxWord bits := rfl

theorem wordFor_append (width : Nat) (bits : List Bool) (bit : Bool) :
    wordFor width (bits ++ [bit]) = pushBit (wordFor width bits) bit := by
  apply BitVec.eq_of_getLsbD_eq
  intro index within
  cases index with
  | zero => cases bit <;> simp [wordFor, pushBit, List.getD_eq_getElem?_getD, within]
  | succ index =>
    simp [wordFor, pushBit, within, List.getD_eq_getElem?_getD]
    by_cases inside : index < bits.length
    · rw [List.getElem?_append_left (by omega)]
      have address : bits.length - (index + 1) = bits.length - 1 - index := by omega
      cases bit <;> simp [inside, address, BitVec.getElem_eq_testBit_toNat,
        Nat.testBit_one_eq_true_iff_self_eq_zero]
    · have high : Nat.testBit 1 (index + 1) = false := by
        apply Bool.eq_false_iff.mpr
        intro truth
        exact Nat.succ_ne_zero index (Nat.testBit_one_eq_true_iff_self_eq_zero.mp truth)
      cases bit <;> simp [inside, high, BitVec.getElem_eq_testBit_toNat]
  done

inductive WordField where | head | first | second
  deriving DecidableEq

def fieldWidth : WordField → Nat
  | .head => 16
  | _ => 32

def fieldStart : WordField → Nat
  | .head => 0
  | .first => 16
  | .second => 48

def fieldLimit (field : WordField) : Nat := fieldStart field + fieldWidth field

def LogicalRegs.get (state : LogicalRegs) (field : WordField) : BitVec (fieldWidth field) :=
  match field with
  | .head => state.headerWord
  | .first => state.payloadFirst
  | .second => state.payloadSecond

theorem logical_get_step (s : LogicalRegs) (b : Bool) (field : WordField) :
    (ingestLogical s b).get field =
      if fieldStart field ≤ s.consumed ∧ s.consumed < fieldLimit field then
        pushBit (s.get field) b else s.get field := by
  cases field <;> simp [ingestLogical, LogicalRegs.get, fieldWidth, fieldStart, fieldLimit]
  all_goals rfl
  done

def segment (bits : List Bool) (start width : Nat) : List Bool :=
  (bits.drop start).take width

theorem segment_append (bits : List Bool) (next : Bool) (start width : Nat) :
    segment (bits ++ [next]) start width =
      if start ≤ bits.length ∧ bits.length < start + width then
        segment bits start width ++ [next] else segment bits start width := by
  by_cases afterStart : start ≤ bits.length
  · have gap : start - bits.length = 0 := by omega
    by_cases beforeEnd : bits.length < start + width
    · have takeNext : ([next] : List Bool).length ≤ width - (bits.length - start) := by
        simp only [List.length_cons, List.length_nil, Nat.zero_add]
        omega
      simp [segment, List.drop_append, gap, List.take_append, afterStart, beforeEnd,
        List.take_of_length_le takeNext]
    · have filled : width - (bits.length - start) = 0 := by omega
      simp [segment, List.drop_append, gap, List.take_append, beforeEnd, filled]
  · have unstarted : ([next] : List Bool).length ≤ start - bits.length := by
      simp only [List.length_cons, List.length_nil, Nat.zero_add]
      omega
    simp [segment, List.drop_append, afterStart, List.drop_of_length_le unstarted]
  done

theorem finite_field_pred (field : WordField) (count : Nat) :
    (fieldStart field ≤ min 97 count ∧ min 97 count < fieldLimit field) ↔
      (fieldStart field ≤ count ∧ count < fieldStart field + fieldWidth field) := by
  cases field <;> simp only [fieldStart, fieldWidth, fieldLimit] <;> omega
  done

theorem finite_crc_pred (count : Nat) :
    (16 ≤ min 97 count ∧ min 97 count < 96) ↔ (16 ≤ count ∧ count < 16+80) := by
  omega
  done

theorem snoc_ind (P : List Bool → Prop) (nil : P []) (snoc : ∀ bs b, P bs → P (bs ++ [b]))
    (bits : List Bool) : P bits := by
  have reversed (xs : List Bool) : P xs.reverse := by
    induction xs with
    | nil => exact nil
    | cons x tail ih =>
      rw [List.reverse_cons]
      exact snoc _ _ ih
  simpa using reversed bits.reverse
  done

structure LogicalAgreement (state : LogicalRegs) (received : List Bool) : Prop where
  count : state.consumed = min 97 received.length
  fields : ∀ field,
    state.get field = wordFor (fieldWidth field) (segment received (fieldStart field) (fieldWidth field))
  crc : state.checksum = (segment received 16 80).foldl usbCrcStep 0xFFFF#16

theorem logical_agreement_step (s : LogicalRegs) (bits : List Bool) (b : Bool)
    (agree : LogicalAgreement s bits) :
    LogicalAgreement (ingestLogical s b) (bits ++ [b]) := by
  constructor
  · simp only [ingestLogical, agree.count, List.length_append, List.length_cons, List.length_nil, Nat.zero_add]
    omega
  · intro field
    rw [logical_get_step, agree.count, segment_append]
    by_cases inWindow : fieldStart field ≤ bits.length ∧
        bits.length < fieldStart field + fieldWidth field
    · rw [if_pos ((finite_field_pred field _).mpr inWindow), if_pos inWindow, agree.fields, wordFor_append]
    · rw [if_neg (fun h => inWindow ((finite_field_pred field _).mp h)), if_neg inWindow, agree.fields]
  · change (if 16 ≤ s.consumed ∧ s.consumed < 96 then usbCrcStep s.checksum b else s.checksum) =
      (segment (bits ++ [b]) 16 80).foldl usbCrcStep 0xFFFF#16
    rw [agree.count, segment_append]
    by_cases inWindow : 16 ≤ bits.length ∧ bits.length < 16+80
    · rw [if_pos ((finite_crc_pred _).mpr inWindow), if_pos inWindow, agree.crc, List.foldl_append]
      rfl
    · rw [if_neg (fun h => inWindow ((finite_crc_pred _).mp h)), if_neg inWindow, agree.crc]
  done

theorem logical_fold_agrees (bits : List Bool) :
    LogicalAgreement (bits.foldl ingestLogical {}) bits := by
  apply snoc_ind (fun xs => LogicalAgreement (xs.foldl ingestLogical {}) xs)
  · constructor
    · rfl
    · intro field
      cases field <;> rfl
    · rfl
  · intro xs bit ih
    simpa only [List.foldl_append, List.foldl_cons, List.foldl_nil] using
      logical_agreement_step (xs.foldl ingestLogical {}) xs bit ih
  done

structure SymbolRegs where
  last : Bool := false
  ones : Nat := 0
  logical : LogicalRegs := {}
  deriving Repr

def ingestSymbol (s : SymbolRegs) (level : Bool) : Option SymbolRegs :=
  let bit := level == s.last
  if s.ones = 6 then
    if bit then none else some { s with last := level, ones := 0 }
  else
    some { last := level, ones := if bit then s.ones + 1 else 0,
           logical := ingestLogical s.logical bit }

def finishSymbols (state : SymbolRegs) : Option LogicalRegs :=
  if state.ones = 6 then none else some state.logical

def replaySymbols (s : SymbolRegs) : List Bool → Option LogicalRegs
  | [] => finishSymbols s
  | level :: more => (ingestSymbol s level).bind (fun next => replaySymbols next more)

theorem replay_symbols_refine (samples : List Bool) (s : SymbolRegs) :
    replaySymbols s samples =
      (removeStuff (readNRZI s.last samples) s.ones).map (fun bits => bits.foldl ingestLogical s.logical) := by
  induction samples generalizing s with
  | nil =>
    simp [replaySymbols, finishSymbols, readNRZI, removeStuff]
    split <;> rfl
  | cons level more ih =>
    by_cases stuffed : s.ones = 6
    · by_cases unchanged : (level == s.last) = true
      · simp [replaySymbols, ingestSymbol, readNRZI, removeStuff, stuffed, unchanged]
      · have toggle : (level == s.last) = false := Bool.eq_false_iff.mpr unchanged
        simp [replaySymbols, ingestSymbol, readNRZI, removeStuff, stuffed, toggle, ih]
    · simp [replaySymbols, ingestSymbol, readNRZI, removeStuff, stuffed, ih,
        Option.map_map, Function.comp_def]
  done

theorem canonical_registers_agree (logical : List Bool) :
    replaySymbols {} (emitNRZI false (insertStuff logical 0)) =
      some (logical.foldl ingestLogical {}) := by
  rw [replay_symbols_refine]
  simp [read_emit_nrzi, remove_insert_stuff]
  done

def decodeWord (word : BitVec width) (numBits : Nat) : List Bool :=
  List.ofFn (fun i : Fin numBits => word.getLsbD (numBits - 1 - i.val))

theorem decode_wordFor (bits : List Bool) (width : Nat) (size : bits.length ≤ width) :
    decodeWord (wordFor width bits) bits.length = bits := by
  apply List.ext_getElem?
  intro index
  by_cases inside : index < bits.length
  · have address : bits.length - 1 - index < bits.length := by omega
    have reflect : bits.length - 1 - (bits.length - 1 - index) = index := by omega
    simp [decodeWord, inside, wordFor, Nat.lt_of_lt_of_le address size, address, reflect]
  · simp [decodeWord, inside]
  done

theorem header_word_iff (bits : List Bool) (size : bits.length = 16) :
    wordFor 16 bits = wordFor 16 (header 0x4B) ↔ bits = header 0x4B := by
  constructor
  · intro same
    have left := decode_wordFor bits 16 (by omega)
    have right := decode_wordFor (header 0x4B) 16 (by simp)
    rw [size, same] at left
    exact left.symm.trans (by simpa only [header_length] using right)
  · rintro rfl
    rfl
  done

def acceptRegisters (state : LogicalRegs) : Prop :=
    state.consumed = 96 ∧
    state.headerWord = wordFor 16 (header 0x4B) ∧
    state.checksum = 0xB001#16

def readRegisterPayload (state : LogicalRegs) : List Bool :=
  decodeWord state.payloadFirst 32 ++ decodeWord state.payloadSecond 32

theorem read_payload_regs (s : LogicalRegs) (bits : List Bool)
    (agree : LogicalAgreement s bits) (size : bits.length = 96) :
    readRegisterPayload s = (bits.drop 16).take 64 := by
  have firstLen : (segment bits 16 32).length = 32 := by simp [segment, size]
  have secondLen : (segment bits 48 32).length = 32 := by simp [segment, size]
  have firstPart : s.payloadFirst = wordFor 32 (segment bits 16 32) := agree.fields .first
  have secondPart : s.payloadSecond = wordFor 32 (segment bits 48 32) := agree.fields .second
  have firstDecoded := decode_wordFor (segment bits 16 32) 32 (by rw [firstLen]; decide)
  have secondDecoded := decode_wordFor (segment bits 48 32) 32 (by rw [secondLen]; decide)
  rw [firstLen] at firstDecoded
  rw [secondLen] at secondDecoded
  rw [readRegisterPayload, firstPart, secondPart, firstDecoded, secondDecoded]
  have split := List.take_append_drop 32 ((bits.drop 16).take 64)
  simpa [segment, List.take_take, List.drop_take] using split
  done

theorem reg_accept_matches_data (s : LogicalRegs) (bits payload : List Bool)
    (agree : LogicalAgreement s bits) :
    (acceptRegisters s ∧ readRegisterPayload s = payload) ↔ DataReply bits payload := by
  constructor
  · rintro ⟨⟨count, headerOk, crcOk⟩, words⟩
    have size : bits.length = 96 := by
      rw [agree.count] at count
      omega
    have headWord : s.headerWord = wordFor 16 (bits.take 16) := agree.fields .head
    have correctHeader := (header_word_iff (bits.take 16) (by simp [size])).mp
      (headWord.symm.trans headerOk)
    have crcBody : s.checksum = (bits.drop 16).foldl usbCrcStep 0xFFFF#16 := by
      have bodyLen : (bits.drop 16).length ≤ 80 := by simp [size]
      simpa [segment, List.take_of_length_le bodyLen] using agree.crc
    exact ⟨correctHeader, size, crcBody.symm.trans crcOk,
      (read_payload_regs s bits agree size).symm.trans words⟩
  · rintro ⟨head, length, goodCRC, content⟩
    have headWord : s.headerWord = wordFor 16 (bits.take 16) := agree.fields .head
    have bodyLen : (bits.drop 16).length ≤ 80 := by simp [length]
    have residue : s.checksum = 0xB001#16 := by
      simpa [segment, List.take_of_length_le bodyLen, goodCRC] using agree.crc
    exact ⟨⟨by simp [agree.count, length], headWord.trans (congrArg (wordFor 16) head), residue⟩,
      (read_payload_regs s bits agree length).trans content⟩
  done

def acceptFlag (s : LogicalRegs) : Bool :=
  (s.consumed == 96) && (s.headerWord == wordFor 16 (header 0x4B)) &&
      (s.checksum == 0xB001#16)

theorem acceptFlag_iff (s : LogicalRegs) : acceptFlag s = true ↔ acceptRegisters s := by
  simp [acceptFlag, acceptRegisters, _root_.and_assoc]
  done

def receiveDataByRegisters (frame : PinFrame) : Option (List Bool) :=
  if frame.endsInJ && decide (31 ≤ frame.se0Clocks ∧ frame.se0Clocks ≤ 33) then
    (replaySymbols {} frame.symbols).bind
      (fun s => if acceptFlag s then some (readRegisterPayload s) else none)
  else none

theorem bounded_data_receiver_refines (frame : PinFrame) (payload : List Bool) :
    receiveDataByRegisters frame = some payload ↔ decodePinFrame (some frame) = .data payload := by
  by_cases eop : (frame.endsInJ && decide (31 ≤ frame.se0Clocks ∧ frame.se0Clocks ≤ 33)) = true
  · simp only [receiveDataByRegisters, decodePinFrame, eop, if_true, replay_symbols_refine]
    change ((removeStuff (readNRZI false frame.symbols) 0).map
        (fun bits => bits.foldl ingestLogical {})).bind _ = some payload ↔
      (match removeStuff (readNRZI false frame.symbols) 0 with
      | none => Outcome.stuff
      | some bits => classifyBits bits) = .data payload
    cases decoded : removeStuff (readNRZI false frame.symbols) 0 with
    | none => simp
    | some bits =>
      let state := bits.foldl ingestLogical {}
      have safe := (reg_accept_matches_data state bits payload (logical_fold_agrees bits))
      simp only [Option.map_some, Option.bind, classify_data_iff]
      change (if acceptFlag state then some (readRegisterPayload state) else none) =
        some payload ↔ DataReply bits payload
      by_cases accept : acceptFlag state = true
      · have ack := (acceptFlag_iff state).mp accept
        simp [accept, ← safe, ack]
      · have reject : ¬ acceptRegisters state := fun h => accept ((acceptFlag_iff state).mpr h)
        simp [accept, ← safe, reject]
  · simp only [receiveDataByRegisters, decodePinFrame, eop]
    simp
  done

end Pinwheel.USBPacketFeasibility

namespace Pinwheel.USBReadFeasibility

theorem small_index_cases (j : Nat) (bound : j < 7) :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 := by
  omega
  done

theorem within_symbol_with_margin
    (den period offset : Int) (_positive : 0 < den)
    (fast : 394 * den ≤ 25 * period) (slow : 25 * period ≤ 406 * den)
    (early : -den < offset) (late : offset ≤ 0)
    (j : Nat) (within_run : j < 7) :
    offset + (j : Int) * period + 6 * den < (8 + 16 * (j : Int)) * den ∧
      (8 + 16 * (j : Int)) * den + 5 * den < offset + ((j : Int) + 1) * period := by
  rcases small_index_cases j within_run with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals omega
  done

theorem transition_offsets
    (den period offset : Int) (_positive : 0 < den)
    (fast : 394 * den ≤ 25 * period) (slow : 25 * period ≤ 406 * den)
    (early : -den < offset) (late : offset ≤ 0)
    (j : Nat) (within_run : j < 7) :
    (16 * ((j : Int) + 1) - 3) * den < offset + ((j : Int) + 1) * period ∧
      offset + ((j : Int) + 1) * period ≤ (16 * ((j : Int) + 1) + 2) * den := by
  rcases small_index_cases j within_run with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals omega
  done

theorem rounded_transition_preempts_old_sample
    (den period offset arrival : Int) (positive : 0 < den)
    (fast : 394 * den ≤ 25 * period) (slow : 25 * period ≤ 406 * den)
    (early : -den < offset) (late : offset ≤ 0)
    (j : Nat) (within_run : j < 7)
    (quantized : (arrival - 1) * den < offset + ((j : Int) + 1) * period) :
    arrival + 6 ≤ 8 + 16 * ((j : Int) + 1) := by
  have latest := (transition_offsets den period offset positive fast slow early late j within_run).2
  by_cases arrives : arrival + 6 ≤ 8 + 16 * ((j : Int) + 1)
  · exact arrives
  · have exceeds : 16 * ((j : Int) + 1) + 2 ≤ arrival - 1 := by omega
    have product : (16 * ((j : Int) + 1) + 2) * den ≤ (arrival - 1) * den :=
      Int.mul_le_mul_of_nonneg_right exceeds (Int.le_of_lt positive)
    exact False.elim (Int.not_lt_of_ge (Int.le_trans latest product) quantized)
  done

theorem quantized_window (den exact detected low high : Int) (positive : 0 < den)
    (qLow : (detected - 1) * den < exact) (qHigh : exact ≤ detected * den)
    (widthLow : (low - 1) * den < exact) (widthHigh : exact ≤ high * den) :
    low ≤ detected ∧ detected ≤ high := by
  constructor
  · by_cases h : low ≤ detected
    · exact h
    · have outside : detected ≤ low - 1 := by omega
      have product : detected * den ≤ (low - 1) * den :=
        Int.mul_le_mul_of_nonneg_right outside (Int.le_of_lt positive)
      exact False.elim (Int.not_lt_of_ge (Int.le_trans qHigh product) widthLow)
  · by_cases h : detected ≤ high
    · exact h
    · have outside : high ≤ detected - 1 := by omega
      have product : high * den ≤ (detected - 1) * den :=
        Int.mul_le_mul_of_nonneg_right outside (Int.le_of_lt positive)
      exact False.elim (Int.not_lt_of_ge (Int.le_trans widthHigh product) qLow)
  done

theorem se0_pulse_widths (den period offset detected : Int) (positive : 0 < den)
    (fast : 394 * den ≤ 25 * period) (slow : 25 * period ≤ 406 * den)
    (early : -den < offset) (late : offset ≤ 0)
    (bits : Int) (span : bits = 1 ∨ bits = 2 ∨ bits = 3)
    (qLow : (detected - 1) * den < offset + bits * period)
    (qHigh : offset + bits * period ≤ detected * den) :
    16 * bits - 1 ≤ detected ∧ detected ≤ 16 * bits + 1 := by
  apply quantized_window den (offset + bits * period) detected _ _ positive qLow qHigh
  all_goals rcases span with rfl | rfl | rfl <;> omega
  done

theorem ack_after_validated_j (den offset : Int) (_positive : 0 < den)
    (early : -den < offset) (late : offset ≤ 0) :
    48 * den ≤ (2 + 46) * den - offset ∧ (2 + 46) * den - offset < 49 * den := by
  omega
  done

end Pinwheel.USBReadFeasibility
namespace Pinwheel.USBClockFeasibility

structure Sampler where
  level : Bool := false
  down : Nat := 0
  deriving DecidableEq, Repr

def tick (s : Sampler) (wire : Bool) : Sampler × List Bool :=
  if wire ≠ s.level then (⟨wire, 7⟩, [])
  else if s.down = 0 then (⟨wire, 15⟩, [wire])
  else (⟨wire, s.down - 1⟩, [])

def sampleTrace (s : Sampler) (trace : List Bool) : Sampler × List Bool :=
  match trace with
  | [] => (s, [])
  | wire :: more =>
    let next := tick s wire
    let tail := sampleTrace next.1 more
    (tail.1, next.2 ++ tail.2)

theorem sample_append (s : Sampler) (prefixTrace suffix : List Bool) :
    sampleTrace s (prefixTrace ++ suffix) =
      let first := sampleTrace s prefixTrace
      let second := sampleTrace first.1 suffix
      (second.1, first.2 ++ second.2) := by
  induction prefixTrace generalizing s with
  | nil => simp [sampleTrace]
  | cons w more ih =>
    simp [sampleTrace, ih, List.append_assoc]
  done

theorem stable_count (w : Bool) (cycles wait : Nat) (waitBound : wait ≤ 15) :
    (sampleTrace ⟨w, wait⟩ (List.replicate cycles w)).1.level = w ∧
    (sampleTrace ⟨w, wait⟩ (List.replicate cycles w)).2 =
      List.replicate ((cycles + 15 - wait) / 16) w := by
  induction cycles generalizing wait with
  | zero =>
    have slots : (0 + 15 - wait) / 16 = 0 := by omega
    simp [sampleTrace, slots]
  | succ cycles ih =>
    rw [List.replicate_succ]
    by_cases fires : wait = 0
    · subst wait
      have count : (cycles + 1 + 15) / 16 = cycles / 16 + 1 := by omega
      have next := ih 15 (by decide)
      simp [sampleTrace, tick, next.1, next.2, count, List.replicate_succ]
    · have decBound : wait - 1 ≤ 15 := by omega
      have count : (cycles + 1 + 15 - wait) / 16 = (cycles + 15 - (wait-1)) / 16 := by omega
      have next := ih (wait-1) decBound
      simp [sampleTrace, tick, fires, count, next.1, next.2]
  done

structure Run where
  wire : Bool
  clocks : Nat
  symbols : Nat
  deriving Repr

def Run.supported (run : Run) : Prop :=
  0 < run.symbols ∧ run.symbols ≤ 7 ∧
  16 * run.symbols ≤ run.clocks + 2 ∧ run.clocks ≤ 16 * run.symbols + 2

theorem exactly_one_per_symbol (s : Sampler) (run : Run)
    (edge : run.wire ≠ s.level) (width : run.supported) :
    (sampleTrace s (List.replicate run.clocks run.wire)).1.level = run.wire ∧
    (sampleTrace s (List.replicate run.clocks run.wire)).2 =
      List.replicate run.symbols run.wire := by
  obtain ⟨positive, _, early, late⟩ := width
  cases clocks : run.clocks with
  | zero => omega
  | succ remaining =>
    have count : (remaining + 8) / 16 = run.symbols := by omega
    have next := stable_count run.wire remaining 7 (by decide)
    simp [List.replicate_succ, sampleTrace, tick, edge, next.1, next.2, count]
  done

def validSequence (previous : Bool) : List Run → Prop
  | [] => True
  | head :: tail => head.wire ≠ previous ∧ head.supported ∧ validSequence head.wire tail

def clockTape (runs : List Run) : List Bool :=
  runs.flatMap (fun run => List.replicate run.clocks run.wire)

def intendedWireSymbols (runs : List Run) : List Bool :=
  runs.flatMap (fun run => List.replicate run.symbols run.wire)

theorem sample_runs_exact (runs : List Run) (s : Sampler) (legal : validSequence s.level runs) :
    (sampleTrace s (clockTape runs)).2 = intendedWireSymbols runs := by
  induction runs generalizing s with
  | nil => rfl
  | cons head tail ih =>
    obtain ⟨edge, width, rest⟩ := legal
    let next := sampleTrace s (List.replicate head.clocks head.wire)
    have result := exactly_one_per_symbol s head edge width
    have goodRest : validSequence next.1.level tail := by
      change validSequence (sampleTrace s (List.replicate head.clocks head.wire)).1.level tail
      rw [result.1]
      exact rest
    have tailEq := ih next.1 goodRest
    simp only [clockTape, intendedWireSymbols, List.flatMap_cons, sample_append]
    change next.2 ++ (sampleTrace next.1 (clockTape tail)).2 =
      List.replicate head.symbols head.wire ++ intendedWireSymbols tail
    rw [show next.2 = _ from result.2, tailEq]
  done

theorem quantized_run_supported (run : Run) (den period offset : Int)
    (positive : 0 < den) (fast : 394 * den ≤ 25 * period) (slow : 25 * period ≤ 406 * den)
    (early : -den < offset) (late : offset ≤ 0)
    (runBits : 0 < run.symbols ∧ run.symbols ≤ 7)
    (qLow : ((run.clocks : Int)-1)*den < offset + (run.symbols : Int)*period)
    (qHigh : offset + (run.symbols : Int)*period ≤ (run.clocks : Int)*den) :
    run.supported := by
  have residue := Pinwheel.USBReadFeasibility.transition_offsets den period offset positive fast slow
    early late (run.symbols - 1) (by omega)
  have castLength : ((run.symbols - 1 : Nat) : Int) + 1 = (run.symbols : Int) := by omega
  rw [castLength] at residue
  have bounds := Pinwheel.USBReadFeasibility.quantized_window den
    (offset + (run.symbols : Int) * period) (run.clocks : Int)
    (16 * (run.symbols : Int) - 2) (16 * (run.symbols : Int) + 2) positive qLow qHigh
    (by simpa [Int.sub_sub] using residue.1) residue.2
  exact ⟨runBits.1, runBits.2, by omega, by omega⟩
  done

structure PeerRate where
  den : Int
  period : Int
  positive : 0 < den
  fast : 394 * den ≤ 25 * period
  slow : 25 * period ≤ 406 * den

def measuredAtRate (rate : PeerRate) (run : Run) : Prop :=
  (0 < run.symbols ∧ run.symbols ≤ 7) ∧
  ∃ offset : Int, -rate.den < offset ∧ offset ≤ 0 ∧
    ((run.clocks : Int) - 1)*rate.den < offset + (run.symbols : Int)*rate.period ∧
    offset + (run.symbols : Int)*rate.period ≤ (run.clocks : Int)*rate.den

def rateTrace (rate : PeerRate) (previous : Bool) : List Run → Prop
  | [] => True
  | run :: rest => run.wire ≠ previous ∧ measuredAtRate rate run ∧ rateTrace rate run.wire rest

theorem trace_of_rate (rate : PeerRate) (previous : Bool) (runs : List Run)
    (legal : rateTrace rate previous runs) : validSequence previous runs := by
  induction runs generalizing previous with
  | nil => exact True.intro
  | cons run rest ih =>
    rcases legal with ⟨changeLevel, ⟨bits, off, early, late, lo, hi⟩, tail⟩
    exact ⟨changeLevel, quantized_run_supported run rate.den rate.period off rate.positive
      rate.fast rate.slow early late bits lo hi, ih _ tail⟩
  done

theorem end_marker_quantized (rate : PeerRate) (markerClocks : Nat) (off : Int)
    (early : -rate.den < off) (late : off ≤ 0)
    (lo : ((markerClocks : Int) - 1)*rate.den < off + 2*rate.period)
    (hi : off + 2*rate.period ≤ (markerClocks : Int)*rate.den) :
    31 ≤ markerClocks ∧ markerClocks ≤ 33 := by
  have span := Pinwheel.USBReadFeasibility.se0_pulse_widths rate.den rate.period off (markerClocks : Int)
    rate.positive rate.fast rate.slow early late 2 (Or.inr (Or.inl rfl)) lo hi
  omega
  done

end Pinwheel.USBClockFeasibility

namespace Pinwheel.USBTimedFeasibility
open Pinwheel.USBPacketFeasibility Pinwheel.USBClockFeasibility
open Pinwheel.Program.Streaming

def clockedFrame (runs : List Run) (markerClocks : Nat) (endsInJ : Bool) : PinFrame :=
  ⟨(sampleTrace {} (clockTape runs)).2, markerClocks, endsInJ⟩

theorem clocked_payload_exact (rate : PeerRate) (runs : List Run)
    (timing : rateTrace rate false runs) (markerClocks : Nat)
    (endsInJ : Bool) (payload : List Bool) :
    receiveDataByRegisters (clockedFrame runs markerClocks endsInJ) = some payload ↔
      endsInJ = true ∧ (31 ≤ markerClocks ∧ markerClocks ≤ 33) ∧
        payload.length = 64 ∧
        intendedWireSymbols runs = emitNRZI false (insertStuff (canonicalDATA1 payload) 0) := by
  rw [bounded_data_receiver_refines, data_pins_exact]
  have sampled := sample_runs_exact runs {} (trace_of_rate rate false runs timing)
  simp [dataFraming, clockedFrame, sampled, _root_.and_assoc]
  done

theorem ideal_data_recovered (rate : PeerRate) (runs : List Run)
    (timing : rateTrace rate false runs) (payload : List Bool) (size : payload.length = 64)
    (matchesPacket : intendedWireSymbols runs = emitNRZI false (insertStuff (canonicalDATA1 payload) 0))
    (markerClocks rawJEdge peerRelease : Nat) (markerOffset : Int)
    (early : -rate.den < markerOffset) (late : markerOffset ≤ 0)
    (lo : ((markerClocks : Int) - 1)*rate.den < markerOffset + 2*rate.period)
    (hi : markerOffset + 2*rate.period ≤ (markerClocks : Int)*rate.den)
    (release : peerRelease ≤ rawJEdge + 17) :
    let frame := clockedFrame runs markerClocks true
    let data := receiveDataByRegisters frame
    let verdict := decodePinFrame (some frame)
    let queue := commitDecoded verdict
    data = some payload ∧ scheduledAck (rawJEdge + 2) verdict = some (rawJEdge + 48) ∧
      peerRelease < rawJEdge + 48 ∧
      queue.peek.rxBits ++ (queue.tick none true).peek.rxBits = payload ∧
      ((queue.tick none true).tick none true).count.val = 0 := by
  let frame := clockedFrame runs markerClocks true
  have marker := end_marker_quantized rate markerClocks markerOffset early late lo hi
  have accepted : receiveDataByRegisters frame = some payload :=
    (clocked_payload_exact rate runs timing markerClocks true payload).mpr
      ⟨rfl, marker, size, matchesPacket⟩
  have result := (bounded_data_receiver_refines frame payload).mp accepted
  dsimp only
  rw [result]
  refine ⟨accepted, rfl, by omega, ?_⟩
  exact accepted_payload_drains_in_order payload size
  done

theorem stuffed_length_limit (source : List Bool) (ones : Nat) (valid : ones ≤ 5) :
    6 * (insertStuff source ones).length ≤ 7 * source.length + ones := by
  induction source generalizing ones with
  | nil => simp [insertStuff]
  | cons bit rest ih =>
    cases bit with
    | false =>
      have carry := ih 0 (by decide)
      simp [insertStuff] at *
      omega
    | true =>
      by_cases full : ones = 5
      · subst ones
        have carry := ih 0 (by decide)
        simp [insertStuff] at *
        omega
      · have carry := ih (ones+1) (by omega)
        simp [insertStuff, full] at *
        omega
  done

theorem maximum_data_wave_bits (payload : List Bool) (size : payload.length = 64) :
    (insertStuff (canonicalDATA1 payload) 0).length + 2 ≤ 114 := by
  have bound := stuffed_length_limit (canonicalDATA1 payload) 0 (by decide)
  simp only [canonicalDATA1, List.length_append, size, crc_low_bits_length, header_length] at bound
  unfold canonicalDATA1
  omega
  done

theorem response_watchdog_budget (rate : PeerRate)
    (sopExact eopExact : Int) (sopTick eopTick : Nat)
    (sopNonnegative : 0 ≤ sopExact) (eopNonnegative : 0 ≤ eopExact)
    (turnaround : 2*sopExact ≤ 15*rate.period)
    (packetLength : eopExact ≤ sopExact + 114*rate.period)
    (sopLo : ((sopTick : Int) - 1) * rate.den < sopExact)
    (sopHi : sopExact ≤ (sopTick : Int) * rate.den)
    (eopLo : ((eopTick : Int) - 1) * rate.den < eopExact)
    (eopHi : eopExact ≤ (eopTick : Int) * rate.den) :
    sopTick + 2 ≤ 124 ∧ eopTick + 2 + 46 ≤ 2022 := by
  have startBy : sopExact ≤ 122 * rate.den := by
    have rateMax := rate.slow
    omega
  have endBy : eopExact ≤ 1974 * rate.den := by
    have rateMax := rate.slow
    omega
  have start := Pinwheel.USBReadFeasibility.quantized_window rate.den sopExact (sopTick : Int)
    0 122 rate.positive sopLo sopHi (by have := rate.positive; omega) startBy
  have stop := Pinwheel.USBReadFeasibility.quantized_window rate.den eopExact (eopTick : Int)
    0 1974 rate.positive eopLo eopHi (by have := rate.positive; omega) endBy
  omega
  done

end Pinwheel.USBTimedFeasibility

namespace Pinwheel.USBWaveformConstruction
open Pinwheel.USBPacketFeasibility Pinwheel.USBClockFeasibility

structure SymbolRun where
  level : Bool
  cells : Nat
  deriving Repr

def expand (runs : List SymbolRun) : List Bool :=
  runs.flatMap (fun run => List.replicate run.cells run.level)

def alternating (previous : Bool) : List SymbolRun → Prop
  | [] => True
  | run :: rest =>
    run.level ≠ previous ∧ 0 < run.cells ∧ run.cells ≤ 7 ∧ alternating run.level rest

def buildRuns (level : Bool) (count : Nat) : List Bool → List SymbolRun
  | [] => [⟨level, count⟩]
  | bit :: rest =>
    if bit then buildRuns level (count+1) rest
    else ⟨level, count⟩ :: buildRuns (!level) 1 rest

theorem expand_cons (first : SymbolRun) (rest : List SymbolRun) :
    expand (first :: rest) = List.replicate first.cells first.level ++ expand rest := rfl

theorem expand_build (bits : List Bool) (level : Bool) (count : Nat) :
    expand (buildRuns level count bits) = List.replicate count level ++ emitNRZI level bits := by
  induction bits generalizing level count with
  | nil => simp [expand, buildRuns, emitNRZI]
  | cons bit rest ih =>
    cases bit with
    | false => simp [buildRuns, expand_cons, emitNRZI, ih]
    | true => simp [buildRuns, emitNRZI, ih, ← List.replicate_append_replicate]
  done

theorem build_alternates (bits : List Bool) (previous level : Bool) (count : Nat)
    (different : level ≠ previous) (nonempty : 0 < count) (bounded : count ≤ 7)
    (restLegal : onesBound bits (count-1) = true) : alternating previous (buildRuns level count bits) := by
  induction bits generalizing previous level count with
  | nil => simp [buildRuns, alternating, different, nonempty, bounded]
  | cons bit rest ih =>
    cases bit with
    | false =>
      simp only [buildRuns, Bool.false_eq_true, if_false, alternating]
      have newLevel : (!level) ≠ level := by cases level <;> decide
      have restBound : onesBound rest (1-1) = true := by simpa [onesBound] using restLegal
      exact ⟨different, nonempty, bounded, ih level (!level) 1 newLevel (by decide) (by decide) restBound⟩
    | true =>
      simp only [buildRuns, if_true]
      simp only [onesBound, Bool.and_eq_true, decide_eq_true_eq] at restLegal
      have carry : count - 1 + 1 = count := by omega
      rw [carry] at restLegal
      have restBound : onesBound rest ((count+1)-1) = true := by simpa using restLegal.2
      exact ih previous level (count+1) different (by omega) (by omega) restBound
  done

def dataRuns (payload : List Bool) : List SymbolRun :=
  buildRuns true 1 (insertStuff ((canonicalDATA1 payload).drop 1) 0)

theorem canonical_starts_with_toggle (payload : List Bool) :
    insertStuff (canonicalDATA1 payload) 0 =
      false :: insertStuff ((canonicalDATA1 payload).drop 1) 0 := by
  rfl

theorem all_data_runs_legal (payload : List Bool) :
    alternating false (dataRuns payload) :=
  build_alternates _ false true 1 (by decide) (by decide) (by decide)
    (stuffed_gap_bound _ 0 (by decide))

theorem data_runs_exact (payload : List Bool) :
    expand (dataRuns payload) = emitNRZI false (insertStuff (canonicalDATA1 payload) 0) := by
  rw [canonical_starts_with_toggle]
  simp [dataRuns, expand_build, emitNRZI]
  done

def ceilTick (num den : Int) : Int := (num + den - 1) / den

theorem ceilTick_bounds (num den : Int) (positive : 0 < den) :
    (ceilTick num den - 1) * den < num ∧ num ≤ ceilTick num den * den := by
  have quotient := Int.ediv_mul_add_emod (num + den - 1) den
  have lo := Int.emod_nonneg (num + den - 1) (Int.ne_of_gt positive)
  have hi := Int.emod_lt_of_pos (num + den - 1) positive
  unfold ceilTick
  rw [Int.sub_mul, Int.one_mul]
  omega
  done

theorem ceilTick_monotone (x y den : Int) (positive : 0 < den) (earlier : x ≤ y) :
    ceilTick x den ≤ ceilTick y den := by
  by_cases order : ceilTick x den ≤ ceilTick y den
  · exact order
  · have ahead : ceilTick y den ≤ ceilTick x den - 1 := by omega
    have before : ceilTick y den * den ≤ (ceilTick x den - 1) * den :=
      Int.mul_le_mul_of_nonneg_right ahead (Int.le_of_lt positive)
    have lo := (ceilTick_bounds x den positive).1
    have hi := (ceilTick_bounds y den positive).2
    omega
  done

def clockSpan (start stop den : Int) : Nat := (ceilTick stop den - ceilTick start den).toNat

theorem span_rounded (start stop den : Int) (positive : 0 < den) (order : start ≤ stop) :
    ∃ phase : Int, -den < phase ∧ phase ≤ 0 ∧
      ((clockSpan start stop den : Int) - 1) * den < phase + (stop - start) ∧
        phase + (stop - start) ≤ (clockSpan start stop den : Int) * den := by
  let first := ceilTick start den
  let last := ceilTick stop den
  let phase := start - first * den
  have begin := ceilTick_bounds start den positive
  have finish := ceilTick_bounds stop den positive
  have increasing := ceilTick_monotone start stop den positive order
  have nonnegative : 0 ≤ last - first := by change 0 ≤ ceilTick stop den - ceilTick start den; omega
  have asInt : (clockSpan start stop den : Int) = last - first := Int.toNat_of_nonneg nonnegative
  refine ⟨phase, ?_, ?_, ?_, ?_⟩
  · simp only [phase, first]
    rw [Int.sub_mul, Int.one_mul] at begin
    omega
  · simp only [phase, first]
    omega
  · rw [asInt, Int.sub_mul, Int.sub_mul, Int.one_mul]
    dsimp only [phase, first, last]
    rw [Int.sub_mul, Int.one_mul] at finish
    omega
  · rw [asInt, Int.sub_mul]
    dsimp only [phase, first, last]
    omega
  done

theorem period_nonnegative (rate : PeerRate) : 0 ≤ rate.period := by
  have positive := rate.positive
  have minRate := rate.fast
  omega
  done

def advanceTime (rate : PeerRate) (start : Int) (symbols : Nat) : Int :=
  start + (symbols : Int) * rate.period

theorem advanceTime_ordered (rate : PeerRate) (start : Int) (cells : Nat) :
    start ≤ advanceTime rate start cells := by
  have positive : 0 ≤ (cells : Int) * rate.period :=
    Int.mul_nonneg (by omega) (period_nonnegative rate)
  unfold advanceTime
  omega
  done

def digitizeRuns (rate : PeerRate) (start : Int) : List SymbolRun → List Run
  | [] => []
  | run :: rest =>
    let stop := advanceTime rate start run.cells
    ⟨run.level, clockSpan start stop rate.den, run.cells⟩ ::
      digitizeRuns rate stop rest

theorem symbolic_trace_measured (rate : PeerRate) (start : Int) (runs : List SymbolRun)
    (previous : Bool) (legal : alternating previous runs) :
    rateTrace rate previous (digitizeRuns rate start runs) := by
  induction runs generalizing start previous with
  | nil => trivial
  | cons run rest ih =>
    rcases legal with ⟨edge, lower, upper, tail⟩
    have monotone := advanceTime_ordered rate start run.cells
    let stop := advanceTime rate start run.cells
    have duration : stop - start = (run.cells : Int) * rate.period := by
      change start + (run.cells : Int) * rate.period - start = _
      omega
    obtain ⟨off, early, late, lo, hi⟩ := span_rounded start stop rate.den rate.positive monotone
    rw [duration] at lo hi
    exact ⟨edge, ⟨⟨lower, upper⟩, off, early, late, lo, hi⟩, ih stop run.level tail⟩
  done

theorem digitize_preserves_bits (rate : PeerRate) (start : Int) (runs : List SymbolRun) :
    intendedWireSymbols (digitizeRuns rate start runs) = expand runs := by
  induction runs generalizing start with
  | nil => rfl
  | cons run rest ih =>
    change List.replicate run.cells run.level ++
        intendedWireSymbols (digitizeRuns rate (advanceTime rate start run.cells) rest) =
      List.replicate run.cells run.level ++ expand rest
    rw [ih]
  done

theorem ceilTick_nonnegative (num den : Int) (valid : 0 < den) (inTime : 0 ≤ num) :
    0 ≤ ceilTick num den := by
  unfold ceilTick
  exact Int.ediv_nonneg (by omega) (by omega)
  done

theorem receiveLineReleased (rate : PeerRate) (returnAt : Int) (atValidTime : 0 ≤ returnAt) :
    (ceilTick (advanceTime rate returnAt 1) rate.den).toNat ≤ (ceilTick returnAt rate.den).toNat + 17 := by
  let stop := advanceTime rate returnAt 1
  have ordered := advanceTime_ordered rate returnAt 1
  obtain ⟨off, early, late, lo, hi⟩ := span_rounded returnAt stop rate.den rate.positive ordered
  have duration : stop - returnAt = 1 * rate.period := by
    change returnAt + (1 : Int) * rate.period - returnAt = _
    omega
  rw [duration] at lo hi
  have holds := Pinwheel.USBReadFeasibility.se0_pulse_widths rate.den rate.period off
    (clockSpan returnAt stop rate.den : Int) rate.positive rate.fast rate.slow early late
    1 (Or.inl rfl) lo hi
  have ahead := ceilTick_monotone returnAt stop rate.den rate.positive ordered
  have endBound : 0 ≤ ceilTick returnAt rate.den := ceilTick_nonnegative _ _ rate.positive atValidTime
  have stopBound : 0 ≤ ceilTick stop rate.den := by omega
  have diff : (clockSpan returnAt stop rate.den : Int) = ceilTick stop rate.den - ceilTick returnAt rate.den :=
    Int.toNat_of_nonneg (by omega)
  have castStop := Int.toNat_of_nonneg stopBound
  have castEnd := Int.toNat_of_nonneg endBound
  change (ceilTick stop rate.den).toNat ≤ (ceilTick returnAt rate.den).toNat + 17
  omega
  done

def wireCells (runs : List SymbolRun) := (runs.map SymbolRun.cells).sum

theorem expand_symbol_count (runs : List SymbolRun) : (expand runs).length = wireCells runs := by
  induction runs with
  | nil => rfl
  | cons first rest ih =>
    simpa [expand_cons, wireCells] using congrArg (first.cells + ·) ih
  done

theorem physical_data_canonical (rate : PeerRate) (sop : Int) (nonnegative : 0 ≤ sop)
    (payload : List Bool) (size : payload.length = 64) :
    let runs := dataRuns payload
    let markerStart := advanceTime rate sop (wireCells runs)
    let returnAt := advanceTime rate markerStart 2
    let rawJ := (ceilTick returnAt rate.den).toNat
    let deviceOff := (ceilTick (advanceTime rate returnAt 1) rate.den).toNat
    let frame := Pinwheel.USBTimedFeasibility.clockedFrame (digitizeRuns rate sop runs)
      (clockSpan markerStart returnAt rate.den) true
    let verdict := decodePinFrame (some frame)
    let queue := commitDecoded verdict
    receiveDataByRegisters frame = some payload ∧
      scheduledAck (rawJ+2) verdict = some (rawJ+48) ∧
      deviceOff < rawJ+48 ∧
      queue.peek.rxBits ++ (queue.tick none true).peek.rxBits = payload ∧
      ((queue.tick none true).tick none true).count.val = 0 := by
  let runs := dataRuns payload
  let markerStart := advanceTime rate sop (wireCells runs)
  let returnAt := advanceTime rate markerStart 2
  have markerOrder := advanceTime_ordered rate markerStart 2
  have markerDuration : returnAt - markerStart = 2 * rate.period := by
    change markerStart + (2 : Int) * rate.period - markerStart = _
    omega
  have startOrder := advanceTime_ordered rate sop (wireCells runs)
  have nonnegativeReturn : 0 ≤ returnAt := by omega
  obtain ⟨phase, early, late, lo, hi⟩ := span_rounded markerStart returnAt rate.den rate.positive markerOrder
  rw [markerDuration] at lo hi
  have sequence := symbolic_trace_measured rate sop runs false (all_data_runs_legal payload)
  have spell : intendedWireSymbols (digitizeRuns rate sop runs) =
      emitNRZI false (insertStuff (canonicalDATA1 payload) 0) :=
    (digitize_preserves_bits rate sop runs).trans (data_runs_exact payload)
  exact Pinwheel.USBTimedFeasibility.ideal_data_recovered rate
    (digitizeRuns rate sop runs) sequence payload size spell (clockSpan markerStart returnAt rate.den)
    (ceilTick returnAt rate.den).toNat (ceilTick (advanceTime rate returnAt 1) rate.den).toNat
    phase early late lo hi (receiveLineReleased rate returnAt nonnegativeReturn)
  done

theorem emit_nrzi_length (bits : List Bool) (previous : Bool) :
    (emitNRZI previous bits).length = bits.length := by
  induction bits generalizing previous with
  | nil => rfl
  | cons head tail ih =>
    simp [emitNRZI, ih]
  done

theorem measured_canonical_deadline (rate : PeerRate) (sop : Int)
    (nonnegative : 0 ≤ sop) (latestDeviceStart : 2*sop ≤ 15*rate.period)
    (payload : List Bool) (size : payload.length = 64) :
    let markerStart := advanceTime rate sop (wireCells (dataRuns payload))
    let returnAt := advanceTime rate markerStart 2
    let rawSop := (ceilTick sop rate.den).toNat
    let rawJ := (ceilTick returnAt rate.den).toNat
    rawSop + 2 ≤ 124 ∧ rawJ + 48 ≤ 2022 := by
  let runs := dataRuns payload
  let markerStart := advanceTime rate sop (wireCells runs)
  let returnAt := advanceTime rate markerStart 2
  have startOrder := advanceTime_ordered rate sop (wireCells runs)
  have markerOrder := advanceTime_ordered rate markerStart 2
  have nonnegativeStop : 0 ≤ returnAt := by omega
  have bodySize : wireCells runs + 2 ≤ 114 := by
    rw [← expand_symbol_count, data_runs_exact, emit_nrzi_length]
    exact Pinwheel.USBTimedFeasibility.maximum_data_wave_bits payload size
  have product : ((wireCells runs + 2 : Nat) : Int) * rate.period ≤ 114 * rate.period :=
    Int.mul_le_mul_of_nonneg_right (by omega) (period_nonnegative rate)
  have endBound : returnAt ≤ sop + 114*rate.period := by
    change sop + (wireCells runs : Int) * rate.period + 2 * rate.period ≤ _
    have formula : ((wireCells runs + 2 : Nat) : Int) * rate.period =
        (wireCells runs : Int) * rate.period + 2 * rate.period := by
      rw [Int.natCast_add, Int.add_mul]
      rfl
    rw [formula] at product
    omega
  have startCeil := ceilTick_bounds sop rate.den rate.positive
  have stopCeil := ceilTick_bounds returnAt rate.den rate.positive
  let rawSop := (ceilTick sop rate.den).toNat
  let rawJ := (ceilTick returnAt rate.den).toNat
  have castSop : (rawSop : Int) = ceilTick sop rate.den :=
    Int.toNat_of_nonneg (ceilTick_nonnegative _ _ rate.positive nonnegative)
  have castJ : (rawJ : Int) = ceilTick returnAt rate.den :=
    Int.toNat_of_nonneg (ceilTick_nonnegative _ _ rate.positive nonnegativeStop)
  rw [← castSop] at startCeil
  rw [← castJ] at stopCeil
  exact Pinwheel.USBTimedFeasibility.response_watchdog_budget rate sop returnAt rawSop rawJ
    nonnegative nonnegativeStop latestDeviceStart endBound startCeil.1 startCeil.2 stopCeil.1 stopCeil.2
  done

end Pinwheel.USBWaveformConstruction

namespace Pinwheel.USBOnlineFeasibility
open Pinwheel.USBPacketFeasibility Pinwheel.USBClockFeasibility

inductive Wire where | j | k | se0 | se1
  deriving DecidableEq, Repr

structure Capture where
  clock : Sampler := {}
  decoder : SymbolRegs := {}
  deriving Repr

def sampleOnTick (s : Capture) (value : Bool) : Option Capture :=
  let seen := tick s.clock value
  (seen.2.foldlM ingestSymbol s.decoder).map (fun decoder => ⟨seen.1, decoder⟩)

structure Pair where
  first : BitVec 32
  second : BitVec 32
  deriving DecidableEq, Repr

inductive Verdict where
  | data (words : Pair)
  | nak | stall | noReply | watchdog | line | eop | stuff | header | length | crc
  deriving DecidableEq, Repr

def verifyFrame (capture : Capture) : Verdict :=
  match finishSymbols capture.decoder with
  | none => .stuff
  | some regs =>
    if regs.consumed = 16 ∧ regs.headerWord = wordFor 16 (header 0x5A) then .nak
    else if regs.consumed = 16 ∧ regs.headerWord = wordFor 16 (header 0x1E) then .stall
    else if regs.consumed < 16 ∨ regs.headerWord ≠ wordFor 16 (header 0x4B) then .header
    else if regs.consumed ≠ 96 then .length
    else if regs.checksum ≠ 0xB001#16 then .crc
    else .data ⟨regs.payloadFirst, regs.payloadSecond⟩

inductive Mode where
  | waiting
  | receive (c : Capture)
  | se0 (c : Capture) (width : Nat)
  | delayAck (words : Pair) (remaining : Nat)
  | ackOnWire (words : Pair) (remaining : Nat)
  | retained (verdict : Verdict)
  deriving Repr

def Mode.terminal : Mode → Bool
  | .retained _ => true
  | _ => false

def ingestLevel (capture : Capture) (value : Bool) : Mode :=
  match sampleOnTick capture value with
  | some c => .receive c
  | none => .retained .stuff

def advanceMode (age : Nat) (mode : Mode) (wire : Wire) : Mode :=
  match mode with
  | .waiting =>
    if wire = .k then ingestLevel {} true
    else if age = 127 then .retained .noReply
    else if wire = .se1 then .retained .line
    else .waiting
  | .receive c =>
    match wire with
    | .j => ingestLevel c false
    | .k => ingestLevel c true
    | .se0 => .se0 c 1
    | .se1 => .retained .line
  | .se0 c width =>
    match wire with
    | .se0 =>
      if width ≥ 33 then .retained .eop
      else .se0 c (width + 1)
    | .j =>
      if 31 ≤ width ∧ width ≤ 33 then
        match verifyFrame c with
        | .data p => .delayAck p 46
        | invalid => .retained invalid
      else .retained .eop
    | _ => .retained .eop
  | .delayAck words down =>
    if down ≤ 1 then .ackOnWire words 304
    else .delayAck words (down-1)
  | .ackOnWire words down =>
    if down ≤ 1 then .retained (.data words)
    else .ackOnWire words (down-1)
  | .retained verdict => .retained verdict

def Mode.resolved : Mode → Bool
  | .ackOnWire _ _ | .retained _ => true
  | _ => false

def ackStarted : Mode → Mode → Bool
  | .delayAck _ _, .ackOnWire _ _ => true
  | _, _ => false

def Mode.visibleWords : Mode → Option Pair
  | .retained (.data words) => some words
  | _ => none

structure Rx where
  age : Nat := 0
  mode : Mode := .waiting
  deriving Repr

def step (s : Rx) (wire : Wire) : Rx × Bool :=
  if s.mode.terminal then (s, false)
  else if s.age ≥ 2047 ∧ s.mode.resolved = false then (⟨2048, .retained .watchdog⟩, false)
  else
    let next := advanceMode s.age s.mode wire
    (⟨s.age+1, next⟩, ackStarted s.mode next)

def run (s : Rx) : List Wire → Rx × Nat
  | [] => (s, 0)
  | w :: rest =>
    let next := step s w
    let more := run next.1 rest
    (more.1, next.2.toNat + more.2)

theorem terminal_retains (s : Rx) (wire : Wire) (closed : s.mode.terminal = true) :
    step s wire = (s, false) := by
  simp [step, closed]
  done

theorem stays_terminal (s : Rx) (trace : List Wire) (closed : s.mode.terminal = true) :
    run s trace = (s, 0) := by
  induction trace with
  | nil => rfl
  | cons wire more ih => simp [run, terminal_retains s wire closed, ih]
  done

theorem no_response_at_128 :
    (run {} (List.replicate 128 .j)).1.mode matches .retained .noReply := by
  decide +kernel
  done

theorem ack_start_in_flight (old next : Mode) (emits : ackStarted old next = true) :
    next.resolved = true ∧ next.terminal = false ∧ next.visibleWords = none := by
  cases old <;> cases next <;> simp_all [ackStarted, Mode.resolved, Mode.terminal, Mode.visibleWords]
  done

theorem emitted_ack_has_no_visible_payload (s : Rx) (wire : Wire)
    (emits : (step s wire).2 = true) :
    (step s wire).1.mode.resolved = true ∧
      (step s wire).1.mode.terminal = false ∧ (step s wire).1.mode.visibleWords = none := by
  by_cases closed : s.mode.terminal = true
  · simp [step, closed] at emits
  · by_cases late : s.age ≥ 2047 ∧ s.mode.resolved = false
    · simp [step, closed, late] at emits
    · simp only [step, closed, late, if_false] at emits ⊢
      exact ack_start_in_flight _ _ emits
  done

theorem ack_at_most_once_after_resolution_step (s : Rx) (w : Wire)
    (closed : s.mode.resolved = true) :
    (step s w).1.mode.resolved = true ∧ (step s w).2 = false := by
  cases s with
  | mk age mode =>
    cases mode <;> simp [Mode.resolved] at closed ⊢
    case ackOnWire words remaining =>
      by_cases finished : remaining ≤ 1
      · simp [step, Mode.terminal, Mode.resolved, advanceMode, ackStarted, finished]
      · simp [step, Mode.terminal, Mode.resolved, advanceMode, ackStarted, finished]
    case retained verdict =>
      simp [step, Mode.terminal]
  done

theorem ack_at_most_once_after_resolution (s : Rx) (trace : List Wire)
    (closed : s.mode.resolved = true) : (run s trace).2 = 0 := by
  induction trace generalizing s with
  | nil => rfl
  | cons w more ih =>
    have after := ack_at_most_once_after_resolution_step s w closed
    simp [run, after.2, ih _ after.1]
  done

theorem at_most_one_ack (s : Rx) (trace : List Wire) : (run s trace).2 ≤ 1 := by
  induction trace generalizing s with
  | nil => simp [run]
  | cons w more ih =>
    cases fires : (step s w).2
    · simpa [run, fires] using ih (step s w).1
    · have resolves := (emitted_ack_has_no_visible_payload s w fires).1
      simp [run, fires, ack_at_most_once_after_resolution _ _ resolves]
  done

theorem unresolved_step (s : Rx) (wire : Wire) (openAfter : (step s wire).1.mode.resolved = false) :
    s.mode.resolved = false ∧ (step s wire).1.age = s.age + 1 ∧ (step s wire).1.age < 2048 := by
  by_cases resolved : s.mode.resolved = true
  · have still := (ack_at_most_once_after_resolution_step s wire resolved).1
    rw [still] at openAfter
    contradiction
  · have live : s.mode.terminal = false := by
      cases status : s.mode <;> simp_all [Mode.terminal, Mode.resolved]
    have openBefore : s.mode.resolved = false := Bool.eq_false_iff.mpr resolved
    by_cases late : s.age ≥ 2047
    · simp only [step, live, Bool.false_eq_true, if_false, late, true_and, openBefore, if_true] at openAfter
      simp [Mode.resolved] at openAfter
    · refine ⟨openBefore, ?_, ?_⟩
      · simp [step, live, late]
      · simp only [step, live, Bool.false_eq_true, if_false, late, false_and]
        omega
  done

theorem unresolved_age (s : Rx) (trace : List Wire)
    (openAfter : (run s trace).1.mode.resolved = false) :
    s.mode.resolved = false ∧ (run s trace).1.age = s.age + trace.length ∧
      (trace ≠ [] → (run s trace).1.age < 2048) := by
  induction trace generalizing s with
  | nil => exact ⟨openAfter, by simp [run], by simp⟩
  | cons wire rest ih =>
    let first := (step s wire).1
    have tailOpen : (run first rest).1.mode.resolved = false := openAfter
    have tail := ih first tailOpen
    have initial := unresolved_step s wire tail.1
    refine ⟨initial.1, ?_, ?_⟩
    · change (run first rest).1.age = s.age + (wire :: rest).length
      rw [tail.2.1, show first.age = s.age+1 from initial.2.1]
      simp [Nat.add_assoc, Nat.add_comm 1]
    · intro _
      change (run first rest).1.age < 2048
      cases rest with
      | nil => exact initial.2.2
      | cons wire more => exact tail.2.2 (by simp)
  done

theorem watchdog_by_2048 (trace : List Wire) (length : 2048 ≤ trace.length) :
    (run {} trace).1.mode.resolved = true := by
  by_cases resolved : (run {} trace).1.mode.resolved = true
  · exact resolved
  · have live := unresolved_age {} trace (Bool.eq_false_iff.mpr resolved)
    have someInput : trace ≠ [] := by
      intro h
      simp [h] at length
    have n := live.2.2 someInput
    have elapsed := live.2.1
    omega
  done

theorem run_append_exact (s : Rx) (front back : List Wire) :
    run s (front ++ back) =
      let first := run s front
      let second := run first.1 back
      (second.1, first.2 + second.2) := by
  induction front generalizing s with
  | nil => simp [run]
  | cons w front ih => simp [run, ih, Nat.add_assoc]
  done

theorem ack_delay_prefix (words : Pair) (trace : List Wire) (age left : Nat)
    (before : trace.length < left) (budget : age+trace.length ≤ 2047) :
    run ⟨age, .delayAck words left⟩ trace =
      (⟨age+trace.length, .delayAck words (left-trace.length)⟩, 0) := by
  induction trace generalizing age left with
  | nil => simp [run]
  | cons wire more ih =>
    have notDue : ¬ left ≤ 1 := by simp at before; omega
    have time : ¬ age ≥ 2047 := by simp at budget; omega
    have next : step ⟨age, .delayAck words left⟩ wire =
        (⟨age+1, .delayAck words (left-1)⟩, false) := by
      simp [step, Mode.terminal, advanceMode, ackStarted, time, notDue]
    have remaining := ih (age+1) (left-1) (by simp at before; omega) (by simp at budget; omega)
    have shifted : age+1+more.length = age+(more.length+1) := by omega
    have shortened : left-1-more.length = left-(more.length+1) := by omega
    rw [run, next]
    dsimp only
    rw [remaining]
    simp [shifted, shortened]
  done

theorem ack_delay_exact (words : Pair) (trace : List Wire) (age : Nat)
    (oneOrMore : 0 < trace.length) (budget : age+trace.length ≤ 2047) :
    run ⟨age, .delayAck words trace.length⟩ trace =
      (⟨age+trace.length, .ackOnWire words 304⟩, 1) := by
  induction trace generalizing age with
  | nil => simp at oneOrMore
  | cons w rest ih =>
    have time : ¬ age ≥ 2047 := by simp at budget; omega
    cases rest with
    | nil => simp [run, step, Mode.terminal, advanceMode, ackStarted, time]
    | cons v rest =>
      have next : step ⟨age, .delayAck words (w :: v :: rest).length⟩ w =
          (⟨age+1, .delayAck words (v::rest).length⟩, false) := by
        simp [step, Mode.terminal, advanceMode, ackStarted, time]
      have after := ih (age+1) (by simp) (by simp at budget ⊢; omega)
      have shifted : age + 1 + (rest.length + 1) = age + (rest.length + 1 + 1) := by omega
      rw [run, next]
      dsimp only
      rw [after]
      simp [shifted]
  done

theorem ack_flight_prefix (words : Pair) (trace : List Wire) (age left : Nat)
    (before : trace.length < left) :
    run ⟨age, .ackOnWire words left⟩ trace =
      (⟨age+trace.length, .ackOnWire words (left-trace.length)⟩, 0) := by
  induction trace generalizing age left with
  | nil => simp [run]
  | cons wire more ih =>
    have notDue : ¬ left ≤ 1 := by simp at before; omega
    have next : step ⟨age, .ackOnWire words left⟩ wire =
        (⟨age+1, .ackOnWire words (left-1)⟩, false) := by
      simp [step, Mode.terminal, Mode.resolved, advanceMode, ackStarted, notDue]
    have remaining := ih (age+1) (left-1) (by simp at before; omega)
    have shifted : age+1+more.length = age+(more.length+1) := by omega
    have shortened : left-1-more.length = left-(more.length+1) := by omega
    rw [run, next]
    dsimp only
    rw [remaining]
    simp [shifted, shortened]
  done

theorem ack_flight_exact (words : Pair) (trace : List Wire) (age : Nat)
    (oneOrMore : 0 < trace.length) :
    run ⟨age, .ackOnWire words trace.length⟩ trace =
      (⟨age+trace.length, .retained (.data words)⟩, 0) := by
  induction trace generalizing age with
  | nil => simp at oneOrMore
  | cons w rest ih =>
    cases rest with
    | nil => simp [run, step, Mode.terminal, Mode.resolved, advanceMode, ackStarted]
    | cons v rest =>
      have next : step ⟨age, .ackOnWire words (w :: v :: rest).length⟩ w =
          (⟨age+1, .ackOnWire words (v::rest).length⟩, false) := by
        simp [step, Mode.terminal, Mode.resolved, advanceMode, ackStarted]
      have after := ih (age+1) (by simp)
      have shifted : age + 1 + (rest.length + 1) = age + (rest.length + 1 + 1) := by omega
      rw [run, next]
      dsimp only
      rw [after]
      simp [shifted]
  done

theorem capture_fold_equiv (tape : List Bool) (c : Capture) :
    tape.foldlM sampleOnTick c =
      let sampled := sampleTrace c.clock tape
      (sampled.2.foldlM ingestSymbol c.decoder).map (fun decoder => ⟨sampled.1, decoder⟩) := by
  induction tape generalizing c with
  | nil => rfl
  | cons wire rest ih =>
    cases parsed : (tick c.clock wire).2.foldlM ingestSymbol c.decoder with
    | none =>
      simp [List.foldlM_cons, sampleOnTick, sampleTrace, List.foldlM_append, parsed]
    | some decodedState =>
      simp [List.foldlM_cons, sampleOnTick, sampleTrace, List.foldlM_append, parsed, ih]
  done

theorem replay_symbols_finish (tape : List Bool) (s : SymbolRegs) :
    replaySymbols s tape = (tape.foldlM ingestSymbol s).bind finishSymbols := by
  induction tape generalizing s with
  | nil => rfl
  | cons level rest ih =>
    cases first : ingestSymbol s level <;> simp [replaySymbols, List.foldlM_cons, first, ih]
  done

def asWire (bit : Bool) : Wire := if bit then .k else .j

theorem receive_ticks_ok (tape : List Bool) (start result : Capture) (age : Nat)
    (budget : age + tape.length ≤ 2047) (sampled : tape.foldlM sampleOnTick start = some result) :
    run ⟨age, .receive start⟩ (tape.map asWire) =
      (⟨age+tape.length, .receive result⟩, 0) := by
  induction tape generalizing start result age with
  | nil =>
    have same : start = result := Option.some.inj sampled
    simp [run, same]
  | cons bit rest ih =>
    have time : ¬ age ≥ 2047 := by simp at budget; omega
    cases next : sampleOnTick start bit with
    | none => simp [next] at sampled
    | some mid =>
      have tailFound : rest.foldlM sampleOnTick mid = some result := by simpa [next] using sampled
      have keep : step ⟨age, .receive start⟩ (asWire bit) = (⟨age+1, .receive mid⟩, false) := by
        cases bit <;> simp [step, asWire, advanceMode, ingestLevel, Mode.terminal, Mode.resolved, ackStarted, next, time]
      have after := ih mid result (age+1) (by simp at budget ⊢; omega) tailFound
      have shifted : age+1+rest.length = age+(rest.length+1) := by omega
      simp [run, keep, after, shifted]
  done

theorem waiting_first_k_enters_same (age : Nat) (tail : List Wire) (budget : age < 2047) :
    run ⟨age, .waiting⟩ (.k :: tail) = run ⟨age, .receive {}⟩ (.k :: tail) := by
  have initial : sampleOnTick {} true = some ⟨⟨true, 7⟩, {}⟩ := rfl
  simp [run, step, Mode.terminal, advanceMode, ingestLevel, ackStarted, show ¬ age ≥ 2047 by omega]
  done

theorem verify_accept (capture : Capture) (regs : LogicalRegs) (finished : finishSymbols capture.decoder = some regs)
    (accepts : acceptRegisters regs) :
    verifyFrame capture = .data ⟨regs.payloadFirst, regs.payloadSecond⟩ := by
  obtain ⟨count, frameHeader, crc⟩ := accepts
  simp [verifyFrame, finished, count, frameHeader, crc]
  done

theorem sampled_canonical_payload (tape payload : List Bool) (size : payload.length = 64)
    (expected : (sampleTrace {} tape).2 = emitNRZI false (insertStuff (canonicalDATA1 payload) 0)) :
    ∃ cap words,
      tape.foldlM sampleOnTick {} = some cap ∧ verifyFrame cap = .data words ∧
      decodeWord words.first 32 ++ decodeWord words.second 32 = payload := by
  let clocked := sampleTrace {} tape
  let logical := canonicalDATA1 payload
  let regs := logical.foldl ingestLogical {}
  have finalized : replaySymbols {} clocked.2 = some regs := by
    change replaySymbols {} (sampleTrace {} tape).2 = some (logical.foldl ingestLogical {})
    rw [expected]
    exact canonical_registers_agree logical
  rw [replay_symbols_finish] at finalized
  have reference : DataReply logical payload := (data_reply_exact _ _).mpr ⟨size, rfl⟩
  have accepts := (reg_accept_matches_data regs logical payload (logical_fold_agrees logical)).mpr reference
  cases stored : clocked.2.foldlM ingestSymbol {} with
  | none =>
    have impossible : (none : Option LogicalRegs) = some regs :=
      (congrArg (fun o => o.bind finishSymbols) stored).symm.trans finalized
    cases impossible
  | some decoded =>
    have finished : finishSymbols decoded = some regs :=
      (congrArg (fun o => o.bind finishSymbols) stored).symm.trans finalized
    let cap : Capture := ⟨clocked.1,decoded⟩
    let words : Pair := ⟨regs.payloadFirst,regs.payloadSecond⟩
    refine ⟨cap, words, ?_, verify_accept cap regs finished accepts.1, accepts.2⟩
    rw [capture_fold_equiv]
    change (clocked.2.foldlM ingestSymbol {}).map (fun b => ⟨clocked.1,b⟩) = some cap
    exact congrArg (Option.map (fun b => (⟨clocked.1,b⟩ : Capture))) stored
  done

theorem silent_before_sop (age cycles : Nat) (budget : age+cycles ≤ 127) :
    run ⟨age, .waiting⟩ (List.replicate cycles .j) = (⟨age+cycles,.waiting⟩,0) := by
  induction cycles generalizing age with
  | zero => simp [run]
  | succ n ih =>
    have early : ¬ age = 127 := by omega
    have time : ¬ age ≥ 2047 := by omega
    have next : step ⟨age, .waiting⟩ .j = (⟨age+1,.waiting⟩,false) := by
      simp [step, Mode.terminal, advanceMode, ackStarted, early, time]
    have tail := ih (age+1) (by omega)
    rw [List.replicate_succ,run,next]
    dsimp only
    rw [tail]
    simp [show age+1+n = age+(n+1) by omega]
  done

theorem se0_counter_span (capture : Capture) (age width further : Nat)
    (widthBound : width+further ≤ 33) (budget : age+further ≤ 2047) :
    run ⟨age, .se0 capture width⟩ (List.replicate further .se0) =
      (⟨age+further,.se0 capture (width+further)⟩,0) := by
  induction further generalizing age width with
  | zero => simp [run]
  | succ n ih =>
    have room : ¬ width ≥ 33 := by omega
    have time : ¬ age ≥ 2047 := by omega
    have next : step ⟨age, .se0 capture width⟩ .se0 =
        (⟨age+1,.se0 capture (width+1)⟩,false) := by
      simp [step, Mode.terminal, advanceMode, ackStarted, room, time]
    have tail := ih (age+1) (width+1) (by omega) (by omega)
    rw [List.replicate_succ,run,next]
    dsimp only
    rw [tail]
    simp [show age+1+n = age+(n+1) by omega, show width+1+n = width+(n+1) by omega]
  done

theorem marked_packet_enters_ack_delay (c : Capture) (words : Pair) (age width : Nat)
    (framing : 31 ≤ width ∧ width ≤ 33) (budget : age+width+1 ≤ 2047)
    (accepted : verifyFrame c = .data words) :
    run ⟨age,.receive c⟩ (List.replicate width .se0 ++ [.j]) =
      (⟨age+width+1, .delayAck words 46⟩, 0) := by
  cases span : width with
  | zero => omega
  | succ n =>
    have inTime : ¬ age ≥ 2047 := by omega
    have first : step ⟨age,.receive c⟩ .se0 = (⟨age+1,.se0 c 1⟩,false) := by
      simp [step, Mode.terminal, advanceMode, ackStarted, inTime]
    have stayed := se0_counter_span c (age+1) 1 n (by omega) (by omega)
    have time : ¬ age+1+n ≥ 2047 := by omega
    have validSpan : 31 ≤ 1+n ∧ 1+n ≤ 33 := by omega
    have final : step ⟨age+1+n,.se0 c (1+n)⟩ .j =
        (⟨age+1+n+1,.delayAck words 46⟩,false) := by
      simp [step, Mode.terminal, advanceMode, ackStarted, time, validSpan.1, validSpan.2, accepted]
    simp only [List.replicate_succ, List.cons_append,run]
    rw [first]
    dsimp only
    rw [run_append_exact, stayed]
    dsimp only
    rw [run, final]
    simp [run, show age+1+n+1 = age+(n+1)+1 by omega]
  done

theorem complete_sampled_data (payload levels : List Bool) (idle width : Nat)
    (awaitAck onAck : List Wire)
    (size : payload.length = 64)
    (firstLevel : ∃ rest, levels = true :: rest)
    (encoded : (sampleTrace {} levels).2 = emitNRZI false (insertStuff (canonicalDATA1 payload) 0))
    (startOnTime : idle ≤ 127) (framing : 31 ≤ width ∧ width ≤ 33)
    (deadline : idle+levels.length+width+1+46 ≤ 2047)
    (gap : awaitAck.length = 46) (flight : onAck.length = 304) :
    let payloadTape := (List.replicate idle .j) ++ (levels.map asWire)
    let endedTape := payloadTape ++ (List.replicate width .se0 ++ [.j])
    let ackTape := endedTape ++ awaitAck
    ∃ words,
      run {} endedTape = (⟨idle+levels.length+width+1,.delayAck words 46⟩,0) ∧
      run {} ackTape = (⟨idle+levels.length+width+1+46,.ackOnWire words 304⟩,1) ∧
      run {} (ackTape++onAck) = (⟨idle+levels.length+width+1+46+304,.retained (.data words)⟩,1) ∧
      decodeWord words.first 32 ++ decodeWord words.second 32 = payload := by
  obtain ⟨c, words, sampled, valid, payloadCorrect⟩ := sampled_canonical_payload levels payload size encoded
  have quiet : run {} (List.replicate idle .j) = (⟨idle,.waiting⟩,0) := by
    simpa using silent_before_sop 0 idle (by omega)
  have recv : run ⟨idle,.waiting⟩ (levels.map asWire) = (⟨idle+levels.length,.receive c⟩,0) := by
    obtain ⟨rest, starts⟩ := firstLevel
    have hostStart : run ⟨idle,.waiting⟩ (levels.map asWire) =
        run ⟨idle,.receive {}⟩ (levels.map asWire) := by
      rw [starts]
      exact waiting_first_k_enters_same idle (rest.map asWire) (by omega)
    rw [hostStart]
    exact receive_ticks_ok levels {} c idle (by omega) sampled
  let payloadTape := (List.replicate idle .j) ++ (levels.map asWire)
  let endedTape := payloadTape ++ (List.replicate width .se0 ++ [.j])
  let ackTape := endedTape ++ awaitAck
  have got : run {} payloadTape = (⟨idle+levels.length,.receive c⟩,0) := by
    unfold payloadTape
    rw [run_append_exact, quiet]
    dsimp only
    rw [recv] <;> simp
  have eos := marked_packet_enters_ack_delay c words (idle+levels.length) width framing (by omega) valid
  have armed : run {} endedTape = (⟨idle+levels.length+width+1,.delayAck words 46⟩,0) := by
    unfold endedTape
    rw [run_append_exact, got]
    dsimp only
    rw [eos] <;> simp
  have ack := ack_delay_exact words awaitAck (idle+levels.length+width+1) (by omega) (by omega)
  rw [gap] at ack
  have sending : run {} ackTape = (⟨idle+levels.length+width+1+46,.ackOnWire words 304⟩,1) := by
    unfold ackTape
    rw [run_append_exact, armed]
    dsimp only
    rw [ack] <;> simp
  have sent := ack_flight_exact words onAck (idle+levels.length+width+1+46) (by omega)
  rw [flight] at sent
  have retained : run {} (ackTape++onAck) =
      (⟨idle+levels.length+width+1+46+304,.retained (.data words)⟩,1) := by
    rw [run_append_exact, sending]
    dsimp only
    rw [sent] <;> simp
  exact ⟨words, armed, sending, retained, payloadCorrect⟩
  done

end Pinwheel.USBOnlineFeasibility

namespace Pinwheel.USBWaveformConstruction
open Pinwheel.USBClockFeasibility Pinwheel.USBPacketFeasibility

theorem ceilSpan_add (x y z den : Int) (positive : 0 < den)
    (xy : x ≤ y) (yz : y ≤ z) :
    clockSpan x y den + clockSpan y z den = clockSpan x z den := by
  have first := ceilTick_monotone x y den positive xy
  have second := ceilTick_monotone y z den positive yz
  have a : (clockSpan x y den : Int) = ceilTick y den - ceilTick x den :=
    Int.toNat_of_nonneg (by omega)
  have b : (clockSpan y z den : Int) = ceilTick z den - ceilTick y den :=
    Int.toNat_of_nonneg (by omega)
  have c : (clockSpan x z den : Int) = ceilTick z den - ceilTick x den :=
    Int.toNat_of_nonneg (by omega)
  omega
  done

theorem digitized_clock_length (rate : PeerRate) (sop : Int) (runs : List SymbolRun) :
    (clockTape (digitizeRuns rate sop runs)).length =
      clockSpan sop (advanceTime rate sop (wireCells runs)) rate.den := by
  induction runs generalizing sop with
  | nil => simp [clockTape, wireCells, digitizeRuns, advanceTime, clockSpan]
  | cons one rest ih =>
    let firstEnd := advanceTime rate sop one.cells
    let wholeEnd := advanceTime rate sop (wireCells (one :: rest))
    have exactEnd : wholeEnd = advanceTime rate firstEnd (wireCells rest) := by
      change advanceTime rate sop (one.cells + wireCells rest) =
        advanceTime rate firstEnd (wireCells rest)
      simp [firstEnd, advanceTime, Int.natCast_add, Int.add_mul, Int.add_assoc]
    change (List.replicate (clockSpan sop firstEnd rate.den) one.level ++
      clockTape (digitizeRuns rate firstEnd rest)).length = clockSpan sop wholeEnd rate.den
    rw [List.length_append, List.length_replicate, ih, ← exactEnd]
    exact ceilSpan_add sop firstEnd wholeEnd rate.den rate.positive
      (advanceTime_ordered rate sop one.cells)
      (exactEnd.symm ▸ advanceTime_ordered rate firstEnd (wireCells rest))
  done

theorem symbolic_has_first (logical : List Bool) (level : Bool) (cells : Nat) :
    ∃ count rest, buildRuns level cells logical = ⟨level,count⟩ :: rest := by
  induction logical generalizing level cells with
  | nil => exact ⟨cells, [], rfl⟩
  | cons bit tail ih =>
    cases bit
    · exact ⟨cells, buildRuns (!level) 1 tail, rfl⟩
    · exact ih level (cells+1)
  done

theorem data_tape_begins_k (rate : PeerRate) (sop : Int) (payload : List Bool) :
    ∃ rest, clockTape (digitizeRuns rate sop (dataRuns payload)) = true :: rest := by
  obtain ⟨count, rest, start⟩ := symbolic_has_first (insertStuff ((canonicalDATA1 payload).drop 1) 0) true 1
  change dataRuns payload = _ at start
  have correct := trace_of_rate rate false _ (symbolic_trace_measured rate sop _
    false (all_data_runs_legal payload))
  rw [start] at correct
  change validSequence false
    (⟨true, clockSpan sop (advanceTime rate sop count) rate.den, count⟩ ::
      digitizeRuns rate (advanceTime rate sop count) rest) at correct
  have width : 0 < clockSpan sop (advanceTime rate sop count) rate.den := by
    have ⟨pos, _, low, _⟩ := correct.2.1
    change 0 < count at pos
    change 16*count ≤ clockSpan sop (advanceTime rate sop count) rate.den + 2 at low
    omega
  rw [start]
  change ∃ restTape, List.replicate (clockSpan sop (advanceTime rate sop count) rate.den) true ++
      clockTape (digitizeRuns rate (advanceTime rate sop count) rest) = true :: restTape
  cases length : clockSpan sop (advanceTime rate sop count) rate.den with
  | zero => omega
  | succ n => exact ⟨List.replicate n true ++ clockTape (digitizeRuns rate (advanceTime rate sop count) rest), rfl⟩
  done

theorem relative_clocks_add_absolute (sop j : Int) (rate : PeerRate) (nonnegative : 0 ≤ sop)
    (ordered : sop ≤ j) :
    (ceilTick sop rate.den).toNat + clockSpan sop j rate.den = (ceilTick j rate.den).toNat := by
  have before := ceilTick_monotone sop j rate.den rate.positive ordered
  have a := Int.toNat_of_nonneg (ceilTick_nonnegative sop rate.den rate.positive nonnegative)
  have b := Int.toNat_of_nonneg (ceilTick_nonnegative j rate.den rate.positive (by omega))
  have c : (clockSpan sop j rate.den : Int) = ceilTick j rate.den - ceilTick sop rate.den :=
    Int.toNat_of_nonneg (by omega)
  omega
  done

open Pinwheel.USBOnlineFeasibility

theorem complete_clocked_data (rate : PeerRate) (sop : Int) (nonnegative : 0 ≤ sop)
    (timely : 2*sop ≤ 15*rate.period) (payload : List Bool) (size : payload.length = 64) :
    let runs := dataRuns payload
    let markerAt := advanceTime rate sop (wireCells runs)
    let j := advanceTime rate markerAt 2
    let rawJ := (ceilTick j rate.den).toNat
    let idle := (ceilTick sop rate.den).toNat + 2
    let tape := clockTape (digitizeRuns rate sop runs)
    let width := clockSpan markerAt j rate.den
    let throughEop := (List.replicate idle .j ++ tape.map asWire) ++ (List.replicate width .se0 ++ [.j])
    let throughAckStart := throughEop ++ List.replicate 46 .j
    ∃ words,
      run {} throughEop = (⟨rawJ+3,.delayAck words 46⟩,0) ∧
      run {} throughAckStart = (⟨rawJ+49,.ackOnWire words 304⟩,1) ∧
      run {} (throughAckStart ++ List.replicate 304 .j) = (⟨rawJ+353,.retained (.data words)⟩,1) ∧
      decodeWord words.first 32 ++ decodeWord words.second 32 = payload := by
  let runs := dataRuns payload
  let markerAt := advanceTime rate sop (wireCells runs)
  let j := advanceTime rate markerAt 2
  let rawJ := (ceilTick j rate.den).toNat
  let idle := (ceilTick sop rate.den).toNat+2
  let tape := clockTape (digitizeRuns rate sop runs)
  let width := clockSpan markerAt j rate.den
  have clocks : idle ≤ 124 ∧ rawJ+48 ≤ 2022 :=
    measured_canonical_deadline rate sop nonnegative timely payload size
  have a := advanceTime_ordered rate sop (wireCells runs)
  have b := advanceTime_ordered rate markerAt 2
  have spanOk : tape.length + width = clockSpan sop j rate.den := by
    change (clockTape (digitizeRuns rate sop runs)).length + clockSpan markerAt j rate.den = _
    rw [digitized_clock_length]
    exact ceilSpan_add sop markerAt j rate.den rate.positive a b
  have absOk : (ceilTick sop rate.den).toNat + clockSpan sop j rate.den = rawJ :=
    relative_clocks_add_absolute sop j rate nonnegative (Int.le_trans a b)
  have anchor : idle + tape.length + width + 1 = rawJ+3 := by
    change (ceilTick sop rate.den).toNat+2+tape.length+width+1 = rawJ+3
    omega
  have markerSpan : j - markerAt = 2*rate.period := by
    change markerAt + (2 : Int)*rate.period - markerAt = _
    omega
  obtain ⟨off, early, late, lo, hi⟩ := span_rounded markerAt j rate.den rate.positive b
  rw [markerSpan] at lo hi
  have framing := end_marker_quantized rate width off early late lo hi
  have sequence := symbolic_trace_measured rate sop runs false (all_data_runs_legal payload)
  have recovered : (sampleTrace {} tape).2 = emitNRZI false (insertStuff (canonicalDATA1 payload) 0) :=
    (sample_runs_exact _ {} (trace_of_rate rate _ _ sequence)).trans
      ((digitize_preserves_bits rate sop runs).trans (data_runs_exact payload))
  have whole := complete_sampled_data payload tape idle width (List.replicate 46 .j)
    (List.replicate 304 .j) size (data_tape_begins_k rate sop payload) recovered
    (by omega) framing (by omega) (by rw [List.length_replicate]) (by rw [List.length_replicate])
  dsimp only at whole ⊢
  rw [anchor] at whole
  exact whole
  done

end Pinwheel.USBWaveformConstruction

namespace Pinwheel.USBWaveformConstruction
open Pinwheel.USBPacketFeasibility Pinwheel.USBClockFeasibility Pinwheel.USBOnlineFeasibility

def ackSymbols : List Wire :=
  (emitNRZI false (insertStuff (header 0xD2) 0)).map asWire ++ [.se0,.se0,.j]

def ackClocks : List Wire := ackSymbols.flatMap (List.replicate 16)

def padValue : Wire → Nat
  | .se0 => 0
  | .k => 1
  | .j => 2
  | .se1 => 3

def capturedAck : List Nat := [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2]

theorem ack_clock_count : ackClocks.length = 304 := by decide +kernel

theorem ack_matches_core_trace : ackClocks.map padValue = capturedAck := by decide +kernel

def drive (mode : Mode) : Option Wire :=
  match mode with
  | .ackOnWire _ left => ackClocks[304-left]?
  | _ => none

theorem ack_flight_prefix (words : Pair) (trace : List Wire) (age left : Nat)
    (flying : trace.length < left) :
    run ⟨age,.ackOnWire words left⟩ trace =
      (⟨age+trace.length,.ackOnWire words (left-trace.length)⟩,0) := by
  induction trace generalizing age left with
  | nil => simp [run]
  | cons w rest ih =>
    have leftTwo : ¬ left ≤ 1 := by simp at flying; omega
    have room : rest.length < left-1 := by simp at flying; omega
    have next : step ⟨age,.ackOnWire words left⟩ w =
        (⟨age+1,.ackOnWire words (left-1)⟩,false) := by
      simp [step,Mode.terminal,Mode.resolved,advanceMode,ackStarted,leftTwo]
    simp only [run,next,List.length_cons,Bool.toNat_false,Nat.zero_add]
    have later := ih (age+1) (left-1) room
    simp only [later]
    simp only [List.length_cons] at flying ⊢
    have a : age+1+rest.length = age+(rest.length+1) := by omega
    have b : left-1-rest.length = left-(rest.length+1) := by omega
    simp [a,b]

theorem each_ack_clock (words : Pair) (age : Nat) (trace : List Wire)
    (within : trace.length < 304) :
    drive (run ⟨age,.ackOnWire words 304⟩ trace).1.mode = ackClocks[trace.length]? := by
  rw [ack_flight_prefix words trace age 304 within]
  simp [drive, show 304-(304-trace.length) = trace.length by omega]

theorem released_after_ack (words : Pair) (age : Nat) (ackInput tail : List Wire)
    (all : ackInput.length = 304) :
    drive (run ⟨age,.ackOnWire words 304⟩ (ackInput ++ tail)).1.mode = none := by
  have final := ack_flight_exact words ackInput age (by omega)
  rw [all] at final
  rw [run_append_exact, final]
  have stayed := stays_terminal ⟨age+304,.retained (.data words)⟩ tail (by rfl)
  simp only [stayed, drive]

theorem no_emit_no_drive (s : Rx) (trace : List Wire)
    (unresolved : s.mode.resolved = false)
    (noEvent : (run s trace).2 = 0) :
    drive (run s trace).1.mode = none := by
  induction trace generalizing s with
  | nil =>
    have h : drive s.mode = none := by
      cases eq : s.mode <;> simp_all [Mode.resolved,drive]
    exact h
  | cons w rest ih =>
    have later : (run (step s w).1 rest).2 = 0 := by simp [run] at noEvent; omega
    have quiet : (step s w).2 = false := by
      cases b : (step s w).2 <;> simp_all [run]
    cases v : (step s w).1.mode with
    | waiting | receive | se0 | delayAck =>
      exact ih _ (by simp [v,Mode.resolved]) later
    | retained verdict =>
      have final := stays_terminal (step s w).1 rest (by simp [v,Mode.terminal])
      simp [run,final,v,drive]
    | ackOnWire words left =>
      cases s with
      | mk age initial =>
        cases initial <;> simp only [Mode.resolved,Bool.true_eq_false] at unresolved
        all_goals
          simp only [step,Mode.terminal,Mode.resolved,Bool.false_eq_true,if_false] at v quiet
          split at v <;> try contradiction
          rename_i timely
          simp only [timely,if_false] at quiet
          dsimp only at v quiet
          rw [v] at quiet
          simp only [ackStarted] at quiet
        all_goals
          cases w <;> simp [advanceMode,ingestLevel] at v <;> grind
  done

end Pinwheel.USBWaveformConstruction

namespace Pinwheel.USBWaveformConstruction
open Pinwheel.USBPacketFeasibility Pinwheel.USBClockFeasibility Pinwheel.USBOnlineFeasibility

def ackPinAt (samples : List Wire) (clock : Nat) : Option Wire :=
  drive (run {} (samples.take (clock+1))).1.mode

theorem quiet_prefix (s : Rx) (tape : List Wire) (count : Nat)
    (silent : (run s tape).2 = 0) :
    (run s (tape.take count)).2 = 0 := by
  have x := run_append_exact s (tape.take count) (tape.drop count)
  rw [List.take_append_drop] at x
  simp only [x] at silent
  omega

theorem ack_pin_schedule (ready : List Wire) (base : Nat) (words : Pair)
    (clocks : ready.length = base+3)
    (pending : run {} ready = (⟨base+3,.delayAck words 46⟩,0))
    (bound : base+48 ≤ 2047)
    (firing : run {} (ready ++ List.replicate 46 .j) =
      (⟨base+49,.ackOnWire words 304⟩,1))
    (tail : List Wire) (clock : Nat) :
    ackPinAt ((ready ++ List.replicate 46 .j) ++ (List.replicate 304 .j ++ tail)) clock =
      if clock < base+48 then none else ackClocks[clock-(base+48)]? := by
  let before := ready ++ List.replicate 45 .j
  let through := ready ++ List.replicate 46 .j
  let rest := List.replicate 304 .j ++ tail
  have beforeLen : before.length = base+48 := by simp [before,clocks]
  have throughLen : through.length = base+49 := by simp [through,clocks]
  change ackPinAt (through ++ rest) clock = _
  unfold ackPinAt
  split
  · rename_i early
    have earlyQuiet := ack_delay_prefix words (List.replicate 45 .j) (base+3) 46
      (by simp) (by simp; omega)
    have noStart : (run {} before).2 = 0 := by
      unfold before
      rw [run_append_exact,pending]
      dsimp only
      rw [earlyQuiet]
      rfl
    have moreInput : through ++ rest = before ++ (Wire.j :: rest) := by
      simp only [through,before,List.append_assoc]
      congr 1
    rw [moreInput,List.take_append_of_le_length (show clock+1 ≤ before.length by omega)]
    exact no_emit_no_drive _ _ (by rfl) (quiet_prefix _ _ _ noStart)
  · rename_i reached
    have afterPrefix : clock+1 ≥ through.length := by omega
    rw [List.take_append, List.take_of_length_le afterPrefix,run_append_exact]
    change drive (run (run {} through).1 (rest.take (clock+1-through.length))).1.mode = _
    rw [firing, throughLen]
    have offset : clock+1-(base+49) = clock-(base+48) := by omega
    rw [offset]
    let index := clock-(base+48)
    change drive (run ⟨base+49,.ackOnWire words 304⟩ (rest.take index)).1.mode =
      ackClocks[index]?
    by_cases active : index < 304
    · have enough : index ≤ rest.length := by simp only [rest,List.length_append,List.length_replicate]; omega
      have ticks : (rest.take index).length = index := List.length_take_of_le enough
      simpa only [ticks] using each_ack_clock words (base+49) (rest.take index) (by omega)
    · have firstEnough : (List.replicate 304 Wire.j).length ≤ index := by rw [List.length_replicate]; omega
      have after : ackClocks[index]? = none := List.getElem?_eq_none (by rw [ack_clock_count]; omega)
      rw [after]
      unfold rest
      rw [List.take_append, List.take_of_length_le firstEnough]
      exact released_after_ack words (base+49) _ _ List.length_replicate
  done

end Pinwheel.USBWaveformConstruction

namespace Pinwheel.USBWaveformConstruction
open Pinwheel.USBPacketFeasibility Pinwheel.USBClockFeasibility Pinwheel.USBOnlineFeasibility

def arrivalSamples (rate : PeerRate) (sop : Int) (payload : List Bool) : List Wire :=
  let runs := dataRuns payload
  let marker := advanceTime rate sop (wireCells runs)
  let returnToJ := advanceTime rate marker 2
  (List.replicate ((ceilTick sop rate.den).toNat+2) .j ++
    (clockTape (digitizeRuns rate sop runs)).map asWire) ++
  (List.replicate (clockSpan marker returnToJ rate.den) .se0 ++ [.j])

theorem first_peer_drive (rate : PeerRate) (sop : Int) (minimum : 2*rate.period ≤ sop) :
    31 ≤ (ceilTick sop rate.den).toNat := by
  have ceiling := (ceilTick_bounds sop rate.den rate.positive).2
  have enough : 788*rate.den ≤ 25*sop := by
    have fast := rate.fast
    omega
  by_cases enoughClocks : 31 ≤ (ceilTick sop rate.den).toNat
  · exact enoughClocks
  have small : ceilTick sop rate.den ≤ 30 := by omega
  have product := Int.mul_le_mul_of_nonneg_right small (Int.le_of_lt rate.positive)
  have pos := rate.positive
  omega

theorem clocked_data_pin (rate : PeerRate) (sop : Int) (nonnegative : 0 ≤ sop)
    (minimum : 2*rate.period ≤ sop) (timely : 2*sop ≤ 15*rate.period)
    (payload : List Bool) (size : payload.length = 64) (tail : List Wire) :
    let marker := advanceTime rate sop (wireCells (dataRuns payload))
    let returnToJ := advanceTime rate marker 2
    let rawJ := (ceilTick returnToJ rate.den).toNat
    let peerSop := (ceilTick sop rate.den).toNat
    let release := (ceilTick (advanceTime rate returnToJ 1) rate.den).toNat
    let input := (arrivalSamples rate sop payload ++ List.replicate 46 .j) ++
      (List.replicate 304 .j ++ tail)
    (∀ clock, ackPinAt input clock =
      if clock < rawJ+48 then none else ackClocks[clock-(rawJ+48)]?) ∧
    (∀ clock, peerSop ≤ clock → clock < release →
      16 ≤ clock ∧ ackPinAt input clock = none) := by
  let runs := dataRuns payload
  let marker := advanceTime rate sop (wireCells runs)
  let returnToJ := advanceTime rate marker 2
  let rawJ := (ceilTick returnToJ rate.den).toNat
  let samples := arrivalSamples rate sop payload
  have sopToMarker := advanceTime_ordered rate sop (wireCells runs)
  have markerToJ := advanceTime_ordered rate marker 2
  have order : sop ≤ returnToJ := Int.le_trans sopToMarker markerToJ
  have jPositive : 0 ≤ returnToJ := by omega
  obtain ⟨words, ready, started, _, _⟩ := complete_clocked_data rate sop nonnegative timely payload size
  have spans : (clockTape (digitizeRuns rate sop runs)).length +
      clockSpan marker returnToJ rate.den = clockSpan sop returnToJ rate.den := by
    rw [digitized_clock_length]
    exact ceilSpan_add sop marker returnToJ rate.den rate.positive sopToMarker markerToJ
  have absolute := relative_clocks_add_absolute sop returnToJ rate nonnegative order
  have len : samples.length = rawJ+3 := by
    simp only [samples,arrivalSamples,List.length_append,List.length_replicate,List.length_map,
      List.length_cons,List.length_nil]
    change (ceilTick sop rate.den).toNat + 2 +
      (clockTape (digitizeRuns rate sop runs)).length + (clockSpan marker returnToJ rate.den+1) =
      (ceilTick returnToJ rate.den).toNat+3
    omega
  have deadline := (measured_canonical_deadline rate sop nonnegative timely payload size).2
  have budget : rawJ+48 ≤ 2047 := by change rawJ+48 ≤ 2022 at deadline; omega
  have output := ack_pin_schedule samples rawJ words len ready budget started tail
  have released := receiveLineReleased rate returnToJ jPositive
  have starts := first_peer_drive rate sop minimum
  refine ⟨output, ?_⟩
  intro clock afterStart beforeRelease
  change clock < (ceilTick (advanceTime rate returnToJ 1) rate.den).toNat at beforeRelease
  have beforeAck : clock < rawJ+48 := by change _ ≤ rawJ+17 at released; omega
  constructor
  · omega
  · exact (output clock).trans (if_pos beforeAck)
  done

theorem ack_launch_from_physical_marker (rate : PeerRate) (j : Int) :
    let launch := (ceilTick j rate.den + 48) * rate.den
    48 * rate.den ≤ launch - j ∧ launch - j < 49 * rate.den := by
  have ⟨before,after⟩ := ceilTick_bounds j rate.den rate.positive
  rw [Int.sub_mul,Int.one_mul] at before
  dsimp only
  rw [Int.add_mul]
  omega

end Pinwheel.USBWaveformConstruction

namespace Pinwheel.USBOnlineFeasibility
open Pinwheel.USBPacketFeasibility Pinwheel.USBClockFeasibility

def finalizeVerdict (state : LogicalRegs) : Outcome → Verdict
  | .data _ => .data ⟨state.payloadFirst,state.payloadSecond⟩
  | .nak => .nak
  | .stall => .stall
  | .noReply => .noReply
  | .eop => .eop
  | .stuff => .stuff
  | .header => .header
  | .length => .length
  | .crc => .crc

theorem sampled_verdict (capture : Capture) (bits : List Bool) (state : LogicalRegs)
    (parsed : finishSymbols capture.decoder = some state)
    (agrees : LogicalAgreement state bits) :
    verifyFrame capture = finalizeVerdict state (classifyBits bits) := by
  have headWord : state.headerWord = wordFor 16 (bits.take 16) := agrees.fields .head
  have namedHeader (pid : Nat) (wide : 16 ≤ bits.length) :
      state.headerWord = wordFor 16 (header pid) ↔ bits.take 16 = header pid := by
    rw [headWord]
    constructor
    · intro equal
      have leftLength : (bits.take 16).length = 16 := List.length_take_of_le wide
      have before := decode_wordFor (bits.take 16) 16 (by omega)
      have after := decode_wordFor (header pid) 16 (by simp)
      rw [leftLength] at before
      simp only [header_length] at after
      rw [← before,← after,equal]
    · intro same
      rw [same]
  have shortWord (pid : Nat) :
      state.consumed = 16 ∧ state.headerWord = wordFor 16 (header pid) ↔ bits = header pid := by
    rw [agrees.count]
    constructor
    · rintro ⟨n,h⟩
      have size : bits.length = 16 := by omega
      have same := (namedHeader pid (by omega)).mp h
      rwa [List.take_of_length_le (show bits.length ≤ 16 by omega)] at same
    · intro equal
      have size : bits.length = 16 := by simp [equal]
      have same : bits.take 16 = header pid := by
        rw [List.take_of_length_le (show bits.length ≤ 16 by omega),equal]
      exact ⟨by simp [size],(namedHeader pid (by omega)).mpr same⟩
  have notDataHeader :
      state.consumed < 16 ∨ state.headerWord ≠ wordFor 16 (header 0x4B) ↔
        bits.take 16 ≠ header 0x4B := by
    by_cases wide : 16 ≤ bits.length
    · have enough : ¬ state.consumed < 16 := by rw [agrees.count]; omega
      simp [enough, namedHeader _ wide]
    · have short : state.consumed < 16 := by rw [agrees.count]; omega
      have different : bits.take 16 ≠ header 0x4B := by
        intro equal
        have sizes := congrArg List.length equal
        simp only [List.length_take,header_length] at sizes
        omega
      simp [short,different]
  have notDataLength : state.consumed ≠ 96 ↔ bits.length ≠ 96 := by rw [agrees.count]; omega
  by_cases correctLength : bits.length = 96
  · have body : (bits.drop 16).length ≤ 80 := by simp [correctLength]
    have residue : state.checksum = (bits.drop 16).foldl usbCrcStep 0xFFFF#16 := by
      simpa [segment,List.take_of_length_le body] using agrees.crc
    simp only [verifyFrame,parsed,shortWord,notDataHeader,notDataLength,correctLength,residue,classifyBits]
    split <;> try rfl
    split <;> try rfl
    split <;> try rfl
    split <;> simp_all [finalizeVerdict]
    split <;> simp_all
  · simp only [verifyFrame,parsed,shortWord,notDataHeader,notDataLength,classifyBits]
    split <;> try rfl
    split <;> try rfl
    split <;> simp_all [finalizeVerdict]
  done

theorem receive_ticks_stuff_fault (tape : List Bool) (state : Capture) (age : Nat)
    (budget : age+tape.length ≤ 2047) (failure : tape.foldlM sampleOnTick state = none) :
    ∃ endAge, endAge ≤ age+tape.length ∧
      run ⟨age,.receive state⟩ (tape.map asWire) = (⟨endAge,.retained .stuff⟩,0) := by
  induction tape generalizing age state with
  | nil => simp at failure
  | cons bit rest ih =>
    have safe : ¬ age ≥ 2047 := by simp at budget; omega
    cases next : sampleOnTick state bit with
    | none =>
      have first : step ⟨age,.receive state⟩ (asWire bit) =
          (⟨age+1,.retained .stuff⟩,false) := by
        cases bit <;> simp [step,asWire,advanceMode,ingestLevel,Mode.terminal,Mode.resolved,ackStarted,next,safe]
      have held := stays_terminal ⟨age+1,.retained .stuff⟩ (rest.map asWire) (by rfl)
      refine ⟨age+1,by simp,?_⟩
      simp [run,first,held]
    | some mid =>
      have first : step ⟨age,.receive state⟩ (asWire bit) =
          (⟨age+1,.receive mid⟩,false) := by
        cases bit <;> simp [step,asWire,advanceMode,ingestLevel,Mode.terminal,Mode.resolved,ackStarted,next,safe]
      obtain ⟨endAge,early,last⟩ := ih mid (age+1) (by simp at budget; omega)
        (by simpa [next] using failure)
      refine ⟨endAge,by simp; omega,?_⟩
      simp [run,first,last]
  done

theorem eop_j_reject (cap : Capture) (age width : Nat) (verdict : Verdict)
    (budget : age+width+1 ≤ 2047) (withinMax : width ≤ 33)
    (started : 0 < width)
    (reject : (if 31 ≤ width then verifyFrame cap else .eop) = verdict)
    (noData : ∀ words, verdict ≠ .data words) :
    run ⟨age,.receive cap⟩ (List.replicate width .se0 ++ [.j]) =
     (⟨age+width+1,.retained verdict⟩,0) := by
  cases span : width with
  | zero => omega
  | succ n =>
    have safe : ¬ age ≥ 2047 := by omega
    have first : step ⟨age,.receive cap⟩ .se0 = (⟨age+1,.se0 cap 1⟩,false) := by
      simp [step,Mode.terminal,advanceMode,ackStarted,safe]
    have counted := se0_counter_span cap (age+1) 1 n (by omega) (by omega)
    have stopSafe : ¬ age+1+n ≥ 2047 := by omega
    have maxOk : 1+n ≤ 33 := by omega
    have last : step ⟨age+1+n,.se0 cap (1+n)⟩ .j =
        (⟨age+1+n+1,.retained verdict⟩,false) := by
      have same : 1+n = n+1 := by omega
      rw [same] at maxOk ⊢
      rw [span] at reject
      by_cases longEnough : 31 ≤ n+1
      · rw [if_pos longEnough] at reject
        simp [step,Mode.terminal,advanceMode,Mode.resolved,longEnough,maxOk,stopSafe,reject]
        cases verdict <;> simp_all [ackStarted]
      · rw [if_neg longEnough] at reject
        simp [step,Mode.terminal,advanceMode,Mode.resolved,longEnough,stopSafe,← reject,ackStarted]
    simp only [List.replicate_succ,List.cons_append,run]
    rw [first]
    dsimp only
    rw [run_append_exact,counted]
    dsimp only
    rw [run,last]
    simp [run,show age+1+n+1 = age+(n+1)+1 by omega]
  done

end Pinwheel.USBOnlineFeasibility

namespace Pinwheel.USBOnlineFeasibility
open Pinwheel.USBPacketFeasibility Pinwheel.USBClockFeasibility

theorem good_stuff_sampled (tape bits : List Bool)
    (decoded : (sampleTrace {} tape).2 = emitNRZI false (insertStuff bits 0)) :
    ∃ cap, tape.foldlM sampleOnTick {} = some cap ∧
      finishSymbols cap.decoder = some (bits.foldl ingestLogical {}) := by
  let clocked := sampleTrace {} tape
  have finished : replaySymbols {} clocked.2 = some (bits.foldl ingestLogical {}) := by
    change replaySymbols {} (sampleTrace {} tape).2 = _
    rw [decoded]
    exact canonical_registers_agree bits
  rw [replay_symbols_finish] at finished
  cases body : clocked.2.foldlM ingestSymbol {} with
  | none => rw [body] at finished; contradiction
  | some regs =>
    refine ⟨⟨clocked.1,regs⟩,?_,?_⟩
    · rw [capture_fold_equiv]
      change (clocked.2.foldlM ingestSymbol {}).map (fun d => (⟨clocked.1,d⟩ : Capture)) =
        some (⟨clocked.1,regs⟩ : Capture)
      rw [body]
      rfl
    · exact (congrArg (fun d => d.bind finishSymbols) body).symm.trans finished
  done

theorem replay_begun_body (idle : Nat) (tape : List Bool) (cap : Capture)
    (initial : ∃ rest, tape = true :: rest) (waiting : idle ≤ 127)
    (budget : idle+tape.length ≤ 2047) (sampled : tape.foldlM sampleOnTick {} = some cap) :
    run {} (List.replicate idle .j ++ tape.map asWire) =
      (⟨idle+tape.length,.receive cap⟩,0) := by
  have quiet : run {} (List.replicate idle .j) = (⟨idle,.waiting⟩,0) := by
    simpa using silent_before_sop 0 idle (by omega)
  have same : run ⟨idle,.waiting⟩ (tape.map asWire) =
      run ⟨idle,.receive {}⟩ (tape.map asWire) := by
    obtain ⟨rest,first⟩ := initial
    rw [first]
    exact waiting_first_k_enters_same idle (rest.map asWire) (by omega)
  rw [run_append_exact,quiet]
  dsimp only
  rw [same, receive_ticks_ok _ _ cap _ budget sampled]
  rfl
  done

theorem clock_trace_negative (idle width : Nat) (tape bits : List Bool) (v : Verdict)
    (initial : ∃ rest, tape = true :: rest) (waiting : idle ≤ 127)
    (budget : idle+tape.length+width+1 ≤ 2047) (eop : 31 ≤ width ∧ width ≤ 33)
    (decoded : (sampleTrace {} tape).2 = emitNRZI false (insertStuff bits 0))
    (reject : finalizeVerdict (bits.foldl ingestLogical {}) (classifyBits bits) = v)
    (noData : ∀ p, v ≠ .data p) (tail : List Wire) :
    run {} ((List.replicate idle .j ++ tape.map asWire) ++
      ((List.replicate width .se0 ++ [.j]) ++ tail)) =
      (⟨idle+tape.length+width+1,.retained v⟩,0) := by
  obtain ⟨cap, entered, finalized⟩ := good_stuff_sampled tape bits decoded
  have verdict := (sampled_verdict cap bits _ finalized (logical_fold_agrees bits)).trans reject
  have readBody := replay_begun_body idle tape cap initial waiting (by omega) entered
  have ending := eop_j_reject cap (idle+tape.length) width v budget eop.2 (by omega)
    (by rw [if_pos eop.1]; exact verdict) noData
  rw [run_append_exact,readBody]
  dsimp only
  rw [run_append_exact,ending]
  dsimp only
  rw [stays_terminal ⟨_,.retained v⟩ tail (by rfl)]
  rfl
  done

theorem clock_trace_stuff (idle width : Nat) (tape : List Bool)
    (initial : ∃ rest, tape = true :: rest) (waiting : idle ≤ 127)
    (budget : idle+tape.length+width+1 ≤ 2047) (eop : 31 ≤ width ∧ width ≤ 33)
    (rejected : removeStuff (readNRZI false (sampleTrace {} tape).2) 0 = none)
    (tail : List Wire) :
    ∃ endAge, endAge ≤ idle+tape.length+width+1 ∧
      run {} ((List.replicate idle .j ++ tape.map asWire) ++ ((List.replicate width .se0 ++ [.j]) ++ tail)) =
        (⟨endAge,.retained .stuff⟩,0) := by
  let sample := sampleTrace {} tape
  have failed : replaySymbols {} sample.2 = none := by
    change replaySymbols {} (sampleTrace {} tape).2 = none
    rw [replay_symbols_refine]
    change (removeStuff (readNRZI false (sampleTrace {} tape).2) 0).map _ = none
    rw [rejected]
    rfl
  rw [replay_symbols_finish] at failed
  have onTicks := capture_fold_equiv tape {}
  change tape.foldlM sampleOnTick {} =
    (sample.2.foldlM ingestSymbol {}).map (fun d => ⟨sample.1,d⟩) at onTicks
  cases body : sample.2.foldlM ingestSymbol {} with
  | none =>
    have failure : tape.foldlM sampleOnTick {} = none := by rw [onTicks,body]; rfl
    obtain ⟨age,when,stopped⟩ := receive_ticks_stuff_fault tape {} idle (by omega) failure
    have silent : run {} (List.replicate idle .j) = (⟨idle,.waiting⟩,0) := by
      simpa using silent_before_sop 0 idle (by omega)
    have same : run ⟨idle,.waiting⟩ (tape.map asWire) =
        run ⟨idle,.receive {}⟩ (tape.map asWire) := by
      obtain ⟨rest,first⟩ := initial
      rw [first]
      exact waiting_first_k_enters_same idle (rest.map asWire) (by omega)
    refine ⟨age,by omega,?_⟩
    rw [run_append_exact,run_append_exact,silent]
    dsimp only
    rw [same,stopped]
    dsimp only
    rw [stays_terminal ⟨age,.retained .stuff⟩ _ (by rfl)]
    rfl
  | some regs =>
    let cap : Capture := ⟨sample.1,regs⟩
    have captured : tape.foldlM sampleOnTick {} = some cap := by rw [onTicks,body]; rfl
    have invalid : finishSymbols cap.decoder = none :=
      (congrArg (fun d => d.bind finishSymbols) body).symm.trans failed
    have got := replay_begun_body idle tape cap initial waiting (by omega) captured
    have ended := eop_j_reject cap (idle+tape.length) width .stuff budget eop.2 (by omega)
      (by simp [verifyFrame,invalid,eop.1]) (by intro p h; cases h)
    refine ⟨_,Nat.le_refl _,?_⟩
    rw [run_append_exact,got]
    dsimp only
    rw [run_append_exact,ended]
    dsimp only
    rw [stays_terminal ⟨_,.retained .stuff⟩ tail (by rfl)]
    rfl
  done

end Pinwheel.USBOnlineFeasibility

namespace Pinwheel.USBWaveformConstruction
open Pinwheel.USBPacketFeasibility Pinwheel.USBClockFeasibility Pinwheel.USBOnlineFeasibility

theorem digitized_starts_k (rate : PeerRate) (sop : Int) (postToggle : List Bool)
    (legal : onesBound postToggle 0 = true) :
    ∃ rest, clockTape (digitizeRuns rate sop (buildRuns true 1 postToggle)) = true :: rest := by
  obtain ⟨count,rest,start⟩ := symbolic_has_first postToggle true 1
  have shape := build_alternates postToggle false true 1 (by decide) (by decide) (by decide) legal
  have digits := trace_of_rate rate false _ (symbolic_trace_measured rate sop _ false shape)
  rw [start] at digits ⊢
  change validSequence false
    (⟨true,clockSpan sop (advanceTime rate sop count) rate.den,count⟩ ::
      digitizeRuns rate (advanceTime rate sop count) rest) at digits
  have positive : 0 < clockSpan sop (advanceTime rate sop count) rate.den := by
    have ⟨number,_,low,_⟩ := digits.2.1
    change 0 < count at number
    change 16*count ≤ clockSpan sop (advanceTime rate sop count) rate.den+2 at low
    omega
  change ∃ more, List.replicate (clockSpan sop (advanceTime rate sop count) rate.den) true ++
    clockTape (digitizeRuns rate (advanceTime rate sop count) rest) = true :: more
  cases span : clockSpan sop (advanceTime rate sop count) rate.den with
  | zero => omega
  | succ n =>
    exact ⟨List.replicate n true ++ clockTape (digitizeRuns rate (advanceTime rate sop count) rest),rfl⟩
  done

def negativeRuns (afterFirst : List Bool) : List SymbolRun :=
  buildRuns true 1 (insertStuff afterFirst 0)

theorem clocked_negative_reply (rate : PeerRate) (sop : Int) (nonnegative : 0 ≤ sop)
    (timely : 2*sop ≤ 15*rate.period) (afterFirst : List Bool) (size : afterFirst.length ≤ 95)
    (v : Verdict) (reject : finalizeVerdict ((false::afterFirst).foldl ingestLogical {})
      (classifyBits (false::afterFirst)) = v)
    (noData : ∀ w, v ≠ .data w) (tail : List Wire) :
    let runs := negativeRuns afterFirst
    let markerAt := advanceTime rate sop (wireCells runs)
    let rawReturn := advanceTime rate markerAt 2
    let idle := (ceilTick sop rate.den).toNat + 2
    let tape := clockTape (digitizeRuns rate sop runs)
    let span := clockSpan markerAt rawReturn rate.den
    run {} ((List.replicate idle .j ++ tape.map asWire) ++
      ((List.replicate span .se0 ++ [.j]) ++ tail)) =
      (⟨(ceilTick rawReturn rate.den).toNat+3,.retained v⟩,0) := by
  let bits := false :: afterFirst
  let stuffed := insertStuff afterFirst 0
  let runs := negativeRuns afterFirst
  let markerAt := advanceTime rate sop (wireCells runs)
  let rawReturn := advanceTime rate markerAt 2
  let idle := (ceilTick sop rate.den).toNat+2
  let tape := clockTape (digitizeRuns rate sop runs)
  let span := clockSpan markerAt rawReturn rate.den
  have noLongOnes := stuffed_gap_bound afterFirst 0 (by decide)
  have shape := build_alternates stuffed false true 1 (by decide) (by decide) (by decide) noLongOnes
  have exactWave : expand runs = emitNRZI false (insertStuff bits 0) := by
    simp [runs,negativeRuns,expand_build,bits,emitNRZI,insertStuff]
  have cellCount : wireCells runs + 2 ≤ 114 := by
    have bitCount := Pinwheel.USBTimedFeasibility.stuffed_length_limit bits 0 (by decide)
    have bitSize : bits.length ≤ 96 := by simp [bits]; omega
    rw [← expand_symbol_count,exactWave,emit_nrzi_length]
    omega
  have timing1 := advanceTime_ordered rate sop (wireCells runs)
  have timing2 := advanceTime_ordered rate markerAt 2
  have ordered := Int.le_trans timing1 timing2
  have rawOk : 0 ≤ rawReturn := by omega
  have cellSpan : (wireCells runs : Int)*rate.period + 2*rate.period ≤ 114*rate.period := by
    have count : (wireCells runs : Int)+2 ≤ 114 := by omega
    have compared := Int.mul_le_mul_of_nonneg_right count (period_nonnegative rate)
    rwa [Int.add_mul] at compared
  have timeBound : rawReturn ≤ sop+114*rate.period := by
    change sop+(wireCells runs : Int)*rate.period+2*rate.period ≤ _
    omega
  have hs := ceilTick_bounds sop rate.den rate.positive
  have hj := ceilTick_bounds rawReturn rate.den rate.positive
  have rawSopAsNat := Int.toNat_of_nonneg (ceilTick_nonnegative sop rate.den rate.positive nonnegative)
  have rawReturnAsNat := Int.toNat_of_nonneg (ceilTick_nonnegative rawReturn rate.den rate.positive rawOk)
  have limits := Pinwheel.USBTimedFeasibility.response_watchdog_budget rate sop rawReturn
    (ceilTick sop rate.den).toNat (ceilTick rawReturn rate.den).toNat nonnegative rawOk timely timeBound
    (by rw [rawSopAsNat]; exact hs.1) (by rw [rawSopAsNat]; exact hs.2)
    (by rw [rawReturnAsNat]; exact hj.1) (by rw [rawReturnAsNat]; exact hj.2)
  have exactTape : tape.length + span = clockSpan sop rawReturn rate.den := by
    change (clockTape (digitizeRuns rate sop runs)).length + span = _
    rw [digitized_clock_length]
    exact ceilSpan_add sop markerAt rawReturn rate.den rate.positive timing1 timing2
  have absolute := relative_clocks_add_absolute sop rawReturn rate nonnegative ordered
  have elapsed : idle+tape.length+span+1 = (ceilTick rawReturn rate.den).toNat+3 := by
    change (ceilTick sop rate.den).toNat+2+tape.length+span+1 = _
    omega
  have markerSize : rawReturn-markerAt = 2*rate.period := by
    change markerAt+(2:Int)*rate.period-markerAt = _
    omega
  obtain ⟨off,early,late,lo,hi⟩ := span_rounded markerAt rawReturn rate.den rate.positive timing2
  rw [markerSize] at lo hi
  have framing := end_marker_quantized rate span off early late lo hi
  have measured := symbolic_trace_measured rate sop runs false shape
  have readBack : (sampleTrace {} tape).2 = emitNRZI false (insertStuff bits 0) :=
    (sample_runs_exact _ {} (trace_of_rate rate _ _ measured)).trans
      ((digitize_preserves_bits rate sop runs).trans exactWave)
  have initial : ∃ rest, tape = true :: rest := digitized_starts_k rate sop stuffed noLongOnes
  have onTime : idle ≤ 127 := by change (ceilTick sop rate.den).toNat+2 ≤ _; omega
  have checked := clock_trace_negative idle span tape bits v initial onTime
    (by omega) framing readBack reject noData tail
  rw [elapsed] at checked
  exact checked
  done

end Pinwheel.USBWaveformConstruction

namespace Pinwheel.USBOnlineFeasibility
open Pinwheel.USBPacketFeasibility Pinwheel.USBClockFeasibility

theorem invalid_eop_exit (cap : Capture) (age width : Nat) (exit : Wire)
    (observed : 0 < width ∧ width ≤ 33) (nonIdle : exit ≠ .j) (nonSe0 : exit ≠ .se0)
    (budget : age+width+1 ≤ 2047) (tail : List Wire) :
    run ⟨age,.receive cap⟩ ((List.replicate width .se0 ++ [exit]) ++ tail) =
      (⟨age+width+1,.retained .eop⟩,0) := by
  cases span : width with
  | zero => omega
  | succ n =>
    have safe : ¬ age ≥ 2047 := by omega
    have first : step ⟨age,.receive cap⟩ .se0 = (⟨age+1,.se0 cap 1⟩,false) := by
      simp [step,Mode.terminal,advanceMode,ackStarted,safe]
    have counted := se0_counter_span cap (age+1) 1 n (by omega) (by omega)
    have stopSafe : ¬ age+1+n ≥ 2047 := by omega
    have last : step ⟨age+1+n,.se0 cap (1+n)⟩ exit =
        (⟨age+1+n+1,.retained .eop⟩,false) := by
      cases exit <;> simp_all [step,Mode.terminal,Mode.resolved,advanceMode,ackStarted]
    have ageExact : age+1+n+1 = age+(n+1)+1 := by omega
    have seq : run ⟨age,.receive cap⟩ (List.replicate (n+1) .se0 ++ [exit]) =
      (⟨age+(n+1)+1,.retained .eop⟩,0) := by
      simp only [List.replicate_succ,List.cons_append,run]
      rw [first]
      dsimp only
      rw [run_append_exact,counted]
      dsimp only
      rw [run,last]
      simp [run,ageExact]
    rw [run_append_exact,seq]
    dsimp only
    rw [stays_terminal ⟨_,.retained .eop⟩ tail (by rfl)]
    rfl
  done

theorem invalid_eop_long (cap : Capture) (age : Nat) (tail : List Wire)
    (budget : age+34 ≤ 2047) :
    run ⟨age,.receive cap⟩ (List.replicate 34 .se0 ++ tail) =
      (⟨age+34,.retained .eop⟩,0) := by
  have safe : ¬ age ≥ 2047 := by omega
  have first : step ⟨age,.receive cap⟩ .se0 = (⟨age+1,.se0 cap 1⟩,false) := by
    simp [step,Mode.terminal,advanceMode,ackStarted,safe]
  have counted := se0_counter_span cap (age+1) 1 32 (by omega) (by omega)
  have stopSafe : ¬ age+1+32 ≥ 2047 := by omega
  have last : step ⟨age+1+32,.se0 cap 33⟩ .se0 =
      (⟨age+34,.retained .eop⟩,false) := by
    simp [step,Mode.terminal,Mode.resolved,advanceMode,ackStarted,stopSafe,Nat.add_assoc]
  have cells : List.replicate 34 Wire.se0 = .se0 :: (List.replicate 32 .se0 ++ [.se0]) := by
    decide +kernel
  rw [cells,List.cons_append,run,first]
  dsimp only
  rw [List.append_assoc,run_append_exact,counted]
  dsimp only
  simp only [List.singleton_append]
  rw [run,last]
  dsimp only
  rw [stays_terminal ⟨age+34,.retained .eop⟩ tail (by rfl)]
  rfl
  done

end Pinwheel.USBOnlineFeasibility

namespace Pinwheel.USBWaveformConstruction
open Pinwheel.USBPacketFeasibility Pinwheel.USBClockFeasibility Pinwheel.USBOnlineFeasibility

theorem negative_pin_quiet (trace : List Wire) (age : Nat) (v : Verdict)
    (complete : run {} trace = (⟨age,.retained v⟩,0))
    (bad : ∀ words, v ≠ .data words) (clock : Nat) :
    ackPinAt trace clock = none ∧
      (run {} (trace.take (clock+1))).1.mode.visibleWords = none := by
  have countZero : (run {} trace).2 = 0 := by rw [complete]
  constructor
  · exact no_emit_no_drive _ _ (by rfl) (quiet_prefix _ _ _ countZero)
  · cases status : (run {} (trace.take (clock+1))).1.mode with
    | waiting | receive | se0 | delayAck | ackOnWire => rfl
    | retained observed =>
      cases observed <;> try rfl
      case data words =>
        have split := run_append_exact {} (trace.take (clock+1)) (trace.drop (clock+1))
        rw [List.take_append_drop] at split
        have sticky := stays_terminal (run {} (trace.take (clock+1))).1 (trace.drop (clock+1))
          (by simp [status,Mode.terminal])
        dsimp only at split
        rw [sticky,complete] at split
        have same := congrArg (fun (r : Rx × Nat) => r.1.mode) split
        dsimp only at same
        rw [status] at same
        cases same
        exact False.elim (bad words rfl)
  done

end Pinwheel.USBWaveformConstruction
