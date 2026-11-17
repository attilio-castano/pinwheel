import Std

/-! Classical CAN base-format data frames with DLC=1. The wire alphabet uses
`false` for dominant and `true` for recessive. A separate receiver supplies
the dominant ACK. The observer keeps a fixed 64-slot receive window. -/
namespace Pinwheel.Program.StreamingCAN

private def msbBits (value : BitVec n) : List Bool :=
  (List.ofFn fun bit : Fin n => value.getLsbD bit.val).reverse

private def msbValue (n : Nat) (bits : List Bool) : BitVec n :=
  (BitVec.ofBoolListLE bits.reverse).setWidth n

private def formatBits : List Bool := [false, false, false, false, false, false, true]

private def dataFields (identifier : BitVec 11) (payload : BitVec 8) : List Bool :=
  [false] ++ msbBits identifier ++ formatBits ++ msbBits payload

/-- CRC-15/CAN, with the implicit leading coefficient omitted from the shift register. -/
def crc15 (bits : List Bool) : BitVec 15 :=
  bits.foldl (fun crc bit =>
    let shifted := crc <<< 1
    if bit != crc[14] then shifted ^^^ 0x4599 else shifted) 0

private def consecutive (previous : Bool) (run : Nat) (bit : Bool) : Nat :=
  if bit == previous then run + 1 else 1

/-- Insert the complement immediately after the fifth equal bit, including at
    the end of the CRC sequence. The negative control flips the first insertion. -/
private def stuff (corrupt : Bool) (previous : Bool) (run : Nat) : List Bool → List Bool
  | [] => []
  | bit :: rest =>
    let next := consecutive previous run bit
    if next = 5 then
      bit :: (if corrupt then bit else !bit) :: stuff false (!bit) 1 rest
    else bit :: stuff corrupt bit next rest

private def needsStuff (previous : Bool) (run : Nat) : List Bool → Bool
  | [] => false
  | bit :: rest =>
    let next := consecutive previous run bit
    if next = 5 then true else needsStuff bit next rest

/-- Take a known number of unstuffed bits and return the remaining wire suffix.
    An expected stuff bit must be present and have the complementary value. -/
private def destuff (remaining : Nat) (previous : Bool) (run : Nat)
    (wire : List Bool) : Option (List Bool × List Bool) :=
  match remaining, wire with
  | 0, _ => some ([], wire)
  | _ + 1, [] => none
  | remaining + 1, bit :: rest =>
    let next := consecutive previous run bit
    let prepend (result : List Bool × List Bool) := (bit :: result.1, result.2)
    if next = 5 then
      match rest with
      | [] => none
      | inserted :: tail =>
        if inserted == !bit then (destuff remaining inserted 1 tail).map prepend else none
    else (destuff remaining bit next rest).map prepend

private def trailer : List Bool := [true, false] ++ List.replicate 8 true

private def paddedTrailer (length : Nat) : List Bool :=
  trailer ++ List.replicate (64 - (length + trailer.length)) true

private def fixedWindow (wire : List Bool) : List Bool :=
  wire ++ paddedTrailer wire.length

private def protectedBits (identifier : BitVec 11) (payload : BitVec 8) (badCRC : Bool) :
    List Bool :=
  let fields := dataFields identifier payload
  let crc := crc15 fields
  fields ++ msbBits (if badCRC then crc ^^^ 1 else crc)

private def encode (identifier : BitVec 11) (payload : BitVec 8) (badStuff badCRC : Bool) :
    List Bool :=
  fixedWindow (stuff badStuff false 0 (protectedBits identifier payload badCRC))

def frameBits (identifier : BitVec 11) (payload : BitVec 8) : List Bool :=
  encode identifier payload false false

def badStuffBits (identifier : BitVec 11) (payload : BitVec 8) : List Bool :=
  encode identifier payload true false

def badCRCBits (identifier : BitVec 11) (payload : BitVec 8) : List Bool :=
  encode identifier payload false true

private def decodeFields (bits : List Bool) : Option (BitVec 11 × BitVec 8) :=
  let fields := bits.take 27
  let identifier := msbValue 11 ((fields.drop 1).take 11)
  let payload := msbValue 8 (fields.drop 19)
  if fields = dataFields identifier payload ∧ bits.drop 27 = msbBits (crc15 fields)
  then some (identifier, payload) else none

/-- Verify the fixed format, stuffing, CRC, and acknowledged EOF on the
    captured window. Recessive samples after EOF fill the unused slots. -/
def decodeFrame (wire : List Bool) : Option (BitVec 11 × BitVec 8) :=
  if wire.length = 64 then
    match destuff 42 false 0 wire with
    | none => none
    | some (bits, rest) =>
      if rest.take 10 = trailer ∧ (rest.drop 10).all id = true then decodeFields bits
      else none
  else none

@[simp] private theorem msbBits_length (v : BitVec n) : (msbBits v).length = n := by
  simp [msbBits]

@[simp] private theorem dataFields_length (identifier : BitVec 11) (payload : BitVec 8) :
    (dataFields identifier payload).length = 27 := by
  simp [dataFields, formatBits]

@[simp] private theorem protectedBits_length (identifier : BitVec 11) (payload : BitVec 8)
    (badCRC : Bool) : (protectedBits identifier payload badCRC).length = 42 := by
  simp [protectedBits]

private theorem destuff_stuff (fields : List Bool) (previous : Bool) (run : Nat)
    (tail : List Bool) :
    destuff fields.length previous run (stuff false previous run fields ++ tail) =
      some (fields, tail) := by
  induction fields generalizing previous run with
  | nil => rfl
  | cons bit rest ih =>
    by_cases inserts : consecutive previous run bit = 5 <;>
      simp [stuff, destuff, inserts, ih]

private theorem destuff_bad (fields : List Bool) (previous : Bool) (run : Nat)
    (tail : List Bool) (insertion : needsStuff previous run fields = true) :
    destuff fields.length previous run (stuff true previous run fields ++ tail) = none := by
  induction fields generalizing previous run with
  | nil => contradiction
  | cons bit rest ih =>
    by_cases inserts : consecutive previous run bit = 5
    · cases bit <;> simp [stuff, destuff, inserts]
    · simp [needsStuff, inserts] at insertion
      simp [stuff, destuff, inserts, ih _ _ insertion]

private theorem consecutive_le (previous bit : Bool) (run : Nat) :
    consecutive previous run bit ≤ run + 1 := by
  unfold consecutive
  split <;> omega

/-- The first insertion requires five original bits. An insertion resets the
    physical run to one, so each later insertion costs at least four more. -/
private theorem stuff_bound (fields : List Bool) (corrupt previous : Bool) (run : Nat)
    (runBound : run ≤ 4) : 4 * (stuff corrupt previous run fields).length ≤ 5 * fields.length + run := by
  induction fields generalizing corrupt previous run with
  | nil => simp [stuff]
  | cons bit rest ih =>
    have next := consecutive_le previous bit run
    by_cases inserts : consecutive previous run bit = 5
    · have bound := ih false (!bit) 1 (by decide)
      simp only [stuff, inserts, if_true, List.length_cons]
      omega
    · have bound := ih corrupt bit (consecutive previous run bit) (by omega)
      simp only [stuff, inserts, if_false, List.length_cons]
      omega

private theorem needsStuff_prefix (earlier later : List Bool) (previous : Bool) (run : Nat)
    (runBound : run ≤ 4) (forced : ∀ p n, n ≤ 4 → needsStuff p n later = true) :
    needsStuff previous run (earlier ++ later) = true := by
  induction earlier generalizing previous run with
  | nil => exact forced _ _ runBound
  | cons bit rest ih =>
    have next := consecutive_le previous bit run
    by_cases inserts : consecutive previous run bit = 5
    · simp [needsStuff, inserts]
    · simpa [needsStuff, inserts] using ih bit _ (by omega)

private theorem format_forces_stuff (rest : List Bool) (previous : Bool) (run : Nat)
    (runBound : run ≤ 4) : needsStuff previous run (formatBits ++ rest) = true := by
  have casesRun : run = 0 ∨ run = 1 ∨ run = 2 ∨ run = 3 ∨ run = 4 := by omega
  rcases casesRun with rfl | rfl | rfl | rfl | rfl <;> cases previous <;> rfl

private theorem protectedBits_force_stuff (identifier : BitVec 11) (payload : BitVec 8)
    (badCRC : Bool) : needsStuff false 0 (protectedBits identifier payload badCRC) = true := by
  unfold protectedBits dataFields
  dsimp only
  rw [List.append_assoc ([false] ++ msbBits identifier) formatBits (msbBits payload), List.append_assoc,
    List.append_assoc formatBits]
  exact needsStuff_prefix _ _ _ _ (by decide) (format_forces_stuff _)

private theorem encode_length (identifier : BitVec 11) (payload : BitVec 8) (badStuff badCRC : Bool) :
    (encode identifier payload badStuff badCRC).length = 64 := by
  have bound := stuff_bound (protectedBits identifier payload badCRC) badStuff false 0 (by decide)
  simp only [encode, fixedWindow, paddedTrailer, trailer, protectedBits_length, List.length_append,
    List.length_cons, List.length_nil, List.length_replicate] at *
  omega

@[simp] theorem frameBits_length (identifier : BitVec 11) (payload : BitVec 8) :
    (frameBits identifier payload).length = 64 :=
  encode_length identifier payload false false

@[simp] theorem badStuffBits_length (identifier : BitVec 11) (payload : BitVec 8) :
    (badStuffBits identifier payload).length = 64 :=
  encode_length identifier payload true false

@[simp] theorem badCRCBits_length (identifier : BitVec 11) (payload : BitVec 8) :
    (badCRCBits identifier payload).length = 64 :=
  encode_length identifier payload false true

private theorem encode_sof (identifier : BitVec 11) (payload : BitVec 8) (badStuff badCRC : Bool) :
    (encode identifier payload badStuff badCRC)[0]? = some false := by
  rfl

@[simp] theorem frameBits_sof (identifier : BitVec 11) (payload : BitVec 8) :
    (frameBits identifier payload)[0]? = some false :=
  encode_sof identifier payload false false

@[simp] theorem badStuffBits_sof (identifier : BitVec 11) (payload : BitVec 8) :
    (badStuffBits identifier payload)[0]? = some false :=
  encode_sof identifier payload true false

@[simp] theorem badCRCBits_sof (identifier : BitVec 11) (payload : BitVec 8) :
    (badCRCBits identifier payload)[0]? = some false :=
  encode_sof identifier payload false true

private theorem msbValue_msbBits (value : BitVec n) :
    msbValue n (msbBits value) = value := by
  apply BitVec.eq_of_getLsbD_eq
  intro bit valid
  simp only [msbValue, msbBits, List.reverse_reverse, BitVec.getLsbD_setWidth, valid, decide_true,
    Bool.true_and, BitVec.getLsbD_ofBoolListLE, List.getD_eq_getElem?_getD, List.getElem?_ofFn,
    dif_pos True.intro, Option.getD_some]

private theorem crc_flip_ne (crc : BitVec 15) : crc ^^^ 1 ≠ crc := by
  intro equal
  have low := congrArg (fun v : BitVec 15 => v.getLsbD 0) equal
  rw [BitVec.getLsbD_xor] at low
  change (crc.getLsbD 0 ^^ true) = crc.getLsbD 0 at low
  cases crc.getLsbD 0 <;> simp at low

private theorem decode_protected (identifier : BitVec 11) (payload : BitVec 8) (badCRC : Bool) :
    decodeFields (protectedBits identifier payload badCRC) =
      if badCRC then none else some (identifier, payload) := by
  unfold decodeFields
  dsimp only
  have fields : (protectedBits identifier payload badCRC).take 27 = dataFields identifier payload := by
    unfold protectedBits
    rw [← dataFields_length identifier payload, List.take_append_length]
  rw [fields]
  have identifierBits : ((dataFields identifier payload).drop 1).take 11 = msbBits identifier := by
    change ((msbBits identifier ++ formatBits) ++ msbBits payload).take 11 = _
    rw [List.append_assoc]
    simpa only [msbBits_length] using
      (List.take_append_length (l₁ := msbBits identifier) (l₂ := formatBits ++ msbBits payload))
  have payloadBits : (dataFields identifier payload).drop 19 = msbBits payload := by
    change (([false] ++ msbBits identifier ++ formatBits) ++ msbBits payload).drop 19 = _
    have size : ([false] ++ msbBits identifier ++ formatBits).length = 19 := by
      simp [formatBits]
    rw [← size, List.drop_append_length]
  rw [identifierBits, payloadBits, msbValue_msbBits, msbValue_msbBits]
  let crc := crc15 (dataFields identifier payload)
  have crcBits : (protectedBits identifier payload badCRC).drop 27 =
      msbBits (if badCRC then crc ^^^ 1 else crc) := by
    unfold protectedBits
    rw [← dataFields_length identifier payload, List.drop_append_length]
  rw [crcBits]
  cases badCRC
  · simp [crc]
  · have different : msbBits (crc ^^^ 1) ≠ msbBits crc := by
      intro equal
      have wrong := congrArg (msbValue 15) equal
      simp only [msbValue_msbBits] at wrong
      exact crc_flip_ne crc wrong
    change (if _ ∧ msbBits (crc ^^^ 1) = msbBits crc then _ else _) = _
    rw [if_neg (fun equal => different equal.2)]
    rfl

private theorem paddedTrailer_valid (length : Nat) :
    (paddedTrailer length).take 10 = trailer ∧
      ((paddedTrailer length).drop 10).all id = true := by
  have size : trailer.length = 10 := rfl
  constructor
  · simpa only [paddedTrailer, size] using
      (List.take_append_length (l₁ := trailer)
        (l₂ := List.replicate (64 - (length + trailer.length)) true))
  · unfold paddedTrailer
    rw [← size, List.drop_append_length]
    exact List.all_eq_true.mpr fun _ member => List.eq_of_mem_replicate member

private theorem decode_encoded (identifier : BitVec 11) (payload : BitVec 8) (badCRC : Bool) :
    decodeFrame (encode identifier payload false badCRC) =
      decodeFields (protectedBits identifier payload badCRC) := by
  rw [decodeFrame, if_pos (encode_length ..)]
  unfold encode fixedWindow
  rw [← protectedBits_length identifier payload badCRC, destuff_stuff]
  exact if_pos (paddedTrailer_valid _)

theorem decode_frame (identifier : BitVec 11) (payload : BitVec 8) :
    decodeFrame (frameBits identifier payload) = some (identifier, payload) := by
  rw [frameBits, decode_encoded, decode_protected]
  rfl

theorem decode_badStuff (identifier : BitVec 11) (payload : BitVec 8) :
    decodeFrame (badStuffBits identifier payload) = none := by
  rw [badStuffBits, decodeFrame, if_pos (encode_length ..)]
  unfold encode fixedWindow
  rw [← protectedBits_length identifier payload false,
    destuff_bad _ _ _ _ (protectedBits_force_stuff identifier payload false)]

theorem decode_badCRC (identifier : BitVec 11) (payload : BitVec 8) :
    decodeFrame (badCRCBits identifier payload) = none := by
  rw [badCRCBits, decode_encoded, decode_protected]
  rfl

end Pinwheel.Program.StreamingCAN
