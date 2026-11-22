import Pinwheel.Hardware.Processor.Examples.ReadySPI

namespace Pinwheel.Hardware.Processor.ReadySPI
open RV32I.Semantics

/-- The three arithmetic instructions after the GPIO load retain exactly its
low nibble. The result holds for every register bank and every status byte,
including arbitrary ready and busy bits in that byte. -/
def receiveNibble (frames collect : Nat) (s : State) : State :=
  let code := program frames collect
  let masked := (step s code[26]!).state
  let shifted := (step masked code[27]!).state
  (step shifted code[28]!).state

theorem receiveNibble_value (frames collect : Nat) (s : State) :
    read (receiveNibble frames collect s).registers 10 =
      (read s.registers 10 <<< 4) ||| (read s.registers 12 &&& 15) := by
  dsimp only [receiveNibble]
  rw [show (program frames collect)[26]! = (0x00f67613 : BitVec 32) by rfl,
      show (program frames collect)[27]! = (0x00451513 : BitVec 32) by rfl,
      show (program frames collect)[28]! = (0x00c56533 : BitVec 32) by rfl]
  rfl

/-- The collecting instruction in the ROM copies the reconstructed response
word to the architectural result register without assuming its value. -/
theorem collect_value (frames collect : Nat) (s : State) :
    read (step s (program frames collect)[33]!).state.registers 25 = read s.registers 10 := by
  rw [show (program frames collect)[33]! = (0x00050c93 : BitVec 32) by rfl]
  change read s.registers 10 + 0 = _
  simp

/-- One completed GPIO load followed by the mask, shift and OR instructions. -/
def receiveSample (frames collect : Nat) (s : State) (gpio : BitVec 32) : State :=
  receiveNibble frames collect (writeNext s 12 gpio)

private theorem sample_value (frames collect : Nat) (s : State) (gpio : BitVec 32) :
    read (receiveSample frames collect s gpio).registers 10 =
      (read s.registers 10 <<< 4) ||| (gpio &&& 15) := by
  rw [receiveSample, receiveNibble_value]
  rfl

private theorem receive_fold (frames collect : Nat) (samples : List (BitVec 32)) (s : State) :
    read (samples.foldl (receiveSample frames collect) s).registers 10 =
      samples.foldl (fun (acc raw : BitVec 32) => (acc <<< 4) ||| (raw &&& 15)) (read s.registers 10) := by
  induction samples generalizing s with
  | nil => rfl
  | cons head tail ih =>
    simp only [List.foldl_cons, ih, sample_value]

/-- Eight high-to-low data nibbles overwrite all earlier header and status
bits. The software's data path recovers every possible 32-bit reply word. -/
theorem receive_word (frames collect : Nat) (s : State) (word : BitVec 32) :
    let samples := [28,24,20,16,12,8,4,0].map (fun k : Nat => word >>> k)
    read (samples.foldl (receiveSample frames collect) s).registers 10 = word := by
  dsimp only
  rw [receive_fold]
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro i hi
  simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil]
  -- Each output bit comes from exactly one of the eight samples.
  match i with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15
    | 16 | 17 | 18 | 19 | 20 | 21 | 22 | 23 | 24 | 25 | 26 | 27 | 28 | 29 | 30 | 31 =>
    simp +decide
  | k+32 => omega

end Pinwheel.Hardware.Processor.ReadySPI
