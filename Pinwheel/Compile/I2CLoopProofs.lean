import Pinwheel.Compile.I2CLoop
import Pinwheel.Engine.FetchProofs

namespace Pinwheel.Compile.I2CLoop
open Engine.Reactive.Counted

/-- The write-address byte appends the zero direction bit. -/
theorem address_bit (address : Fin 128) (bit : Fin 8) :
    (BitVec.ofNat 8 (address.val * 2)).getLsbD (7 - bit.val) =
      (if bit.val < 7 then address.val.testBit (6 - bit.val) else false) := by
  simp only [BitVec.getLsbD_ofNat, show (address.val * 2).testBit (7 - bit.val) =
    (decide (1 ≤ 7 - bit.val) && address.val.testBit (7 - bit.val - 1)) from
      Nat.testBit_mul_two_pow address.val (7 - bit.val) 1]
  by_cases h : bit.val < 7 <;> simp [h, show 7 - bit.val < 8 by omega,
    show (1 ≤ 7 - bit.val) ↔ bit.val < 7 by omega, show 7 - bit.val - 1 = 6 - bit.val by omega]
  done

private theorem address_literals (a : Fin 128) :
    (BitVec.ofNat 8 (a.val * 2)).getLsbD 7 = a.val.testBit 6 ∧ (BitVec.ofNat 8 (a.val * 2)).getLsbD 6 = a.val.testBit 5 ∧ (BitVec.ofNat 8 (a.val * 2)).getLsbD 5 = a.val.testBit 4 ∧ (BitVec.ofNat 8 (a.val * 2)).getLsbD 4 = a.val.testBit 3 ∧ (BitVec.ofNat 8 (a.val * 2)).getLsbD 3 = a.val.testBit 2 ∧ (BitVec.ofNat 8 (a.val * 2)).getLsbD 2 = a.val.testBit 1 ∧ (BitVec.ofNat 8 (a.val * 2)).getLsbD 1 = a.val.testBit 0 ∧ (BitVec.ofNat 8 (a.val * 2)).getLsbD 0 = false := by
  exact ⟨address_bit a 0, address_bit a 1, address_bit a 2, address_bit a 3, address_bit a 4, address_bit a 5, address_bit a 6, address_bit a 7⟩

private theorem pc_cases (pc : Fin 128) : pc = 0 ∨ pc = 1 ∨ pc = 2 ∨ pc = 3 ∨ pc = 4 ∨ pc = 5 ∨ pc = 6 ∨ pc = 7 ∨ pc = 8 ∨ pc = 9 ∨ pc = 10 ∨ pc = 11 ∨ pc = 12 ∨ pc = 13 ∨ pc = 14 ∨ pc = 15 ∨ pc = 16 ∨ pc = 17 ∨ pc = 18 ∨ pc = 19 ∨ pc = 20 ∨ pc = 21 ∨ pc = 22 ∨ pc = 23 ∨ pc = 24 ∨ pc = 25 ∨ pc = 26 ∨ pc = 27 ∨ pc = 28 ∨ pc = 29 ∨ pc = 30 ∨ pc = 31 ∨ pc = 32 ∨ pc = 33 ∨ pc = 34 ∨ pc = 35 ∨ pc = 36 ∨ pc = 37 ∨ pc = 38 ∨ pc = 39 ∨ pc = 40 ∨ pc = 41 ∨ pc = 42 ∨ pc = 43 ∨ pc = 44 ∨ pc = 45 ∨ pc = 46 ∨ pc = 47 ∨ pc = 48 ∨ pc = 49 ∨ pc = 50 ∨ pc = 51 ∨ pc = 52 ∨ pc = 53 ∨ pc = 54 ∨ pc = 55 ∨ pc = 56 ∨ pc = 57 ∨ pc = 58 ∨ pc = 59 ∨ pc = 60 ∨ pc = 61 ∨ pc = 62 ∨ pc = 63 ∨ pc = 64 ∨ pc = 65 ∨ pc = 66 ∨ pc = 67 ∨ pc = 68 ∨ pc = 69 ∨ pc = 70 ∨ pc = 71 ∨ pc = 72 ∨ pc = 73 ∨ pc = 74 ∨ pc = 75 ∨ pc = 76 ∨ pc = 77 ∨ pc = 78 ∨ pc = 79 ∨ pc = 80 ∨ pc = 81 ∨ pc = 82 ∨ pc = 83 ∨ pc = 84 ∨ pc = 85 ∨ pc = 86 ∨ pc = 87 ∨ pc = 88 ∨ pc = 89 ∨ pc = 90 ∨ pc = 91 ∨ pc = 92 ∨ pc = 93 ∨ pc = 94 ∨ pc = 95 ∨ pc = 96 ∨ pc = 97 ∨ pc = 98 ∨ pc = 99 ∨ pc = 100 ∨ pc = 101 ∨ pc = 102 ∨ pc = 103 ∨ pc = 104 ∨ pc = 105 ∨ pc = 106 ∨ pc = 107 ∨ pc = 108 ∨ pc = 109 ∨ pc = 110 ∨ pc = 111 ∨ pc = 112 ∨ pc = 113 ∨ pc = 114 ∨ pc = 115 ∨ pc = 116 ∨ pc = 117 ∨ pc = 118 ∨ pc = 119 ∨ pc = 120 ∨ pc = 121 ∨ pc = 122 ∨ pc = 123 ∨ pc = 124 ∨ pc = 125 ∨ pc = 126 ∨ pc = 127 := by omega

private theorem literals :
  (0 : Fin 128).val = 0 ∧ (1 : Fin 128).val = 1 ∧ (2 : Fin 128).val = 2 ∧ (3 : Fin 128).val = 3 ∧ (4 : Fin 128).val = 4 ∧ (5 : Fin 128).val = 5 ∧ (6 : Fin 128).val = 6 ∧ (7 : Fin 128).val = 7 ∧ (8 : Fin 128).val = 8 ∧ (9 : Fin 128).val = 9 ∧ (10 : Fin 128).val = 10 ∧ (11 : Fin 128).val = 11 ∧ (12 : Fin 128).val = 12 ∧ (13 : Fin 128).val = 13 ∧ (14 : Fin 128).val = 14 ∧ (15 : Fin 128).val = 15 ∧ (16 : Fin 128).val = 16 ∧ (17 : Fin 128).val = 17 ∧ (18 : Fin 128).val = 18 ∧ (19 : Fin 128).val = 19 ∧ (20 : Fin 128).val = 20 ∧ (21 : Fin 128).val = 21 ∧ (22 : Fin 128).val = 22 ∧ (23 : Fin 128).val = 23 ∧ (24 : Fin 128).val = 24 ∧ (25 : Fin 128).val = 25 ∧ (26 : Fin 128).val = 26 ∧ (27 : Fin 128).val = 27 ∧ (28 : Fin 128).val = 28 ∧ (29 : Fin 128).val = 29 ∧ (30 : Fin 128).val = 30 ∧ (31 : Fin 128).val = 31 ∧ (32 : Fin 128).val = 32 ∧ (33 : Fin 128).val = 33 ∧ (34 : Fin 128).val = 34 ∧ (35 : Fin 128).val = 35 ∧ (36 : Fin 128).val = 36 ∧ (37 : Fin 128).val = 37 ∧ (38 : Fin 128).val = 38 ∧ (39 : Fin 128).val = 39 ∧ (40 : Fin 128).val = 40 ∧ (41 : Fin 128).val = 41 ∧ (42 : Fin 128).val = 42 ∧ (43 : Fin 128).val = 43 ∧ (44 : Fin 128).val = 44 ∧ (45 : Fin 128).val = 45 ∧ (46 : Fin 128).val = 46 ∧ (47 : Fin 128).val = 47 ∧ (48 : Fin 128).val = 48 ∧ (49 : Fin 128).val = 49 ∧ (50 : Fin 128).val = 50 ∧ (51 : Fin 128).val = 51 ∧ (52 : Fin 128).val = 52 ∧ (53 : Fin 128).val = 53 ∧ (54 : Fin 128).val = 54 ∧ (55 : Fin 128).val = 55 ∧ (56 : Fin 128).val = 56 ∧ (57 : Fin 128).val = 57 ∧ (58 : Fin 128).val = 58 ∧ (59 : Fin 128).val = 59 ∧ (60 : Fin 128).val = 60 ∧ (61 : Fin 128).val = 61 ∧ (62 : Fin 128).val = 62 ∧ (63 : Fin 128).val = 63 ∧ (64 : Fin 128).val = 64 ∧ (65 : Fin 128).val = 65 ∧ (66 : Fin 128).val = 66 ∧ (67 : Fin 128).val = 67 ∧ (68 : Fin 128).val = 68 ∧ (69 : Fin 128).val = 69 ∧ (70 : Fin 128).val = 70 ∧ (71 : Fin 128).val = 71 ∧ (72 : Fin 128).val = 72 ∧ (73 : Fin 128).val = 73 ∧ (74 : Fin 128).val = 74 ∧ (75 : Fin 128).val = 75 ∧ (76 : Fin 128).val = 76 ∧ (77 : Fin 128).val = 77 ∧ (78 : Fin 128).val = 78 ∧ (79 : Fin 128).val = 79 ∧ (80 : Fin 128).val = 80 ∧ (81 : Fin 128).val = 81 ∧ (82 : Fin 128).val = 82 ∧ (83 : Fin 128).val = 83 ∧ (84 : Fin 128).val = 84 ∧ (85 : Fin 128).val = 85 ∧ (86 : Fin 128).val = 86 ∧ (87 : Fin 128).val = 87 ∧ (88 : Fin 128).val = 88 ∧ (89 : Fin 128).val = 89 ∧ (90 : Fin 128).val = 90 ∧ (91 : Fin 128).val = 91 ∧ (92 : Fin 128).val = 92 ∧ (93 : Fin 128).val = 93 ∧ (94 : Fin 128).val = 94 ∧ (95 : Fin 128).val = 95 ∧ (96 : Fin 128).val = 96 ∧ (97 : Fin 128).val = 97 ∧ (98 : Fin 128).val = 98 ∧ (99 : Fin 128).val = 99 ∧ (100 : Fin 128).val = 100 ∧ (101 : Fin 128).val = 101 ∧ (102 : Fin 128).val = 102 ∧ (103 : Fin 128).val = 103 ∧ (104 : Fin 128).val = 104 ∧ (105 : Fin 128).val = 105 ∧ (106 : Fin 128).val = 106 ∧ (107 : Fin 128).val = 107 ∧ (108 : Fin 128).val = 108 ∧ (109 : Fin 128).val = 109 ∧ (110 : Fin 128).val = 110 ∧ (111 : Fin 128).val = 111 ∧ (112 : Fin 128).val = 112 ∧ (113 : Fin 128).val = 113 ∧ (114 : Fin 128).val = 114 ∧ (115 : Fin 128).val = 115 ∧ (116 : Fin 128).val = 116 ∧ (117 : Fin 128).val = 117 ∧ (118 : Fin 128).val = 118 ∧ (119 : Fin 128).val = 119 ∧ (120 : Fin 128).val = 120 ∧ (121 : Fin 128).val = 121 ∧ (122 : Fin 128).val = 122 ∧ (123 : Fin 128).val = 123 ∧ (124 : Fin 128).val = 124 ∧ (125 : Fin 128).val = 125 ∧ (126 : Fin 128).val = 126 ∧ (127 : Fin 128).val = 127 ∧ (0 : Fin 8).val = 0 ∧ (1 : Fin 8).val = 1 ∧ (2 : Fin 8).val = 2 ∧ (3 : Fin 8).val = 3 ∧ (4 : Fin 8).val = 4 ∧ (5 : Fin 8).val = 5 ∧ (6 : Fin 8).val = 6 ∧ (7 : Fin 8).val = 7 ∧ (0 : Fin 2).val = 0 ∧ (1 : Fin 2).val = 1 ∧ (0 : Fin 3).val = 0 ∧ (1 : Fin 3).val = 1 ∧ (2 : Fin 3).val = 2 := by repeat constructor

set_option maxHeartbeats 8000000 in
theorem fetch_eq (cfg : Pinwheel.I2C.Config) (r : Pinwheel.I2C.Request) (pc : Fin 128) :
    (program cfg r).fetch pc = some ((I2C.program cfg r).fetch pc) := by
  rcases pc_cases pc with hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp
  all_goals simp [hp, program, Program.fetch, code, chain, bitBody, ackBody, serialPins,
    Code.locate, Code.span, Template.eval, PinExpr.eval, Index.eval, Sample.eval,
    Successor.eval, Transfer.eval, Target.eval, I2C.program, Engine.Reactive.Program.fetch,
    I2C.instruction, I2C.bitInstruction, I2C.bitPins, I2C.ackCapture, I2C.fallFinish,
    I2C.encodePins, Engine.Reactive.Pins.openDrain, Pinwheel.I2C.releaseData, literals]
  all_goals simp only [← BitVec.getLsbD_eq_getElem, address_literals]
  all_goals split <;> simp_all
  done

end Pinwheel.Compile.I2CLoop
