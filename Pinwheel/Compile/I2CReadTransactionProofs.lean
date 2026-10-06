import Pinwheel.Compile.I2CReadTransaction
import Pinwheel.I2C.RegisterReadTransactionProofs
import Pinwheel.Compile.I2CPhases
import Pinwheel.Engine.FetchProofs

set_option maxRecDepth 4096

namespace Pinwheel.Compile.I2CReadTransaction
open Engine.Reactive

def control (s : Pinwheel.I2C.RegisterReadTransaction.State) : Control 255 :=
  match s.phase with
  | .free => .qualifying 0 s.remaining s.waitLeft
  | .startHold => .checked 1 s.remaining
  | .setup slot => .active (bitPC slot 0) s.remaining
  | .rise slot => .waiting (bitPC slot 1) s.waitLeft
  | .high slot => .checked (bitPC slot 2) s.remaining
  | .fall slot => .checked (bitPC slot 3) s.remaining
  | .restartSetup => .active 74 s.remaining
  | .restartRise => .waiting 75 s.waitLeft
  | .restartHigh => .checked 76 s.remaining
  | .restartHold => .checked 77 s.remaining
  | .stopLow nack => .active (if nack then 191 else 186) s.remaining
  | .stopRise nack => .waiting (if nack then 192 else 187) s.waitLeft
  | .stopHigh nack => .checked (if nack then 193 else 188) s.remaining
  | .stopFree nack => .qualifying (if nack then 194 else 189) s.remaining s.waitLeft
  | .nackTerminal => .active 195 0
  | .finished => .stopped .completed
  | .timeout => .stopped .timeout
  | .fault => .stopped .fault

def lift (r : Pinwheel.I2C.RegisterReadTransaction.Request)
    (s : Pinwheel.I2C.RegisterReadTransaction.State) : ReadState :=
  ⟨control s, I2C.encodePins (Pinwheel.I2C.RegisterReadTransaction.pins r s.phase), s.samples⟩

private theorem literals :
    (0 : Fin 256).val = 0 ∧
    (1 : Fin 256).val = 1 ∧
    (2 : Fin 256).val = 2 ∧
    (3 : Fin 256).val = 3 ∧
    (4 : Fin 256).val = 4 ∧
    (5 : Fin 256).val = 5 ∧
    (6 : Fin 256).val = 6 ∧
    (7 : Fin 256).val = 7 ∧
    (8 : Fin 256).val = 8 ∧
    (9 : Fin 256).val = 9 ∧
    (10 : Fin 256).val = 10 ∧
    (11 : Fin 256).val = 11 ∧
    (12 : Fin 256).val = 12 ∧
    (13 : Fin 256).val = 13 ∧
    (14 : Fin 256).val = 14 ∧
    (15 : Fin 256).val = 15 ∧
    (16 : Fin 256).val = 16 ∧
    (17 : Fin 256).val = 17 ∧
    (18 : Fin 256).val = 18 ∧
    (19 : Fin 256).val = 19 ∧
    (20 : Fin 256).val = 20 ∧
    (21 : Fin 256).val = 21 ∧
    (22 : Fin 256).val = 22 ∧
    (23 : Fin 256).val = 23 ∧
    (24 : Fin 256).val = 24 ∧
    (25 : Fin 256).val = 25 ∧
    (26 : Fin 256).val = 26 ∧
    (27 : Fin 256).val = 27 ∧
    (28 : Fin 256).val = 28 ∧
    (29 : Fin 256).val = 29 ∧
    (30 : Fin 256).val = 30 ∧
    (31 : Fin 256).val = 31 ∧
    (32 : Fin 256).val = 32 ∧
    (33 : Fin 256).val = 33 ∧
    (34 : Fin 256).val = 34 ∧
    (35 : Fin 256).val = 35 ∧
    (36 : Fin 256).val = 36 ∧
    (37 : Fin 256).val = 37 ∧
    (38 : Fin 256).val = 38 ∧
    (39 : Fin 256).val = 39 ∧
    (40 : Fin 256).val = 40 ∧
    (41 : Fin 256).val = 41 ∧
    (42 : Fin 256).val = 42 ∧
    (43 : Fin 256).val = 43 ∧
    (44 : Fin 256).val = 44 ∧
    (45 : Fin 256).val = 45 ∧
    (46 : Fin 256).val = 46 ∧
    (47 : Fin 256).val = 47 ∧
    (48 : Fin 256).val = 48 ∧
    (49 : Fin 256).val = 49 ∧
    (50 : Fin 256).val = 50 ∧
    (51 : Fin 256).val = 51 ∧
    (52 : Fin 256).val = 52 ∧
    (53 : Fin 256).val = 53 ∧
    (54 : Fin 256).val = 54 ∧
    (55 : Fin 256).val = 55 ∧
    (56 : Fin 256).val = 56 ∧
    (57 : Fin 256).val = 57 ∧
    (58 : Fin 256).val = 58 ∧
    (59 : Fin 256).val = 59 ∧
    (60 : Fin 256).val = 60 ∧
    (61 : Fin 256).val = 61 ∧
    (62 : Fin 256).val = 62 ∧
    (63 : Fin 256).val = 63 ∧
    (64 : Fin 256).val = 64 ∧
    (65 : Fin 256).val = 65 ∧
    (66 : Fin 256).val = 66 ∧
    (67 : Fin 256).val = 67 ∧
    (68 : Fin 256).val = 68 ∧
    (69 : Fin 256).val = 69 ∧
    (70 : Fin 256).val = 70 ∧
    (71 : Fin 256).val = 71 ∧
    (72 : Fin 256).val = 72 ∧
    (73 : Fin 256).val = 73 ∧
    (74 : Fin 256).val = 74 ∧
    (75 : Fin 256).val = 75 ∧
    (76 : Fin 256).val = 76 ∧
    (77 : Fin 256).val = 77 ∧
    (78 : Fin 256).val = 78 ∧
    (79 : Fin 256).val = 79 ∧
    (80 : Fin 256).val = 80 ∧
    (81 : Fin 256).val = 81 ∧
    (82 : Fin 256).val = 82 ∧
    (83 : Fin 256).val = 83 ∧
    (84 : Fin 256).val = 84 ∧
    (85 : Fin 256).val = 85 ∧
    (86 : Fin 256).val = 86 ∧
    (87 : Fin 256).val = 87 ∧
    (88 : Fin 256).val = 88 ∧
    (89 : Fin 256).val = 89 ∧
    (90 : Fin 256).val = 90 ∧
    (91 : Fin 256).val = 91 ∧
    (92 : Fin 256).val = 92 ∧
    (93 : Fin 256).val = 93 ∧
    (94 : Fin 256).val = 94 ∧
    (95 : Fin 256).val = 95 ∧
    (96 : Fin 256).val = 96 ∧
    (97 : Fin 256).val = 97 ∧
    (98 : Fin 256).val = 98 ∧
    (99 : Fin 256).val = 99 ∧
    (100 : Fin 256).val = 100 ∧
    (101 : Fin 256).val = 101 ∧
    (102 : Fin 256).val = 102 ∧
    (103 : Fin 256).val = 103 ∧
    (104 : Fin 256).val = 104 ∧
    (105 : Fin 256).val = 105 ∧
    (106 : Fin 256).val = 106 ∧
    (107 : Fin 256).val = 107 ∧
    (108 : Fin 256).val = 108 ∧
    (109 : Fin 256).val = 109 ∧
    (110 : Fin 256).val = 110 ∧
    (111 : Fin 256).val = 111 ∧
    (112 : Fin 256).val = 112 ∧
    (113 : Fin 256).val = 113 ∧
    (114 : Fin 256).val = 114 ∧
    (115 : Fin 256).val = 115 ∧
    (116 : Fin 256).val = 116 ∧
    (117 : Fin 256).val = 117 ∧
    (118 : Fin 256).val = 118 ∧
    (119 : Fin 256).val = 119 ∧
    (120 : Fin 256).val = 120 ∧
    (121 : Fin 256).val = 121 ∧
    (122 : Fin 256).val = 122 ∧
    (123 : Fin 256).val = 123 ∧
    (124 : Fin 256).val = 124 ∧
    (125 : Fin 256).val = 125 ∧
    (126 : Fin 256).val = 126 ∧
    (127 : Fin 256).val = 127 ∧
    (128 : Fin 256).val = 128 ∧
    (129 : Fin 256).val = 129 ∧
    (130 : Fin 256).val = 130 ∧
    (131 : Fin 256).val = 131 ∧
    (132 : Fin 256).val = 132 ∧
    (133 : Fin 256).val = 133 ∧
    (134 : Fin 256).val = 134 ∧
    (135 : Fin 256).val = 135 ∧
    (136 : Fin 256).val = 136 ∧
    (137 : Fin 256).val = 137 ∧
    (138 : Fin 256).val = 138 ∧
    (139 : Fin 256).val = 139 ∧
    (140 : Fin 256).val = 140 ∧
    (141 : Fin 256).val = 141 ∧
    (142 : Fin 256).val = 142 ∧
    (143 : Fin 256).val = 143 ∧
    (144 : Fin 256).val = 144 ∧
    (145 : Fin 256).val = 145 ∧
    (146 : Fin 256).val = 146 ∧
    (147 : Fin 256).val = 147 ∧
    (148 : Fin 256).val = 148 ∧
    (149 : Fin 256).val = 149 ∧
    (150 : Fin 256).val = 150 ∧
    (151 : Fin 256).val = 151 ∧
    (152 : Fin 256).val = 152 ∧
    (153 : Fin 256).val = 153 ∧
    (154 : Fin 256).val = 154 ∧
    (155 : Fin 256).val = 155 ∧
    (156 : Fin 256).val = 156 ∧
    (157 : Fin 256).val = 157 ∧
    (158 : Fin 256).val = 158 ∧
    (159 : Fin 256).val = 159 ∧
    (160 : Fin 256).val = 160 ∧
    (161 : Fin 256).val = 161 ∧
    (162 : Fin 256).val = 162 ∧
    (163 : Fin 256).val = 163 ∧
    (164 : Fin 256).val = 164 ∧
    (165 : Fin 256).val = 165 ∧
    (166 : Fin 256).val = 166 ∧
    (167 : Fin 256).val = 167 ∧
    (168 : Fin 256).val = 168 ∧
    (169 : Fin 256).val = 169 ∧
    (170 : Fin 256).val = 170 ∧
    (171 : Fin 256).val = 171 ∧
    (172 : Fin 256).val = 172 ∧
    (173 : Fin 256).val = 173 ∧
    (174 : Fin 256).val = 174 ∧
    (175 : Fin 256).val = 175 ∧
    (176 : Fin 256).val = 176 ∧
    (177 : Fin 256).val = 177 ∧
    (178 : Fin 256).val = 178 ∧
    (179 : Fin 256).val = 179 ∧
    (180 : Fin 256).val = 180 ∧
    (181 : Fin 256).val = 181 ∧
    (182 : Fin 256).val = 182 ∧
    (183 : Fin 256).val = 183 ∧
    (184 : Fin 256).val = 184 ∧
    (185 : Fin 256).val = 185 ∧
    (186 : Fin 256).val = 186 ∧
    (187 : Fin 256).val = 187 ∧
    (188 : Fin 256).val = 188 ∧
    (189 : Fin 256).val = 189 ∧
    (190 : Fin 256).val = 190 ∧
    (191 : Fin 256).val = 191 ∧
    (192 : Fin 256).val = 192 ∧
    (193 : Fin 256).val = 193 ∧
    (194 : Fin 256).val = 194 ∧
    (195 : Fin 256).val = 195 ∧
    (0 : Fin 45).val = 0 ∧
    (1 : Fin 45).val = 1 ∧
    (2 : Fin 45).val = 2 ∧
    (3 : Fin 45).val = 3 ∧
    (4 : Fin 45).val = 4 ∧
    (5 : Fin 45).val = 5 ∧
    (6 : Fin 45).val = 6 ∧
    (7 : Fin 45).val = 7 ∧
    (8 : Fin 45).val = 8 ∧
    (9 : Fin 45).val = 9 ∧
    (10 : Fin 45).val = 10 ∧
    (11 : Fin 45).val = 11 ∧
    (12 : Fin 45).val = 12 ∧
    (13 : Fin 45).val = 13 ∧
    (14 : Fin 45).val = 14 ∧
    (15 : Fin 45).val = 15 ∧
    (16 : Fin 45).val = 16 ∧
    (17 : Fin 45).val = 17 ∧
    (18 : Fin 45).val = 18 ∧
    (19 : Fin 45).val = 19 ∧
    (20 : Fin 45).val = 20 ∧
    (21 : Fin 45).val = 21 ∧
    (22 : Fin 45).val = 22 ∧
    (23 : Fin 45).val = 23 ∧
    (24 : Fin 45).val = 24 ∧
    (25 : Fin 45).val = 25 ∧
    (26 : Fin 45).val = 26 ∧
    (27 : Fin 45).val = 27 ∧
    (28 : Fin 45).val = 28 ∧
    (29 : Fin 45).val = 29 ∧
    (30 : Fin 45).val = 30 ∧
    (31 : Fin 45).val = 31 ∧
    (32 : Fin 45).val = 32 ∧
    (33 : Fin 45).val = 33 ∧
    (34 : Fin 45).val = 34 ∧
    (35 : Fin 45).val = 35 ∧
    (36 : Fin 45).val = 36 ∧
    (37 : Fin 45).val = 37 ∧
    (38 : Fin 45).val = 38 ∧
    (39 : Fin 45).val = 39 ∧
    (40 : Fin 45).val = 40 ∧
    (41 : Fin 45).val = 41 ∧
    (42 : Fin 45).val = 42 ∧
    (43 : Fin 45).val = 43 ∧
    (44 : Fin 45).val = 44 ∧
    (0 : Fin 4).val = 0 ∧
    (1 : Fin 4).val = 1 ∧
    (2 : Fin 4).val = 2 ∧
    (3 : Fin 4).val = 3 ∧
    (0 : Fin 16).val = 0 ∧
    (1 : Fin 16).val = 1 ∧
    (2 : Fin 16).val = 2 ∧
    (3 : Fin 16).val = 3 ∧
    (4 : Fin 16).val = 4 ∧
    (5 : Fin 16).val = 5 ∧
    (6 : Fin 16).val = 6 ∧
    (7 : Fin 16).val = 7 ∧
    (8 : Fin 16).val = 8 ∧
    (9 : Fin 16).val = 9 ∧
    (10 : Fin 16).val = 10 ∧
    (11 : Fin 16).val = 11 ∧
    (12 : Fin 16).val = 12 ∧
    (13 : Fin 16).val = 13 ∧
    (14 : Fin 16).val = 14 ∧
    (15 : Fin 16).val = 15 := by repeat constructor

private theorem remaining_pos (r : Fin 256) : (0 < r.val) ↔ r ≠ 0 := by omega

private theorem slot_cases (slot : Fin 45) : slot = 0 ∨ slot = 1 ∨ slot = 2 ∨ slot = 3 ∨ slot = 4 ∨ slot = 5 ∨ slot = 6 ∨ slot = 7 ∨ slot = 8 ∨ slot = 9 ∨ slot = 10 ∨ slot = 11 ∨ slot = 12 ∨ slot = 13 ∨ slot = 14 ∨ slot = 15 ∨ slot = 16 ∨ slot = 17 ∨ slot = 18 ∨ slot = 19 ∨ slot = 20 ∨ slot = 21 ∨ slot = 22 ∨ slot = 23 ∨ slot = 24 ∨ slot = 25 ∨ slot = 26 ∨ slot = 27 ∨ slot = 28 ∨ slot = 29 ∨ slot = 30 ∨ slot = 31 ∨ slot = 32 ∨ slot = 33 ∨ slot = 34 ∨ slot = 35 ∨ slot = 36 ∨ slot = 37 ∨ slot = 38 ∨ slot = 39 ∨ slot = 40 ∨ slot = 41 ∨ slot = 42 ∨ slot = 43 ∨ slot = 44 := by omega

theorem latch_capture (samples : Vector Bool 16) (slot : Fin 45) (bus : Pinwheel.I2C.Bus) :
    capture samples ((Pinwheel.I2C.RegisterReadTransaction.sampleAt slot).map (⟨1, ·⟩)) (I2C.encodeInputs bus) =
      Pinwheel.I2C.RegisterReadTransaction.latch samples slot bus.sda := by
  cases h : Pinwheel.I2C.RegisterReadTransaction.sampleAt slot <;> simp [capture, Pinwheel.I2C.RegisterReadTransaction.latch, h, I2C.input_data, Engine.capture]
  ext i hi
  simp [Fin.ext_iff, Vector.getElem_set]
  done

attribute [local simp] capture lift control advance program Program.fetch instruction bitInstruction bitPC bitPins fallFinish stopInstruction
  I2C.check_clock I2C.check_both I2C.check_none I2C.input_clock I2C.input_data Condition.ready
  next enter stop dispatch jump
  Pinwheel.I2C.RegisterReadTransaction.step Pinwheel.I2C.RegisterReadTransaction.move Pinwheel.I2C.RegisterReadTransaction.count
  Pinwheel.I2C.RegisterReadTransaction.blocked Pinwheel.I2C.RegisterReadTransaction.finish Pinwheel.I2C.RegisterReadTransaction.timed
  Pinwheel.I2C.RegisterReadTransaction.guarded Pinwheel.I2C.RegisterReadTransaction.pins
  I2C.encodePins Pins.openDrain remaining_pos literals

theorem advance_free (cfg : Pinwheel.I2C.Config) (r : Pinwheel.I2C.RegisterReadTransaction.Request)
    (s : Pinwheel.I2C.RegisterReadTransaction.State) (bus : Pinwheel.I2C.Bus) (hp : s.phase = .free) :
    advance (program cfg r) (lift r s) (I2C.encodeInputs bus) =
      lift r (Pinwheel.I2C.RegisterReadTransaction.step cfg r s bus) := by
  by_cases hr : s.remaining = 0 <;> by_cases hw : s.waitLeft = 0 <;> cases hb : bus.scl <;> cases hd : bus.sda <;> simp_all
  done

theorem advance_startHold (cfg : Pinwheel.I2C.Config) (r : Pinwheel.I2C.RegisterReadTransaction.Request)
    (s : Pinwheel.I2C.RegisterReadTransaction.State) (bus : Pinwheel.I2C.Bus) (hp : s.phase = .startHold) :
    advance (program cfg r) (lift r s) (I2C.encodeInputs bus) =
      lift r (Pinwheel.I2C.RegisterReadTransaction.step cfg r s bus) := by
  by_cases hr : s.remaining = 0 <;> by_cases hw : s.waitLeft = 0 <;> cases hb : bus.scl <;> cases hd : bus.sda <;> simp_all
  done

theorem advance_restartSetup (cfg : Pinwheel.I2C.Config) (r : Pinwheel.I2C.RegisterReadTransaction.Request)
    (s : Pinwheel.I2C.RegisterReadTransaction.State) (bus : Pinwheel.I2C.Bus) (hp : s.phase = .restartSetup) :
    advance (program cfg r) (lift r s) (I2C.encodeInputs bus) =
      lift r (Pinwheel.I2C.RegisterReadTransaction.step cfg r s bus) := by
  by_cases hr : s.remaining = 0 <;> by_cases hw : s.waitLeft = 0 <;> cases hb : bus.scl <;> cases hd : bus.sda <;> simp_all
  done

theorem advance_restartRise (cfg : Pinwheel.I2C.Config) (r : Pinwheel.I2C.RegisterReadTransaction.Request)
    (s : Pinwheel.I2C.RegisterReadTransaction.State) (bus : Pinwheel.I2C.Bus) (hp : s.phase = .restartRise) :
    advance (program cfg r) (lift r s) (I2C.encodeInputs bus) =
      lift r (Pinwheel.I2C.RegisterReadTransaction.step cfg r s bus) := by
  by_cases hr : s.remaining = 0 <;> by_cases hw : s.waitLeft = 0 <;> cases hb : bus.scl <;> cases hd : bus.sda <;> simp_all
  done

theorem advance_restartHigh (cfg : Pinwheel.I2C.Config) (r : Pinwheel.I2C.RegisterReadTransaction.Request)
    (s : Pinwheel.I2C.RegisterReadTransaction.State) (bus : Pinwheel.I2C.Bus) (hp : s.phase = .restartHigh) :
    advance (program cfg r) (lift r s) (I2C.encodeInputs bus) =
      lift r (Pinwheel.I2C.RegisterReadTransaction.step cfg r s bus) := by
  by_cases hr : s.remaining = 0 <;> by_cases hw : s.waitLeft = 0 <;> cases hb : bus.scl <;> cases hd : bus.sda <;> simp_all
  done

theorem advance_restartHold (cfg : Pinwheel.I2C.Config) (r : Pinwheel.I2C.RegisterReadTransaction.Request)
    (s : Pinwheel.I2C.RegisterReadTransaction.State) (bus : Pinwheel.I2C.Bus) (hp : s.phase = .restartHold) :
    advance (program cfg r) (lift r s) (I2C.encodeInputs bus) =
      lift r (Pinwheel.I2C.RegisterReadTransaction.step cfg r s bus) := by
  by_cases hr : s.remaining = 0 <;> by_cases hw : s.waitLeft = 0 <;> cases hb : bus.scl <;> cases hd : bus.sda <;> simp_all
  done

theorem advance_stopLow (cfg : Pinwheel.I2C.Config) (r : Pinwheel.I2C.RegisterReadTransaction.Request)
    (s : Pinwheel.I2C.RegisterReadTransaction.State) (nack : Bool) (bus : Pinwheel.I2C.Bus) (hp : s.phase = .stopLow nack) :
    advance (program cfg r) (lift r s) (I2C.encodeInputs bus) =
      lift r (Pinwheel.I2C.RegisterReadTransaction.step cfg r s bus) := by
  cases nack <;> by_cases hr : s.remaining = 0 <;> by_cases hw : s.waitLeft = 0 <;> cases hb : bus.scl <;> cases hd : bus.sda <;> simp_all
  done

theorem advance_stopRise (cfg : Pinwheel.I2C.Config) (r : Pinwheel.I2C.RegisterReadTransaction.Request)
    (s : Pinwheel.I2C.RegisterReadTransaction.State) (nack : Bool) (bus : Pinwheel.I2C.Bus) (hp : s.phase = .stopRise nack) :
    advance (program cfg r) (lift r s) (I2C.encodeInputs bus) =
      lift r (Pinwheel.I2C.RegisterReadTransaction.step cfg r s bus) := by
  cases nack <;> by_cases hr : s.remaining = 0 <;> by_cases hw : s.waitLeft = 0 <;> cases hb : bus.scl <;> cases hd : bus.sda <;> simp_all
  done

theorem advance_stopHigh (cfg : Pinwheel.I2C.Config) (r : Pinwheel.I2C.RegisterReadTransaction.Request)
    (s : Pinwheel.I2C.RegisterReadTransaction.State) (nack : Bool) (bus : Pinwheel.I2C.Bus) (hp : s.phase = .stopHigh nack) :
    advance (program cfg r) (lift r s) (I2C.encodeInputs bus) =
      lift r (Pinwheel.I2C.RegisterReadTransaction.step cfg r s bus) := by
  cases nack <;> by_cases hr : s.remaining = 0 <;> by_cases hw : s.waitLeft = 0 <;> cases hb : bus.scl <;> cases hd : bus.sda <;> simp_all
  done

theorem advance_stopFree (cfg : Pinwheel.I2C.Config) (r : Pinwheel.I2C.RegisterReadTransaction.Request)
    (s : Pinwheel.I2C.RegisterReadTransaction.State) (nack : Bool) (bus : Pinwheel.I2C.Bus) (hp : s.phase = .stopFree nack) :
    advance (program cfg r) (lift r s) (I2C.encodeInputs bus) =
      lift r (Pinwheel.I2C.RegisterReadTransaction.step cfg r s bus) := by
  cases nack <;> by_cases hr : s.remaining = 0 <;> by_cases hw : s.waitLeft = 0 <;> cases hb : bus.scl <;> cases hd : bus.sda <;> simp_all
  done

theorem advance_nackTerminal (cfg : Pinwheel.I2C.Config) (r : Pinwheel.I2C.RegisterReadTransaction.Request)
    (s : Pinwheel.I2C.RegisterReadTransaction.State) (bus : Pinwheel.I2C.Bus) (hp : s.phase = .nackTerminal) :
    advance (program cfg r) (lift r s) (I2C.encodeInputs bus) =
      lift r (Pinwheel.I2C.RegisterReadTransaction.step cfg r s bus) := by
  by_cases hr : s.remaining = 0 <;> by_cases hw : s.waitLeft = 0 <;> cases hb : bus.scl <;> cases hd : bus.sda <;> simp_all
  done

theorem advance_finished (cfg : Pinwheel.I2C.Config) (r : Pinwheel.I2C.RegisterReadTransaction.Request)
    (s : Pinwheel.I2C.RegisterReadTransaction.State) (bus : Pinwheel.I2C.Bus) (hp : s.phase = .finished) :
    advance (program cfg r) (lift r s) (I2C.encodeInputs bus) =
      lift r (Pinwheel.I2C.RegisterReadTransaction.step cfg r s bus) := by
  by_cases hr : s.remaining = 0 <;> by_cases hw : s.waitLeft = 0 <;> cases hb : bus.scl <;> cases hd : bus.sda <;> simp_all
  done

theorem advance_timeout (cfg : Pinwheel.I2C.Config) (r : Pinwheel.I2C.RegisterReadTransaction.Request)
    (s : Pinwheel.I2C.RegisterReadTransaction.State) (bus : Pinwheel.I2C.Bus) (hp : s.phase = .timeout) :
    advance (program cfg r) (lift r s) (I2C.encodeInputs bus) =
      lift r (Pinwheel.I2C.RegisterReadTransaction.step cfg r s bus) := by
  by_cases hr : s.remaining = 0 <;> by_cases hw : s.waitLeft = 0 <;> cases hb : bus.scl <;> cases hd : bus.sda <;> simp_all
  done

theorem advance_fault (cfg : Pinwheel.I2C.Config) (r : Pinwheel.I2C.RegisterReadTransaction.Request)
    (s : Pinwheel.I2C.RegisterReadTransaction.State) (bus : Pinwheel.I2C.Bus) (hp : s.phase = .fault) :
    advance (program cfg r) (lift r s) (I2C.encodeInputs bus) =
      lift r (Pinwheel.I2C.RegisterReadTransaction.step cfg r s bus) := by
  by_cases hr : s.remaining = 0 <;> by_cases hw : s.waitLeft = 0 <;> cases hb : bus.scl <;> cases hd : bus.sda <;> simp_all
  done

set_option maxHeartbeats 4000000 in
theorem advance_rise (cfg : Pinwheel.I2C.Config) (r : Pinwheel.I2C.RegisterReadTransaction.Request)
    (s : Pinwheel.I2C.RegisterReadTransaction.State) (slot : Fin 45) (bus : Pinwheel.I2C.Bus) (hp : s.phase = .rise slot) :
    advance (program cfg r) (lift r s) (I2C.encodeInputs bus) =
      lift r (Pinwheel.I2C.RegisterReadTransaction.step cfg r s bus) := by
  rcases slot_cases slot with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  all_goals by_cases hr : s.remaining = 0 <;> by_cases hw : s.waitLeft = 0 <;> cases hb : bus.scl <;> simp_all
  done

set_option maxHeartbeats 4000000 in
theorem advance_setup (cfg : Pinwheel.I2C.Config) (r : Pinwheel.I2C.RegisterReadTransaction.Request)
    (s : Pinwheel.I2C.RegisterReadTransaction.State) (slot : Fin 45) (bus : Pinwheel.I2C.Bus) (hp : s.phase = .setup slot) :
    advance (program cfg r) (lift r s) (I2C.encodeInputs bus) =
      lift r (Pinwheel.I2C.RegisterReadTransaction.step cfg r s bus) := by
  rcases slot_cases slot with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  all_goals by_cases hr : s.remaining = 0 <;> by_cases hw : s.waitLeft = 0 <;> cases hb : bus.scl <;> simp_all
  done

set_option maxHeartbeats 4000000 in
theorem advance_high (cfg : Pinwheel.I2C.Config) (r : Pinwheel.I2C.RegisterReadTransaction.Request)
    (s : Pinwheel.I2C.RegisterReadTransaction.State) (slot : Fin 45) (bus : Pinwheel.I2C.Bus) (hp : s.phase = .high slot) :
    advance (program cfg r) (lift r s) (I2C.encodeInputs bus) =
      lift r (Pinwheel.I2C.RegisterReadTransaction.step cfg r s bus) := by
  rcases slot_cases slot with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  all_goals by_cases hr : s.remaining = 0 <;> cases hb : bus.scl <;> simp_all
  all_goals simpa only [hs, capture] using latch_capture s.samples slot bus
  done

set_option maxHeartbeats 4000000 in
theorem advance_fall (cfg : Pinwheel.I2C.Config) (r : Pinwheel.I2C.RegisterReadTransaction.Request)
    (s : Pinwheel.I2C.RegisterReadTransaction.State) (slot : Fin 45) (bus : Pinwheel.I2C.Bus) (hp : s.phase = .fall slot) :
    advance (program cfg r) (lift r s) (I2C.encodeInputs bus) =
      lift r (Pinwheel.I2C.RegisterReadTransaction.step cfg r s bus) := by
  rcases slot_cases slot with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  all_goals cases h0 : s.samples[0] <;> cases h1 : s.samples[1] <;> cases h2 : s.samples[2] <;> by_cases hr : s.remaining = 0 <;> by_cases hc : r.countMinusOne.val = 0 <;> simp_all [Pinwheel.I2C.RegisterReadTransaction.afterFall]
  done

/-- Universal one-edge refinement, including qualified NACK STOP and terminal failure. -/
theorem advance_simulation (cfg : Pinwheel.I2C.Config) (r : Pinwheel.I2C.RegisterReadTransaction.Request)
    (s : Pinwheel.I2C.RegisterReadTransaction.State) (bus : Pinwheel.I2C.Bus) :
    advance (program cfg r) (lift r s) (I2C.encodeInputs bus) =
      lift r (Pinwheel.I2C.RegisterReadTransaction.step cfg r s bus) := by
  cases hp : s.phase with
  | free => exact advance_free cfg r s bus hp
  | startHold => exact advance_startHold cfg r s bus hp
  | setup slot => exact advance_setup cfg r s slot bus hp
  | rise slot => exact advance_rise cfg r s slot bus hp
  | high slot => exact advance_high cfg r s slot bus hp
  | fall slot => exact advance_fall cfg r s slot bus hp
  | restartSetup => exact advance_restartSetup cfg r s bus hp
  | restartRise => exact advance_restartRise cfg r s bus hp
  | restartHigh => exact advance_restartHigh cfg r s bus hp
  | restartHold => exact advance_restartHold cfg r s bus hp
  | stopLow nack => exact advance_stopLow cfg r s nack bus hp
  | stopRise nack => exact advance_stopRise cfg r s nack bus hp
  | stopHigh nack => exact advance_stopHigh cfg r s nack bus hp
  | stopFree nack => exact advance_stopFree cfg r s nack bus hp
  | nackTerminal => exact advance_nackTerminal cfg r s bus hp
  | finished => exact advance_finished cfg r s bus hp
  | timeout => exact advance_timeout cfg r s bus hp
  | fault => exact advance_fault cfg r s bus hp
  done

theorem initial_matches (cfg : Pinwheel.I2C.Config) (r : Pinwheel.I2C.RegisterReadTransaction.Request) (inputs : Inputs) :
    start (program cfg r) inputs = lift r (Pinwheel.I2C.RegisterReadTransaction.initial cfg) := by
  simp [start, enter, program, Program.fetch, instruction, lift, control, Pinwheel.I2C.RegisterReadTransaction.initial, Pinwheel.I2C.RegisterReadTransaction.pins, I2C.encodePins, Pins.openDrain]
  done

theorem run_simulation (cfg : Pinwheel.I2C.Config) (r : Pinwheel.I2C.RegisterReadTransaction.Request)
    (incoming : Nat → Pinwheel.I2C.Bus) (n : Nat) :
    run (program cfg r) (start (program cfg r) (I2C.encodeInputs (incoming 0)))
      (fun t => I2C.encodeInputs (incoming t)) n =
      lift r (Pinwheel.I2C.RegisterReadTransaction.run cfg r (Pinwheel.I2C.RegisterReadTransaction.initial cfg) incoming n) := by
  induction n <;> simp_all only [run, Pinwheel.I2C.RegisterReadTransaction.run, initial_matches, advance_simulation]
  done

theorem result_lift (r : Pinwheel.I2C.RegisterReadTransaction.Request)
    (s : Pinwheel.I2C.RegisterReadTransaction.State) :
    result r (lift r s) = Pinwheel.I2C.RegisterReadTransaction.result r s := by
  cases hp : s.phase <;> simp [result, lift, control, Pinwheel.I2C.RegisterReadTransaction.result, hp]
  done

def execute (cfg : Pinwheel.I2C.Config) (r : Pinwheel.I2C.RegisterReadTransaction.Request)
    (incoming : Nat → Pinwheel.I2C.Bus) (n : Nat) : ReadState :=
  run (program cfg r) (start (program cfg r) (I2C.encodeInputs (incoming 0)))
    (fun t => I2C.encodeInputs (incoming t)) n

theorem waveform_correct (cfg : Pinwheel.I2C.Config) (r : Pinwheel.I2C.RegisterReadTransaction.Request)
    (incoming : Nat → Pinwheel.I2C.Bus) (n : Nat) :
    (execute cfg r incoming n).pins = I2C.encodePins (Pinwheel.I2C.RegisterReadTransaction.pins r
      (Pinwheel.I2C.RegisterReadTransaction.run cfg r (Pinwheel.I2C.RegisterReadTransaction.initial cfg) incoming n).phase) := by
  simp only [execute, run_simulation, lift]
  done

theorem samples_correct (cfg : Pinwheel.I2C.Config) (r : Pinwheel.I2C.RegisterReadTransaction.Request)
    (incoming : Nat → Pinwheel.I2C.Bus) (n : Nat) :
    (execute cfg r incoming n).samples =
      (Pinwheel.I2C.RegisterReadTransaction.run cfg r (Pinwheel.I2C.RegisterReadTransaction.initial cfg) incoming n).samples := by
  simp only [execute, run_simulation, lift]
  done

theorem result_correct (cfg : Pinwheel.I2C.Config) (r : Pinwheel.I2C.RegisterReadTransaction.Request)
    (incoming : Nat → Pinwheel.I2C.Bus) (n : Nat) :
    result r (execute cfg r incoming n) = Pinwheel.I2C.RegisterReadTransaction.result r
      (Pinwheel.I2C.RegisterReadTransaction.run cfg r (Pinwheel.I2C.RegisterReadTransaction.initial cfg) incoming n) := by
  simp only [execute, run_simulation, result_lift]
  done

theorem reset_releases (cfg : Pinwheel.I2C.Config) (r : Pinwheel.I2C.RegisterReadTransaction.Request)
    (s : ReadState) (inputs : Inputs) (startRequested : Bool) :
    (step (program cfg r) s true startRequested inputs).pins = ({} : Pins) := rfl

theorem decoded_run (cfg : Pinwheel.I2C.Config) (r : Pinwheel.I2C.RegisterReadTransaction.Request)
    (incoming : Nat → Pinwheel.I2C.Bus) (n : Nat) :
    Fetch.run (Hardware.Execution.directStore (Hardware.Execution.imageWords (program cfg r))
      (program cfg r).idle (program cfg r).last)
      (start (program cfg r) (I2C.encodeInputs (incoming 0)))
      (fun t => I2C.encodeInputs (incoming t)) n =
      lift r (Pinwheel.I2C.RegisterReadTransaction.run cfg r (Pinwheel.I2C.RegisterReadTransaction.initial cfg) incoming n) :=
  (Fetch.run_eq _ _ (decoded_agrees cfg r) _ _ _).trans (run_simulation cfg r incoming n)

theorem one_byte_upper_false (cfg : Pinwheel.I2C.Config) (r : Pinwheel.I2C.RegisterReadTransaction.Request)
    (incoming : Nat → Pinwheel.I2C.Bus) (n : Nat) (h : r.countMinusOne = 0)
    (index : Fin 16) (hi : 8 ≤ index.val) :
    (execute cfg r incoming n).samples[index.val] = false := by
  simp only [samples_correct, Pinwheel.I2C.RegisterReadTransaction.run_one_byte_upper_false cfg r incoming n h index hi]
  done

end Pinwheel.Compile.I2CReadTransaction
