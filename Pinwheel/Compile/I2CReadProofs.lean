import Pinwheel.Compile.I2CRead
import Pinwheel.Compile.I2CPhases
import Pinwheel.Engine.FetchProofs

set_option maxRecDepth 4096

namespace Pinwheel.Compile.I2CRead
open Engine.Reactive

def control (s : Pinwheel.I2C.RegisterRead.State) : Control 255 :=
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
  | .stopLow => .active 150 s.remaining
  | .stopRise => .waiting 151 s.waitLeft
  | .stopHigh => .checked 152 s.remaining
  | .stopFree => .qualifying 153 s.remaining s.waitLeft
  | .finished => .stopped .completed
  | .timeout => .stopped .timeout
  | .fault => .stopped .fault

def lift (r : Pinwheel.I2C.RegisterRead.Request) (s : Pinwheel.I2C.RegisterRead.State) : ReadState :=
  ⟨control s, I2C.encodePins (Pinwheel.I2C.RegisterRead.pins r s.phase), s.samples⟩

theorem latch_capture (samples : Vector Bool 16) (slot : Fin 36) (bus : Pinwheel.I2C.Bus) :
    capture samples ((Pinwheel.I2C.RegisterRead.sampleAt slot).map (⟨1, ·⟩)) (I2C.encodeInputs bus) =
      Pinwheel.I2C.RegisterRead.latch samples slot bus.sda := by
  cases h : Pinwheel.I2C.RegisterRead.sampleAt slot <;> simp [capture, Pinwheel.I2C.RegisterRead.latch, h, I2C.input_data, Engine.capture]
  ext i hi
  simp [Fin.ext_iff, Vector.getElem_set]
  done

private theorem remaining_pos (r : Fin 256) : (0 < r.val) ↔ r ≠ 0 := by omega

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
    (0 : Fin 36).val = 0 ∧
    (1 : Fin 36).val = 1 ∧
    (2 : Fin 36).val = 2 ∧
    (3 : Fin 36).val = 3 ∧
    (4 : Fin 36).val = 4 ∧
    (5 : Fin 36).val = 5 ∧
    (6 : Fin 36).val = 6 ∧
    (7 : Fin 36).val = 7 ∧
    (8 : Fin 36).val = 8 ∧
    (9 : Fin 36).val = 9 ∧
    (10 : Fin 36).val = 10 ∧
    (11 : Fin 36).val = 11 ∧
    (12 : Fin 36).val = 12 ∧
    (13 : Fin 36).val = 13 ∧
    (14 : Fin 36).val = 14 ∧
    (15 : Fin 36).val = 15 ∧
    (16 : Fin 36).val = 16 ∧
    (17 : Fin 36).val = 17 ∧
    (18 : Fin 36).val = 18 ∧
    (19 : Fin 36).val = 19 ∧
    (20 : Fin 36).val = 20 ∧
    (21 : Fin 36).val = 21 ∧
    (22 : Fin 36).val = 22 ∧
    (23 : Fin 36).val = 23 ∧
    (24 : Fin 36).val = 24 ∧
    (25 : Fin 36).val = 25 ∧
    (26 : Fin 36).val = 26 ∧
    (27 : Fin 36).val = 27 ∧
    (28 : Fin 36).val = 28 ∧
    (29 : Fin 36).val = 29 ∧
    (30 : Fin 36).val = 30 ∧
    (31 : Fin 36).val = 31 ∧
    (32 : Fin 36).val = 32 ∧
    (33 : Fin 36).val = 33 ∧
    (34 : Fin 36).val = 34 ∧
    (35 : Fin 36).val = 35 ∧
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

attribute [local simp] capture lift control advance program Program.fetch instruction bitInstruction bitPC bitPins fallFinish
  I2C.check_clock I2C.check_both I2C.check_none I2C.input_clock I2C.input_data Condition.ready
  next enter stop dispatch jump
  Pinwheel.I2C.RegisterRead.step Pinwheel.I2C.RegisterRead.move Pinwheel.I2C.RegisterRead.count
  Pinwheel.I2C.RegisterRead.blocked Pinwheel.I2C.RegisterRead.finish Pinwheel.I2C.RegisterRead.timed
  Pinwheel.I2C.RegisterRead.guarded Pinwheel.I2C.RegisterRead.pins
  I2C.encodePins Pins.openDrain remaining_pos literals

theorem advance_free (cfg : Pinwheel.I2C.Config) (r : Pinwheel.I2C.RegisterRead.Request)
    (s : Pinwheel.I2C.RegisterRead.State) (bus : Pinwheel.I2C.Bus) (hp : s.phase = .free) :
    advance (program cfg r) (lift r s) (I2C.encodeInputs bus) =
      lift r (Pinwheel.I2C.RegisterRead.step cfg s bus) := by
  by_cases hr : s.remaining = 0 <;> by_cases hw : s.waitLeft = 0 <;>
    cases hb : bus.scl <;> cases hd : bus.sda <;> simp_all
  done

theorem advance_startHold (cfg : Pinwheel.I2C.Config) (r : Pinwheel.I2C.RegisterRead.Request)
    (s : Pinwheel.I2C.RegisterRead.State) (bus : Pinwheel.I2C.Bus) (hp : s.phase = .startHold) :
    advance (program cfg r) (lift r s) (I2C.encodeInputs bus) =
      lift r (Pinwheel.I2C.RegisterRead.step cfg s bus) := by
  by_cases hr : s.remaining = 0 <;> by_cases hw : s.waitLeft = 0 <;>
    cases hb : bus.scl <;> cases hd : bus.sda <;> simp_all
  done

theorem advance_restartSetup (cfg : Pinwheel.I2C.Config) (r : Pinwheel.I2C.RegisterRead.Request)
    (s : Pinwheel.I2C.RegisterRead.State) (bus : Pinwheel.I2C.Bus) (hp : s.phase = .restartSetup) :
    advance (program cfg r) (lift r s) (I2C.encodeInputs bus) =
      lift r (Pinwheel.I2C.RegisterRead.step cfg s bus) := by
  by_cases hr : s.remaining = 0 <;> by_cases hw : s.waitLeft = 0 <;>
    cases hb : bus.scl <;> cases hd : bus.sda <;> simp_all
  done

theorem advance_restartRise (cfg : Pinwheel.I2C.Config) (r : Pinwheel.I2C.RegisterRead.Request)
    (s : Pinwheel.I2C.RegisterRead.State) (bus : Pinwheel.I2C.Bus) (hp : s.phase = .restartRise) :
    advance (program cfg r) (lift r s) (I2C.encodeInputs bus) =
      lift r (Pinwheel.I2C.RegisterRead.step cfg s bus) := by
  by_cases hr : s.remaining = 0 <;> by_cases hw : s.waitLeft = 0 <;>
    cases hb : bus.scl <;> cases hd : bus.sda <;> simp_all
  done

theorem advance_restartHigh (cfg : Pinwheel.I2C.Config) (r : Pinwheel.I2C.RegisterRead.Request)
    (s : Pinwheel.I2C.RegisterRead.State) (bus : Pinwheel.I2C.Bus) (hp : s.phase = .restartHigh) :
    advance (program cfg r) (lift r s) (I2C.encodeInputs bus) =
      lift r (Pinwheel.I2C.RegisterRead.step cfg s bus) := by
  by_cases hr : s.remaining = 0 <;> by_cases hw : s.waitLeft = 0 <;>
    cases hb : bus.scl <;> cases hd : bus.sda <;> simp_all
  done

theorem advance_restartHold (cfg : Pinwheel.I2C.Config) (r : Pinwheel.I2C.RegisterRead.Request)
    (s : Pinwheel.I2C.RegisterRead.State) (bus : Pinwheel.I2C.Bus) (hp : s.phase = .restartHold) :
    advance (program cfg r) (lift r s) (I2C.encodeInputs bus) =
      lift r (Pinwheel.I2C.RegisterRead.step cfg s bus) := by
  by_cases hr : s.remaining = 0 <;> by_cases hw : s.waitLeft = 0 <;>
    cases hb : bus.scl <;> cases hd : bus.sda <;> simp_all
  done

theorem advance_stopLow (cfg : Pinwheel.I2C.Config) (r : Pinwheel.I2C.RegisterRead.Request)
    (s : Pinwheel.I2C.RegisterRead.State) (bus : Pinwheel.I2C.Bus) (hp : s.phase = .stopLow) :
    advance (program cfg r) (lift r s) (I2C.encodeInputs bus) =
      lift r (Pinwheel.I2C.RegisterRead.step cfg s bus) := by
  by_cases hr : s.remaining = 0 <;> by_cases hw : s.waitLeft = 0 <;>
    cases hb : bus.scl <;> cases hd : bus.sda <;> simp_all
  done

theorem advance_stopRise (cfg : Pinwheel.I2C.Config) (r : Pinwheel.I2C.RegisterRead.Request)
    (s : Pinwheel.I2C.RegisterRead.State) (bus : Pinwheel.I2C.Bus) (hp : s.phase = .stopRise) :
    advance (program cfg r) (lift r s) (I2C.encodeInputs bus) =
      lift r (Pinwheel.I2C.RegisterRead.step cfg s bus) := by
  by_cases hr : s.remaining = 0 <;> by_cases hw : s.waitLeft = 0 <;>
    cases hb : bus.scl <;> cases hd : bus.sda <;> simp_all
  done

theorem advance_stopHigh (cfg : Pinwheel.I2C.Config) (r : Pinwheel.I2C.RegisterRead.Request)
    (s : Pinwheel.I2C.RegisterRead.State) (bus : Pinwheel.I2C.Bus) (hp : s.phase = .stopHigh) :
    advance (program cfg r) (lift r s) (I2C.encodeInputs bus) =
      lift r (Pinwheel.I2C.RegisterRead.step cfg s bus) := by
  by_cases hr : s.remaining = 0 <;> by_cases hw : s.waitLeft = 0 <;>
    cases hb : bus.scl <;> cases hd : bus.sda <;> simp_all
  done

theorem advance_stopFree (cfg : Pinwheel.I2C.Config) (r : Pinwheel.I2C.RegisterRead.Request)
    (s : Pinwheel.I2C.RegisterRead.State) (bus : Pinwheel.I2C.Bus) (hp : s.phase = .stopFree) :
    advance (program cfg r) (lift r s) (I2C.encodeInputs bus) =
      lift r (Pinwheel.I2C.RegisterRead.step cfg s bus) := by
  by_cases hr : s.remaining = 0 <;> by_cases hw : s.waitLeft = 0 <;>
    cases hb : bus.scl <;> cases hd : bus.sda <;> simp_all
  done

theorem advance_finished (cfg : Pinwheel.I2C.Config) (r : Pinwheel.I2C.RegisterRead.Request)
    (s : Pinwheel.I2C.RegisterRead.State) (bus : Pinwheel.I2C.Bus) (hp : s.phase = .finished) :
    advance (program cfg r) (lift r s) (I2C.encodeInputs bus) =
      lift r (Pinwheel.I2C.RegisterRead.step cfg s bus) := by
  by_cases hr : s.remaining = 0 <;> by_cases hw : s.waitLeft = 0 <;>
    cases hb : bus.scl <;> cases hd : bus.sda <;> simp_all
  done

theorem advance_timeout (cfg : Pinwheel.I2C.Config) (r : Pinwheel.I2C.RegisterRead.Request)
    (s : Pinwheel.I2C.RegisterRead.State) (bus : Pinwheel.I2C.Bus) (hp : s.phase = .timeout) :
    advance (program cfg r) (lift r s) (I2C.encodeInputs bus) =
      lift r (Pinwheel.I2C.RegisterRead.step cfg s bus) := by
  by_cases hr : s.remaining = 0 <;> by_cases hw : s.waitLeft = 0 <;>
    cases hb : bus.scl <;> cases hd : bus.sda <;> simp_all
  done

theorem advance_fault (cfg : Pinwheel.I2C.Config) (r : Pinwheel.I2C.RegisterRead.Request)
    (s : Pinwheel.I2C.RegisterRead.State) (bus : Pinwheel.I2C.Bus) (hp : s.phase = .fault) :
    advance (program cfg r) (lift r s) (I2C.encodeInputs bus) =
      lift r (Pinwheel.I2C.RegisterRead.step cfg s bus) := by
  by_cases hr : s.remaining = 0 <;> by_cases hw : s.waitLeft = 0 <;>
    cases hb : bus.scl <;> cases hd : bus.sda <;> simp_all
  done

private theorem slot_cases (slot : Fin 36) : slot = 0 ∨ slot = 1 ∨ slot = 2 ∨ slot = 3 ∨ slot = 4 ∨ slot = 5 ∨ slot = 6 ∨ slot = 7 ∨ slot = 8 ∨ slot = 9 ∨ slot = 10 ∨ slot = 11 ∨ slot = 12 ∨ slot = 13 ∨ slot = 14 ∨ slot = 15 ∨ slot = 16 ∨ slot = 17 ∨ slot = 18 ∨ slot = 19 ∨ slot = 20 ∨ slot = 21 ∨ slot = 22 ∨ slot = 23 ∨ slot = 24 ∨ slot = 25 ∨ slot = 26 ∨ slot = 27 ∨ slot = 28 ∨ slot = 29 ∨ slot = 30 ∨ slot = 31 ∨ slot = 32 ∨ slot = 33 ∨ slot = 34 ∨ slot = 35 := by omega

set_option maxHeartbeats 3000000 in
theorem advance_high (cfg : Pinwheel.I2C.Config) (r : Pinwheel.I2C.RegisterRead.Request)
    (s : Pinwheel.I2C.RegisterRead.State) (slot : Fin 36) (bus : Pinwheel.I2C.Bus) (hp : s.phase = .high slot) :
    advance (program cfg r) (lift r s) (I2C.encodeInputs bus) =
      lift r (Pinwheel.I2C.RegisterRead.step cfg s bus) := by
  rcases slot_cases slot with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  all_goals by_cases hr : s.remaining = 0 <;> cases hb : bus.scl <;> simp_all
  all_goals simpa only [hs, capture] using latch_capture s.samples slot bus
  done

set_option maxHeartbeats 3000000 in
theorem advance_setup (cfg : Pinwheel.I2C.Config) (r : Pinwheel.I2C.RegisterRead.Request)
    (s : Pinwheel.I2C.RegisterRead.State) (slot : Fin 36) (bus : Pinwheel.I2C.Bus) (hp : s.phase = .setup slot) :
    advance (program cfg r) (lift r s) (I2C.encodeInputs bus) =
      lift r (Pinwheel.I2C.RegisterRead.step cfg s bus) := by
  rcases slot_cases slot with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  all_goals by_cases hr : s.remaining = 0 <;> by_cases hw : s.waitLeft = 0 <;> cases hb : bus.scl <;> simp_all
  done

set_option maxHeartbeats 3000000 in
theorem advance_rise (cfg : Pinwheel.I2C.Config) (r : Pinwheel.I2C.RegisterRead.Request)
    (s : Pinwheel.I2C.RegisterRead.State) (slot : Fin 36) (bus : Pinwheel.I2C.Bus) (hp : s.phase = .rise slot) :
    advance (program cfg r) (lift r s) (I2C.encodeInputs bus) =
      lift r (Pinwheel.I2C.RegisterRead.step cfg s bus) := by
  rcases slot_cases slot with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  all_goals by_cases hr : s.remaining = 0 <;> by_cases hw : s.waitLeft = 0 <;> cases hb : bus.scl <;> simp_all
  done

set_option maxHeartbeats 3000000 in
theorem advance_fall (cfg : Pinwheel.I2C.Config) (r : Pinwheel.I2C.RegisterRead.Request)
    (s : Pinwheel.I2C.RegisterRead.State) (slot : Fin 36) (bus : Pinwheel.I2C.Bus) (hp : s.phase = .fall slot) :
    advance (program cfg r) (lift r s) (I2C.encodeInputs bus) =
      lift r (Pinwheel.I2C.RegisterRead.step cfg s bus) := by
  rcases slot_cases slot with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  all_goals cases h8 : s.samples[8] <;> cases h9 : s.samples[9] <;> cases h10 : s.samples[10] <;> by_cases hr : s.remaining = 0 <;> simp_all [Pinwheel.I2C.RegisterRead.afterFall]
  done

/-- All reference states and sampled buses, including aborts; no target-liveness assumption. -/
theorem advance_simulation (cfg : Pinwheel.I2C.Config) (r : Pinwheel.I2C.RegisterRead.Request)
    (s : Pinwheel.I2C.RegisterRead.State) (bus : Pinwheel.I2C.Bus) :
    advance (program cfg r) (lift r s) (I2C.encodeInputs bus) =
      lift r (Pinwheel.I2C.RegisterRead.step cfg s bus) := by
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
  | stopLow => exact advance_stopLow cfg r s bus hp
  | stopRise => exact advance_stopRise cfg r s bus hp
  | stopHigh => exact advance_stopHigh cfg r s bus hp
  | stopFree => exact advance_stopFree cfg r s bus hp
  | finished => exact advance_finished cfg r s bus hp
  | timeout => exact advance_timeout cfg r s bus hp
  | fault => exact advance_fault cfg r s bus hp
  done

theorem initial_matches (cfg : Pinwheel.I2C.Config) (r : Pinwheel.I2C.RegisterRead.Request) (inputs : Inputs) :
    start (program cfg r) inputs = lift r (Pinwheel.I2C.RegisterRead.initial cfg) := by
  simp [start, Pinwheel.I2C.RegisterRead.initial]
  done

theorem run_simulation (cfg : Pinwheel.I2C.Config) (r : Pinwheel.I2C.RegisterRead.Request)
    (incoming : Nat → Pinwheel.I2C.Bus) (n : Nat) :
    run (program cfg r) (start (program cfg r) (I2C.encodeInputs (incoming 0)))
      (fun t => I2C.encodeInputs (incoming t)) n =
      lift r (Pinwheel.I2C.RegisterRead.run cfg (Pinwheel.I2C.RegisterRead.initial cfg) incoming n) := by
  induction n <;> simp_all only [run, Pinwheel.I2C.RegisterRead.run, initial_matches, advance_simulation]
  done

theorem result_lift (r : Pinwheel.I2C.RegisterRead.Request) (s : Pinwheel.I2C.RegisterRead.State) :
    result (lift r s) = Pinwheel.I2C.RegisterRead.result s := by
  cases hp : s.phase <;> simp [result, Pinwheel.I2C.RegisterRead.result, hp]
  done

theorem reset_releases (cfg : Pinwheel.I2C.Config) (r : Pinwheel.I2C.RegisterRead.Request)
    (s : ReadState) (inputs : Inputs) (startRequested : Bool) :
    (step (program cfg r) s true startRequested inputs).pins = ({} : Pins) := rfl

/-- Three status bits are outside the eight receive destinations. -/
theorem receive_preserves_status (samples : Vector Bool 16) (bit : Fin 8) (sda : Bool)
    (status : Fin 16) (h : 8 ≤ status.val) :
    (Pinwheel.I2C.RegisterRead.latch samples ⟨27 + bit.val, by omega⟩ sda)[status.val] = samples[status.val] := by
  simp [Pinwheel.I2C.RegisterRead.latch, Pinwheel.I2C.RegisterRead.sampleAt,
    show 27 + bit.val ≠ 8 by omega, show 27 + bit.val ≠ 17 by omega,
    show 27 + bit.val ≠ 26 by omega, show 27 + bit.val < 35 by omega, show bit.val ≠ status.val by omega]
  done

end Pinwheel.Compile.I2CRead
