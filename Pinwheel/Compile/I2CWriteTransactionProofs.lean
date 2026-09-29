import Pinwheel.Compile.I2CWriteTransaction
import Pinwheel.I2C.WriteTransactionProofs
import Pinwheel.Compile.I2CPhases
import Pinwheel.Engine.FetchProofs

set_option maxRecDepth 4096

namespace Pinwheel.Compile.I2CWriteTransaction
open Engine.Reactive

def control (s : Pinwheel.I2C.WriteTransaction.State) : Control 255 :=
  match s.phase with
  | .free => .qualifying 0 s.remaining s.waitLeft
  | .startHold => .checked 1 s.remaining
  | .setup slot => .active (bitPC slot 0) s.remaining
  | .rise slot => .waiting (bitPC slot 1) s.waitLeft
  | .high slot => .checked (bitPC slot 2) s.remaining
  | .fall slot => .checked (bitPC slot 3) s.remaining
  | .stopLow => .active 110 s.remaining
  | .stopRise => .waiting 111 s.waitLeft
  | .stopHigh => .checked 112 s.remaining
  | .stopFree => .qualifying 113 s.remaining s.waitLeft
  | .finished => .stopped .completed
  | .timeout => .stopped .timeout
  | .fault => .stopped .fault

def lift (r : Pinwheel.I2C.WriteTransaction.Request) (s : Pinwheel.I2C.WriteTransaction.State) : WriteState :=
  ⟨control s, I2C.encodePins (Pinwheel.I2C.WriteTransaction.pins r s.phase), s.samples⟩

theorem latch_capture (samples : Vector Bool 16) (slot : Fin 27) (bus : Pinwheel.I2C.Bus) :
    capture samples ((Pinwheel.I2C.WriteTransaction.sampleAt slot).map (⟨1, ·⟩)) (I2C.encodeInputs bus) =
      Pinwheel.I2C.WriteTransaction.latch samples slot bus.sda := by
  cases h : Pinwheel.I2C.WriteTransaction.sampleAt slot <;> simp [capture, Pinwheel.I2C.WriteTransaction.latch, h, I2C.input_data, Engine.capture]
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
    (0 : Fin 27).val = 0 ∧
    (1 : Fin 27).val = 1 ∧
    (2 : Fin 27).val = 2 ∧
    (3 : Fin 27).val = 3 ∧
    (4 : Fin 27).val = 4 ∧
    (5 : Fin 27).val = 5 ∧
    (6 : Fin 27).val = 6 ∧
    (7 : Fin 27).val = 7 ∧
    (8 : Fin 27).val = 8 ∧
    (9 : Fin 27).val = 9 ∧
    (10 : Fin 27).val = 10 ∧
    (11 : Fin 27).val = 11 ∧
    (12 : Fin 27).val = 12 ∧
    (13 : Fin 27).val = 13 ∧
    (14 : Fin 27).val = 14 ∧
    (15 : Fin 27).val = 15 ∧
    (16 : Fin 27).val = 16 ∧
    (17 : Fin 27).val = 17 ∧
    (18 : Fin 27).val = 18 ∧
    (19 : Fin 27).val = 19 ∧
    (20 : Fin 27).val = 20 ∧
    (21 : Fin 27).val = 21 ∧
    (22 : Fin 27).val = 22 ∧
    (23 : Fin 27).val = 23 ∧
    (24 : Fin 27).val = 24 ∧
    (25 : Fin 27).val = 25 ∧
    (26 : Fin 27).val = 26 ∧
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
    (15 : Fin 16).val = 15 ∧
    (0 : Fin 2).val = 0 ∧
    (1 : Fin 2).val = 1 := by repeat constructor

attribute [local simp] capture lift control advance program Program.fetch instruction bitInstruction bitPC bitPins fallFinish
  I2C.check_clock I2C.check_both I2C.check_none I2C.input_clock I2C.input_data Condition.ready
  next enter stop dispatch jump
  Pinwheel.I2C.WriteTransaction.step Pinwheel.I2C.WriteTransaction.move Pinwheel.I2C.WriteTransaction.count
  Pinwheel.I2C.WriteTransaction.blocked Pinwheel.I2C.WriteTransaction.finish Pinwheel.I2C.WriteTransaction.timed
  Pinwheel.I2C.WriteTransaction.guarded Pinwheel.I2C.WriteTransaction.pins
  I2C.encodePins Pins.openDrain remaining_pos literals

private theorem slot_cases (slot : Fin 27) : slot = 0 ∨ slot = 1 ∨ slot = 2 ∨ slot = 3 ∨ slot = 4 ∨ slot = 5 ∨ slot = 6 ∨ slot = 7 ∨ slot = 8 ∨ slot = 9 ∨ slot = 10 ∨ slot = 11 ∨ slot = 12 ∨ slot = 13 ∨ slot = 14 ∨ slot = 15 ∨ slot = 16 ∨ slot = 17 ∨ slot = 18 ∨ slot = 19 ∨ slot = 20 ∨ slot = 21 ∨ slot = 22 ∨ slot = 23 ∨ slot = 24 ∨ slot = 25 ∨ slot = 26 := by omega

set_option maxHeartbeats 3000000 in
theorem advance_fall (cfg : Pinwheel.I2C.Config) (r : Pinwheel.I2C.WriteTransaction.Request)
    (s : Pinwheel.I2C.WriteTransaction.State) (slot : Fin 27) (bus : Pinwheel.I2C.Bus) (hp : s.phase = .fall slot) :
    advance (program cfg r) (lift r s) (I2C.encodeInputs bus) =
      lift r (Pinwheel.I2C.WriteTransaction.step cfg r s bus) := by
  rcases slot_cases slot with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  all_goals cases h0 : s.samples[0] <;> cases h1 : s.samples[1] <;>
    by_cases hc : r.countMinusOne.val = 0 <;> by_cases hr : s.remaining = 0 <;>
    simp_all [Pinwheel.I2C.WriteTransaction.afterFall]
  done

set_option maxHeartbeats 3000000 in
theorem advance_high (cfg : Pinwheel.I2C.Config) (r : Pinwheel.I2C.WriteTransaction.Request)
    (s : Pinwheel.I2C.WriteTransaction.State) (slot : Fin 27) (bus : Pinwheel.I2C.Bus) (hp : s.phase = .high slot) :
    advance (program cfg r) (lift r s) (I2C.encodeInputs bus) =
      lift r (Pinwheel.I2C.WriteTransaction.step cfg r s bus) := by
  rcases slot_cases slot with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  all_goals by_cases hr : s.remaining = 0 <;> cases hb : bus.scl <;> simp_all
  all_goals simpa only [hs, capture] using latch_capture s.samples slot bus
  done

set_option maxHeartbeats 3000000 in
theorem advance_setup (cfg : Pinwheel.I2C.Config) (r : Pinwheel.I2C.WriteTransaction.Request)
    (s : Pinwheel.I2C.WriteTransaction.State) (slot : Fin 27) (bus : Pinwheel.I2C.Bus) (hp : s.phase = .setup slot) :
    advance (program cfg r) (lift r s) (I2C.encodeInputs bus) =
      lift r (Pinwheel.I2C.WriteTransaction.step cfg r s bus) := by
  rcases slot_cases slot with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs <;>
    by_cases hr : s.remaining = 0 <;> by_cases hw : s.waitLeft = 0 <;> cases hb : bus.scl <;> simp_all
  done

set_option maxHeartbeats 3000000 in
theorem advance_rise (cfg : Pinwheel.I2C.Config) (r : Pinwheel.I2C.WriteTransaction.Request)
    (s : Pinwheel.I2C.WriteTransaction.State) (slot : Fin 27) (bus : Pinwheel.I2C.Bus) (hp : s.phase = .rise slot) :
    advance (program cfg r) (lift r s) (I2C.encodeInputs bus) =
      lift r (Pinwheel.I2C.WriteTransaction.step cfg r s bus) := by
  rcases slot_cases slot with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs <;>
    by_cases hr : s.remaining = 0 <;> by_cases hw : s.waitLeft = 0 <;> cases hb : bus.scl <;> simp_all
  done

theorem advance_free (cfg : Pinwheel.I2C.Config) (r : Pinwheel.I2C.WriteTransaction.Request)
    (s : Pinwheel.I2C.WriteTransaction.State) (bus : Pinwheel.I2C.Bus) (hp : s.phase = .free) :
    advance (program cfg r) (lift r s) (I2C.encodeInputs bus) =
      lift r (Pinwheel.I2C.WriteTransaction.step cfg r s bus) := by
  by_cases hr : s.remaining = 0 <;> by_cases hw : s.waitLeft = 0 <;>
    cases hb : bus.scl <;> cases hd : bus.sda <;> simp_all
  done

theorem advance_startHold (cfg : Pinwheel.I2C.Config) (r : Pinwheel.I2C.WriteTransaction.Request)
    (s : Pinwheel.I2C.WriteTransaction.State) (bus : Pinwheel.I2C.Bus) (hp : s.phase = .startHold) :
    advance (program cfg r) (lift r s) (I2C.encodeInputs bus) =
      lift r (Pinwheel.I2C.WriteTransaction.step cfg r s bus) := by
  by_cases hr : s.remaining = 0 <;> by_cases hw : s.waitLeft = 0 <;>
    cases hb : bus.scl <;> cases hd : bus.sda <;> simp_all
  done

theorem advance_stopLow (cfg : Pinwheel.I2C.Config) (r : Pinwheel.I2C.WriteTransaction.Request)
    (s : Pinwheel.I2C.WriteTransaction.State) (bus : Pinwheel.I2C.Bus) (hp : s.phase = .stopLow) :
    advance (program cfg r) (lift r s) (I2C.encodeInputs bus) =
      lift r (Pinwheel.I2C.WriteTransaction.step cfg r s bus) := by
  by_cases hr : s.remaining = 0 <;> by_cases hw : s.waitLeft = 0 <;>
    cases hb : bus.scl <;> cases hd : bus.sda <;> simp_all
  done

theorem advance_stopRise (cfg : Pinwheel.I2C.Config) (r : Pinwheel.I2C.WriteTransaction.Request)
    (s : Pinwheel.I2C.WriteTransaction.State) (bus : Pinwheel.I2C.Bus) (hp : s.phase = .stopRise) :
    advance (program cfg r) (lift r s) (I2C.encodeInputs bus) =
      lift r (Pinwheel.I2C.WriteTransaction.step cfg r s bus) := by
  by_cases hr : s.remaining = 0 <;> by_cases hw : s.waitLeft = 0 <;>
    cases hb : bus.scl <;> cases hd : bus.sda <;> simp_all
  done

theorem advance_stopHigh (cfg : Pinwheel.I2C.Config) (r : Pinwheel.I2C.WriteTransaction.Request)
    (s : Pinwheel.I2C.WriteTransaction.State) (bus : Pinwheel.I2C.Bus) (hp : s.phase = .stopHigh) :
    advance (program cfg r) (lift r s) (I2C.encodeInputs bus) =
      lift r (Pinwheel.I2C.WriteTransaction.step cfg r s bus) := by
  by_cases hr : s.remaining = 0 <;> by_cases hw : s.waitLeft = 0 <;>
    cases hb : bus.scl <;> cases hd : bus.sda <;> simp_all
  done

theorem advance_stopFree (cfg : Pinwheel.I2C.Config) (r : Pinwheel.I2C.WriteTransaction.Request)
    (s : Pinwheel.I2C.WriteTransaction.State) (bus : Pinwheel.I2C.Bus) (hp : s.phase = .stopFree) :
    advance (program cfg r) (lift r s) (I2C.encodeInputs bus) =
      lift r (Pinwheel.I2C.WriteTransaction.step cfg r s bus) := by
  by_cases hr : s.remaining = 0 <;> by_cases hw : s.waitLeft = 0 <;>
    cases hb : bus.scl <;> cases hd : bus.sda <;> simp_all
  done

theorem advance_finished (cfg : Pinwheel.I2C.Config) (r : Pinwheel.I2C.WriteTransaction.Request)
    (s : Pinwheel.I2C.WriteTransaction.State) (bus : Pinwheel.I2C.Bus) (hp : s.phase = .finished) :
    advance (program cfg r) (lift r s) (I2C.encodeInputs bus) =
      lift r (Pinwheel.I2C.WriteTransaction.step cfg r s bus) := by
  by_cases hr : s.remaining = 0 <;> by_cases hw : s.waitLeft = 0 <;>
    cases hb : bus.scl <;> cases hd : bus.sda <;> simp_all
  done

theorem advance_timeout (cfg : Pinwheel.I2C.Config) (r : Pinwheel.I2C.WriteTransaction.Request)
    (s : Pinwheel.I2C.WriteTransaction.State) (bus : Pinwheel.I2C.Bus) (hp : s.phase = .timeout) :
    advance (program cfg r) (lift r s) (I2C.encodeInputs bus) =
      lift r (Pinwheel.I2C.WriteTransaction.step cfg r s bus) := by
  by_cases hr : s.remaining = 0 <;> by_cases hw : s.waitLeft = 0 <;>
    cases hb : bus.scl <;> cases hd : bus.sda <;> simp_all
  done

theorem advance_fault (cfg : Pinwheel.I2C.Config) (r : Pinwheel.I2C.WriteTransaction.Request)
    (s : Pinwheel.I2C.WriteTransaction.State) (bus : Pinwheel.I2C.Bus) (hp : s.phase = .fault) :
    advance (program cfg r) (lift r s) (I2C.encodeInputs bus) =
      lift r (Pinwheel.I2C.WriteTransaction.step cfg r s bus) := by
  by_cases hr : s.remaining = 0 <;> by_cases hw : s.waitLeft = 0 <;>
    cases hb : bus.scl <;> cases hd : bus.sda <;> simp_all
  done

/-- Every reference state and consumed digital bus value, including bounded aborts. -/
theorem advance_simulation (cfg : Pinwheel.I2C.Config) (r : Pinwheel.I2C.WriteTransaction.Request)
    (s : Pinwheel.I2C.WriteTransaction.State) (bus : Pinwheel.I2C.Bus) :
    advance (program cfg r) (lift r s) (I2C.encodeInputs bus) =
      lift r (Pinwheel.I2C.WriteTransaction.step cfg r s bus) := by
  cases hp : s.phase with
  | free => exact advance_free cfg r s bus hp
  | startHold => exact advance_startHold cfg r s bus hp
  | setup slot => exact advance_setup cfg r s slot bus hp
  | rise slot => exact advance_rise cfg r s slot bus hp
  | high slot => exact advance_high cfg r s slot bus hp
  | fall slot => exact advance_fall cfg r s slot bus hp
  | stopLow => exact advance_stopLow cfg r s bus hp
  | stopRise => exact advance_stopRise cfg r s bus hp
  | stopHigh => exact advance_stopHigh cfg r s bus hp
  | stopFree => exact advance_stopFree cfg r s bus hp
  | finished => exact advance_finished cfg r s bus hp
  | timeout => exact advance_timeout cfg r s bus hp
  | fault => exact advance_fault cfg r s bus hp
  done

theorem initial_matches (cfg : Pinwheel.I2C.Config) (r : Pinwheel.I2C.WriteTransaction.Request) (inputs : Inputs) :
    start (program cfg r) inputs = lift r (Pinwheel.I2C.WriteTransaction.initial cfg) := by
  simp [start, Pinwheel.I2C.WriteTransaction.initial]
  done

theorem run_simulation (cfg : Pinwheel.I2C.Config) (r : Pinwheel.I2C.WriteTransaction.Request)
    (incoming : Nat → Pinwheel.I2C.Bus) (n : Nat) :
    run (program cfg r) (start (program cfg r) (I2C.encodeInputs (incoming 0)))
      (fun t => I2C.encodeInputs (incoming t)) n =
      lift r (Pinwheel.I2C.WriteTransaction.run cfg r (Pinwheel.I2C.WriteTransaction.initial cfg) incoming n) := by
  induction n <;> simp_all only [run, Pinwheel.I2C.WriteTransaction.run, initial_matches, advance_simulation]
  done

theorem result_lift (r : Pinwheel.I2C.WriteTransaction.Request) (s : Pinwheel.I2C.WriteTransaction.State) :
    result r (lift r s) = Pinwheel.I2C.WriteTransaction.result r s := by
  cases hp : s.phase <;> simp [result, Pinwheel.I2C.WriteTransaction.result, hp]
  done

theorem reset_releases (cfg : Pinwheel.I2C.Config) (r : Pinwheel.I2C.WriteTransaction.Request)
    (s : WriteState) (inputs : Inputs) (startRequested : Bool) :
    (step (program cfg r) s true startRequested inputs).pins = ({} : Pins) := rfl

def execute (cfg : Pinwheel.I2C.Config) (r : Pinwheel.I2C.WriteTransaction.Request)
    (incoming : Nat → Pinwheel.I2C.Bus) (n : Nat) : WriteState :=
  run (program cfg r) (start (program cfg r) (I2C.encodeInputs (incoming 0)))
    (fun t => I2C.encodeInputs (incoming t)) n

theorem waveform_correct (cfg : Pinwheel.I2C.Config) (r : Pinwheel.I2C.WriteTransaction.Request)
    (incoming : Nat → Pinwheel.I2C.Bus) (n : Nat) :
    (execute cfg r incoming n).pins = I2C.encodePins (Pinwheel.I2C.WriteTransaction.pins r
      (Pinwheel.I2C.WriteTransaction.run cfg r (Pinwheel.I2C.WriteTransaction.initial cfg) incoming n).phase) := by
  simp only [execute, run_simulation, lift]
  done

theorem samples_correct (cfg : Pinwheel.I2C.Config) (r : Pinwheel.I2C.WriteTransaction.Request)
    (incoming : Nat → Pinwheel.I2C.Bus) (n : Nat) :
    (execute cfg r incoming n).samples =
      (Pinwheel.I2C.WriteTransaction.run cfg r (Pinwheel.I2C.WriteTransaction.initial cfg) incoming n).samples := by
  simp only [execute, run_simulation, lift]
  done

theorem result_correct (cfg : Pinwheel.I2C.Config) (r : Pinwheel.I2C.WriteTransaction.Request)
    (incoming : Nat → Pinwheel.I2C.Bus) (n : Nat) :
    result r (execute cfg r incoming n) = Pinwheel.I2C.WriteTransaction.result r
      (Pinwheel.I2C.WriteTransaction.run cfg r (Pinwheel.I2C.WriteTransaction.initial cfg) incoming n) := by
  simp only [execute, run_simulation, result_lift]
  done

theorem completed_result (cfg : Pinwheel.I2C.Config) (r : Pinwheel.I2C.WriteTransaction.Request)
    (incoming : Nat → Pinwheel.I2C.Bus) (n : Nat)
    (h : (Pinwheel.I2C.WriteTransaction.run cfg r (Pinwheel.I2C.WriteTransaction.initial cfg) incoming n).phase = .finished) :
    (execute cfg r incoming n).control = .stopped .completed ∧
    busy (execute cfg r incoming n) = false ∧
    result r (execute cfg r incoming n) = some (Pinwheel.I2C.WriteTransaction.outcome r
      (Pinwheel.I2C.WriteTransaction.run cfg r (Pinwheel.I2C.WriteTransaction.initial cfg) incoming n).samples) := by
  simp only [execute, run_simulation, lift, control, h, busy, result]
  trivial
  done

theorem unused_samples_false (cfg : Pinwheel.I2C.Config) (r : Pinwheel.I2C.WriteTransaction.Request)
    (incoming : Nat → Pinwheel.I2C.Bus) (n : Nat) (index : Fin 16) (h : 3 ≤ index.val) :
    (execute cfg r incoming n).samples[index.val] = false := by
  simp only [samples_correct, Pinwheel.I2C.WriteTransaction.run_unused_false cfg r incoming n index h]
  done

theorem one_byte_third_false (cfg : Pinwheel.I2C.Config) (r : Pinwheel.I2C.WriteTransaction.Request)
    (incoming : Nat → Pinwheel.I2C.Bus) (n : Nat) (h : r.countMinusOne = 0) :
    (execute cfg r incoming n).samples[2] = false := by
  simp only [samples_correct, Pinwheel.I2C.WriteTransaction.run_one_byte_third_false cfg r incoming n h]
  done

theorem decoded_run (cfg : Pinwheel.I2C.Config) (r : Pinwheel.I2C.WriteTransaction.Request)
    (incoming : Nat → Pinwheel.I2C.Bus) (n : Nat) :
    Fetch.run (Hardware.Execution.directStore (Hardware.Execution.imageWords (program cfg r))
      (program cfg r).idle (program cfg r).last)
      (start (program cfg r) (I2C.encodeInputs (incoming 0)))
      (fun t => I2C.encodeInputs (incoming t)) n =
      lift r (Pinwheel.I2C.WriteTransaction.run cfg r (Pinwheel.I2C.WriteTransaction.initial cfg) incoming n) :=
  (Fetch.run_eq _ _ (decoded_agrees cfg r) _ _ _).trans (run_simulation cfg r incoming n)

end Pinwheel.Compile.I2CWriteTransaction
