import Pinwheel.Compile.I2C
import Pinwheel.Engine.ControlProofs

namespace Pinwheel.Compile.I2C
open Engine.Reactive

def sampleOutcome (slots : Engine.Samples) : Pinwheel.I2C.Outcome :=
  if slots[0] then .addressNack else if slots[1] then .dataNack else .success

def bitPC (slot : Fin 18) (phase : Fin 4) : Fin 128 := ⟨2 + 4 * slot.val + phase.val, by omega⟩

def control (s : Pinwheel.I2C.State) : Control :=
  match s.phase with
  | .free => .qualifying 0 s.remaining s.waitLeft
  | .startHold => .checked 1 s.remaining
  | .setup => .active (bitPC s.slot 0) s.remaining
  | .rise => .waiting (bitPC s.slot 1) s.waitLeft
  | .high => .checked (bitPC s.slot 2) s.remaining
  | .fall => .checked (bitPC s.slot 3) s.remaining
  | .stopLow => .active 74 s.remaining
  | .stopRise => .waiting 75 s.waitLeft
  | .stopHigh => .checked 76 s.remaining
  | .stopFree => .qualifying 77 s.remaining s.waitLeft
  | .finished => .stopped (match s.outcome with
      | .timeout => .timeout | .busFault => .fault | _ => .completed)

def lift (s : Pinwheel.I2C.State) (slots : Engine.Samples) : State :=
  ⟨control s, encodePins (Pinwheel.I2C.pins s), slots⟩

/-- ACK flags are meaningful only at/after their capture. Abort preserves arbitrary samples. -/
def SamplesOK (s : Pinwheel.I2C.State) (slots : Engine.Samples) : Prop :=
  (s.phase = .finished ∧ (s.outcome = .timeout ∨ s.outcome = .busFault)) ∨
  (s.outcome = sampleOutcome slots ∧ match s.phase with
    | .stopLow | .stopRise | .stopHigh | .stopFree | .finished => True
    | .fall => (slots[0] = true → s.slot.val = 8) ∧ (slots[1] = true → s.slot.val = 17)
    | .free | .startHold => slots[0] = false ∧ slots[1] = false ∧ s.slot.val = 0
    | _ => slots[0] = false ∧ slots[1] = false)

def Matches (s : Pinwheel.I2C.State) (e : State) : Prop :=
  e = lift s e.samples ∧ SamplesOK s e.samples

theorem input_clock (bus : Pinwheel.I2C.Bus) : (encodeInputs bus)[0] = bus.scl := by
  cases bus with | mk scl sda => cases scl <;> cases sda <;> rfl
  done

theorem input_data (bus : Pinwheel.I2C.Bus) : (encodeInputs bus)[1] = bus.sda := by
  cases bus with | mk scl sda => cases scl <;> cases sda <;> rfl
  done

theorem check_clock (bus : Pinwheel.I2C.Bus) : clockHigh.ready (encodeInputs bus) = bus.scl := by
  cases bus with | mk scl sda => cases scl <;> cases sda <;> rfl
  done

theorem check_both (bus : Pinwheel.I2C.Bus) : bothHigh.ready (encodeInputs bus) = (bus.scl && bus.sda) := by
  cases bus with | mk scl sda => cases scl <;> cases sda <;> rfl
  done

theorem check_none (inputs : Inputs) : unguarded.ready inputs = true := by
  simp [unguarded, Check.ready]
  done

theorem fetch_bit (cfg : Pinwheel.I2C.Config) (r : Pinwheel.I2C.Request)
    (slot : Fin 18) (phase : Fin 4) :
    (program cfg r).fetch (bitPC slot phase) = bitInstruction cfg r slot phase.val := by
  simp [program, Program.fetch, instruction, bitPC]
  simp [show 2 + 4 * slot.val + phase.val ≠ 1 by omega,
    show 2 + 4 * slot.val + phase.val < 74 by omega,
    show (2 + 4 * slot.val + phase.val - 2) / 4 = slot.val by omega,
    show (2 + 4 * slot.val + phase.val - 2) % 4 = phase.val by omega]
  done

theorem advance_free (cfg : Pinwheel.I2C.Config) (s : Pinwheel.I2C.State)
    (slots : Engine.Samples) (bus : Pinwheel.I2C.Bus)
    (hp : s.phase = .free) (hs : SamplesOK s slots) :
    Matches (Pinwheel.I2C.step cfg s bus)
      (advance (program cfg s.request) (lift s slots) (encodeInputs bus)) := by
  simp [SamplesOK, hp, sampleOutcome] at hs
  rcases hs with ⟨ho, h0, h1⟩
  by_cases hr : s.remaining = 0 <;> by_cases hw : 0 < s.waitLeft.val <;>
    cases hb : bus.scl <;> cases hd : bus.sda
  all_goals simp_all [Matches, lift, control, SamplesOK, sampleOutcome, advance, program, Program.fetch,
    instruction, check_both, next, enter, stop, Pinwheel.I2C.step, Pinwheel.I2C.move,
    Pinwheel.I2C.count, Pinwheel.I2C.blocked, Pinwheel.I2C.finish, Pinwheel.I2C.pins,
    encodePins, Pins.openDrain, capture, show (78 : Fin 128).val = 78 from rfl,
    show (0 < s.remaining.val) ↔ s.remaining ≠ 0 by omega]
  done

private theorem remaining_pos (r : Fin 256) : (0 < r.val) ↔ r ≠ 0 := by omega

private theorem last_value : (78 : Fin 128).val = 78 := rfl

private theorem pc74 : (74 : Fin 128).val = 74 := rfl
private theorem pc75 : (75 : Fin 128).val = 75 := rfl
private theorem pc76 : (76 : Fin 128).val = 76 := rfl
private theorem pc77 : (77 : Fin 128).val = 77 := rfl

attribute [local simp] Matches lift control SamplesOK sampleOutcome advance program Program.fetch
  instruction bitInstruction bitPC bitPins ackCapture fallFinish
  check_clock check_both check_none input_clock input_data Condition.ready
  next enter stop dispatch jump capture Engine.capture
  Pinwheel.I2C.step Pinwheel.I2C.move Pinwheel.I2C.count Pinwheel.I2C.blocked
  Pinwheel.I2C.finish Pinwheel.I2C.pins Pinwheel.I2C.dataDrive
  Pinwheel.I2C.afterHigh Pinwheel.I2C.afterFall encodePins Pins.openDrain
  remaining_pos last_value pc74 pc75 pc76 pc77

theorem advance_start (cfg : Pinwheel.I2C.Config) (s : Pinwheel.I2C.State)
    (slots : Engine.Samples) (bus : Pinwheel.I2C.Bus)
    (hp : s.phase = .startHold) (hs : SamplesOK s slots) :
    Matches (Pinwheel.I2C.step cfg s bus)
      (advance (program cfg s.request) (lift s slots) (encodeInputs bus)) := by
  by_cases hr : s.remaining = 0 <;> cases hb : bus.scl
  all_goals simp_all
  done

theorem advance_stopLow (cfg : Pinwheel.I2C.Config) (s : Pinwheel.I2C.State)
    (slots : Engine.Samples) (bus : Pinwheel.I2C.Bus)
    (hp : s.phase = .stopLow) (hs : SamplesOK s slots) :
    Matches (Pinwheel.I2C.step cfg s bus)
      (advance (program cfg s.request) (lift s slots) (encodeInputs bus)) := by
  by_cases hr : s.remaining = 0
  all_goals simp_all
  done

theorem advance_stopRise (cfg : Pinwheel.I2C.Config) (s : Pinwheel.I2C.State)
    (slots : Engine.Samples) (bus : Pinwheel.I2C.Bus)
    (hp : s.phase = .stopRise) (hs : SamplesOK s slots) :
    Matches (Pinwheel.I2C.step cfg s bus)
      (advance (program cfg s.request) (lift s slots) (encodeInputs bus)) := by
  by_cases hw : s.waitLeft = 0 <;> cases hb : bus.scl
  all_goals simp_all
  done

theorem advance_stopHigh (cfg : Pinwheel.I2C.Config) (s : Pinwheel.I2C.State)
    (slots : Engine.Samples) (bus : Pinwheel.I2C.Bus)
    (hp : s.phase = .stopHigh) (hs : SamplesOK s slots) :
    Matches (Pinwheel.I2C.step cfg s bus)
      (advance (program cfg s.request) (lift s slots) (encodeInputs bus)) := by
  by_cases hr : s.remaining = 0 <;> cases hb : bus.scl
  all_goals simp_all
  done

theorem advance_stopFree (cfg : Pinwheel.I2C.Config) (s : Pinwheel.I2C.State)
    (slots : Engine.Samples) (bus : Pinwheel.I2C.Bus)
    (hp : s.phase = .stopFree) (hs : SamplesOK s slots) :
    Matches (Pinwheel.I2C.step cfg s bus)
      (advance (program cfg s.request) (lift s slots) (encodeInputs bus)) := by
  by_cases hr : s.remaining = 0 <;> by_cases hw : s.waitLeft = 0 <;>
    cases hb : bus.scl <;> cases hd : bus.sda
  all_goals simp_all
  all_goals cases h0 : slots[0] <;> cases h1 : slots[1] <;> simp_all
  done

theorem advance_finished (cfg : Pinwheel.I2C.Config) (s : Pinwheel.I2C.State)
    (slots : Engine.Samples) (bus : Pinwheel.I2C.Bus)
    (hp : s.phase = .finished) (hs : SamplesOK s slots) :
    Matches (Pinwheel.I2C.step cfg s bus)
      (advance (program cfg s.request) (lift s slots) (encodeInputs bus)) := by
  cases ho : s.outcome <;> cases h0 : slots[0] <;> cases h1 : slots[1] <;> simp_all
  done

private theorem slot_cases (slot : Fin 18) : slot = 0 ∨ slot = 1 ∨ slot = 2 ∨ slot = 3 ∨ slot = 4 ∨ slot = 5 ∨ slot = 6 ∨ slot = 7 ∨ slot = 8 ∨ slot = 9 ∨ slot = 10 ∨ slot = 11 ∨ slot = 12 ∨ slot = 13 ∨ slot = 14 ∨ slot = 15 ∨ slot = 16 ∨ slot = 17 := by omega

/-- Concrete address reduction facts avoid numeral-normalization loops in the pinned simplifier. -/
private theorem address_literals :
    (0 : Fin 128).val = 0 ∧ (1 : Fin 128).val = 1 ∧ (2 : Fin 128).val = 2 ∧ (3 : Fin 128).val = 3 ∧
    (4 : Fin 128).val = 4 ∧ (5 : Fin 128).val = 5 ∧ (6 : Fin 128).val = 6 ∧ (7 : Fin 128).val = 7 ∧
    (8 : Fin 128).val = 8 ∧ (9 : Fin 128).val = 9 ∧ (10 : Fin 128).val = 10 ∧ (11 : Fin 128).val = 11 ∧
    (12 : Fin 128).val = 12 ∧ (13 : Fin 128).val = 13 ∧ (14 : Fin 128).val = 14 ∧ (15 : Fin 128).val = 15 ∧
    (16 : Fin 128).val = 16 ∧ (17 : Fin 128).val = 17 ∧ (18 : Fin 128).val = 18 ∧ (19 : Fin 128).val = 19 ∧
    (20 : Fin 128).val = 20 ∧ (21 : Fin 128).val = 21 ∧ (22 : Fin 128).val = 22 ∧ (23 : Fin 128).val = 23 ∧
    (24 : Fin 128).val = 24 ∧ (25 : Fin 128).val = 25 ∧ (26 : Fin 128).val = 26 ∧ (27 : Fin 128).val = 27 ∧
    (28 : Fin 128).val = 28 ∧ (29 : Fin 128).val = 29 ∧ (30 : Fin 128).val = 30 ∧ (31 : Fin 128).val = 31 ∧
    (32 : Fin 128).val = 32 ∧ (33 : Fin 128).val = 33 ∧ (34 : Fin 128).val = 34 ∧ (35 : Fin 128).val = 35 ∧
    (36 : Fin 128).val = 36 ∧ (37 : Fin 128).val = 37 ∧ (38 : Fin 128).val = 38 ∧ (39 : Fin 128).val = 39 ∧
    (40 : Fin 128).val = 40 ∧ (41 : Fin 128).val = 41 ∧ (42 : Fin 128).val = 42 ∧ (43 : Fin 128).val = 43 ∧
    (44 : Fin 128).val = 44 ∧ (45 : Fin 128).val = 45 ∧ (46 : Fin 128).val = 46 ∧ (47 : Fin 128).val = 47 ∧
    (48 : Fin 128).val = 48 ∧ (49 : Fin 128).val = 49 ∧ (50 : Fin 128).val = 50 ∧ (51 : Fin 128).val = 51 ∧
    (52 : Fin 128).val = 52 ∧ (53 : Fin 128).val = 53 ∧ (54 : Fin 128).val = 54 ∧ (55 : Fin 128).val = 55 ∧
    (56 : Fin 128).val = 56 ∧ (57 : Fin 128).val = 57 ∧ (58 : Fin 128).val = 58 ∧ (59 : Fin 128).val = 59 ∧
    (60 : Fin 128).val = 60 ∧ (61 : Fin 128).val = 61 ∧ (62 : Fin 128).val = 62 ∧ (63 : Fin 128).val = 63 ∧
    (64 : Fin 128).val = 64 ∧ (65 : Fin 128).val = 65 ∧ (66 : Fin 128).val = 66 ∧ (67 : Fin 128).val = 67 ∧
    (68 : Fin 128).val = 68 ∧ (69 : Fin 128).val = 69 ∧ (70 : Fin 128).val = 70 ∧ (71 : Fin 128).val = 71 ∧
    (72 : Fin 128).val = 72 ∧ (73 : Fin 128).val = 73 ∧ (74 : Fin 128).val = 74 ∧ (75 : Fin 128).val = 75 ∧
    (76 : Fin 128).val = 76 ∧ (77 : Fin 128).val = 77 ∧ (78 : Fin 128).val = 78 ∧ (0 : Fin 18).val = 0 ∧
    (1 : Fin 18).val = 1 ∧ (2 : Fin 18).val = 2 ∧ (3 : Fin 18).val = 3 ∧ (4 : Fin 18).val = 4 ∧
    (5 : Fin 18).val = 5 ∧ (6 : Fin 18).val = 6 ∧ (7 : Fin 18).val = 7 ∧ (8 : Fin 18).val = 8 ∧
    (9 : Fin 18).val = 9 ∧ (10 : Fin 18).val = 10 ∧ (11 : Fin 18).val = 11 ∧ (12 : Fin 18).val = 12 ∧
    (13 : Fin 18).val = 13 ∧ (14 : Fin 18).val = 14 ∧ (15 : Fin 18).val = 15 ∧ (16 : Fin 18).val = 16 ∧
    (17 : Fin 18).val = 17 ∧
    (0 : Fin 4).val = 0 ∧ (1 : Fin 4).val = 1 ∧ (2 : Fin 4).val = 2 ∧
    (3 : Fin 4).val = 3 := by repeat constructor

attribute [local simp] address_literals

set_option maxHeartbeats 1000000 in
theorem advance_setup (cfg : Pinwheel.I2C.Config) (s : Pinwheel.I2C.State)
    (slots : Engine.Samples) (bus : Pinwheel.I2C.Bus)
    (hp : s.phase = .setup) (hs : SamplesOK s slots) :
    Matches (Pinwheel.I2C.step cfg s bus)
      (advance (program cfg s.request) (lift s slots) (encodeInputs bus)) := by
  rcases slot_cases s.slot with hslot | hslot | hslot | hslot | hslot | hslot | hslot | hslot | hslot | hslot | hslot | hslot | hslot | hslot | hslot | hslot | hslot | hslot
  all_goals by_cases hr : s.remaining = 0 <;> simp_all
  all_goals cases hd : Pinwheel.I2C.releaseData s.request s.slot <;> simp_all
  done

set_option maxHeartbeats 1000000 in
theorem advance_rise (cfg : Pinwheel.I2C.Config) (s : Pinwheel.I2C.State)
    (slots : Engine.Samples) (bus : Pinwheel.I2C.Bus)
    (hp : s.phase = .rise) (hs : SamplesOK s slots) :
    Matches (Pinwheel.I2C.step cfg s bus)
      (advance (program cfg s.request) (lift s slots) (encodeInputs bus)) := by
  rcases slot_cases s.slot with hslot | hslot | hslot | hslot | hslot | hslot | hslot | hslot | hslot | hslot | hslot | hslot | hslot | hslot | hslot | hslot | hslot | hslot
  all_goals by_cases hw : s.waitLeft = 0 <;> cases hb : bus.scl <;> simp_all
  all_goals cases hd : Pinwheel.I2C.releaseData s.request s.slot <;> simp_all
  done

set_option maxHeartbeats 2000000 in
theorem advance_high (cfg : Pinwheel.I2C.Config) (s : Pinwheel.I2C.State)
    (slots : Engine.Samples) (bus : Pinwheel.I2C.Bus)
    (hp : s.phase = .high) (hs : SamplesOK s slots) :
    Matches (Pinwheel.I2C.step cfg s bus)
      (advance (program cfg s.request) (lift s slots) (encodeInputs bus)) := by
  rcases slot_cases s.slot with hslot | hslot | hslot | hslot | hslot | hslot | hslot | hslot | hslot | hslot | hslot | hslot | hslot | hslot | hslot | hslot | hslot | hslot
  all_goals by_cases hr : s.remaining = 0 <;> cases hb : bus.scl <;> cases hd : bus.sda <;> simp_all
  all_goals cases hv : Pinwheel.I2C.releaseData s.request s.slot <;> simp_all
  done

private theorem data_low (b : Bool) :
    (if b then Pinwheel.I2C.Drive.release else .low) = .low ↔ b = false := by
  cases b <;> simp
  done

attribute [local simp] data_low

set_option maxHeartbeats 2000000 in
theorem advance_fall (cfg : Pinwheel.I2C.Config) (s : Pinwheel.I2C.State)
    (slots : Engine.Samples) (bus : Pinwheel.I2C.Bus)
    (hp : s.phase = .fall) (hs : SamplesOK s slots) :
    Matches (Pinwheel.I2C.step cfg s bus)
      (advance (program cfg s.request) (lift s slots) (encodeInputs bus)) := by
  rcases slot_cases s.slot with hslot | hslot | hslot | hslot | hslot | hslot | hslot | hslot | hslot | hslot | hslot | hslot | hslot | hslot | hslot | hslot | hslot | hslot
  all_goals cases h0 : slots[0] <;> cases h1 : slots[1] <;> by_cases hr : s.remaining = 0 <;> simp_all
  all_goals cases hv : Pinwheel.I2C.releaseData s.request ⟨s.slot.val + 1, by omega⟩ <;> simp_all
  done

end Pinwheel.Compile.I2C
