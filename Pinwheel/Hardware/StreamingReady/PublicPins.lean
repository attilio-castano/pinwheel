import Pinwheel.Hardware.StreamingReady.SessionCorrespondence

/-! Every sampled source pin value has a concrete Tiny Tapeout pad encoding. -/
namespace Pinwheel.Hardware.StreamingReady.PublicPins
open Pinwheel.Hardware Pinwheel.Program.StreamingReady

def ui (mosi : BitVec 4) (raw : BitVec 2) (sck csn : Bool) : BitVec 8 :=
  mosi.extractLsb' 1 3 ++ (raw ++
    (mosi.extractLsb' 0 1 ++ (BitVec.ofBool sck ++ BitVec.ofBool csn)))

def embed (p : Session.Pins) : TinyWiring.Pins :=
  { ui := ui p.mosi p.rawInputs p.sck p.csn
    ena := 1, rstN := BitVec.ofBool (!p.initialize) }

private theorem ui_fields : ∀ (mosi : BitVec 4) (raw : BitVec 2) (sck csn : Bool),
    (ui mosi raw sck csn).getLsbD 0 = csn ∧
    (ui mosi raw sck csn).getLsbD 1 = sck ∧
    (ui mosi raw sck csn).extractLsb' 5 3 ++ (ui mosi raw sck csn).extractLsb' 2 1 = mosi ∧
    (ui mosi raw sck csn).extractLsb' 3 2 = raw := by
  decide +kernel

theorem physical_embed (p : Session.Pins) : SessionCorrespondence.physicalPins (embed p) = p := by
  cases p with
  | mk cold csn sck mosi raw =>
    have fields := ui_fields mosi raw sck csn
    simp only [SessionCorrespondence.physicalPins,embed,fields.1,fields.2.1,fields.2.2.1,fields.2.2.2]
    cases cold <;> rfl

theorem engine_embed (a : Nat) (p : Session.Pins) :
    TinyWiring.Description.enginePins (TinyWiring.canonical a) (embed p) = SessionCorrespondence.pins p := by
  rw [SessionCorrespondence.physical_pins_correct,physical_embed]

private theorem canonical_wiring : Wiring.Certificate a (Wiring.canonical a) := by
  constructor <;> intros <;> rfl

def step (s : Package.State a) (p : Session.Pins) : Package.State a :=
  (TinyWiring.canonical a).step (Wiring.canonical a) (Package.Components.typed a) s (embed p)

theorem step_eq (s : Package.State a) (p : Session.Pins) :
    step s p = s.step (Package.Components.typed a) (SessionCorrespondence.pins p) := by
  unfold step TinyWiring.Description.step
  rw [engine_embed]
  exact canonical_wiring.step_eq _ _ _

/-- Observe the three driven protocol pads and their enables with the package active. -/
def drive (s : Package.State a) : Pins :=
  let out := (TinyWiring.canonical a).observe (Wiring.canonical a) (Package.Components.typed a) s (embed {})
  ⟨(out .uio).extractLsb' 0 3,(out .oe).extractLsb' 0 3⟩

theorem drive_eq (im : SourceRefinement.Image p) (s : Session.State a) :
    drive (SessionCorrespondence.values im s) = s.core.pins := by
  have output : ((Wiring.canonical a).observe (Package.Components.typed a)
      (SessionCorrespondence.values im s) (SessionCorrespondence.pins {}) : Values Package.Output) =
      (fun {w} => @Package.State.observe a (SessionCorrespondence.values im s)
        (Package.Components.typed a) (SessionCorrespondence.pins {}) w) := by
    funext w port
    exact canonical_wiring.observe_eq _ _ _ port
  have pads (out : Values Package.Output) :
      (TinyWiring.canonical a).pads (embed {}) out .uio = 0#5 ++ out .levels ∧
      (TinyWiring.canonical a).pads (embed {}) out .oe = 0#5 ++ out .enabled := by
    have active : TinyWiring.active.eval (TinyWiring.inputs (embed {}) out)
        TinyWiring.registers = (1 : BitVec 1) := by
      change (1#1 &&& 1#1) = 1#1
      decide +kernel
    constructor
    · change (TinyWiring.canonicalOutput .uio).eval (TinyWiring.inputs (embed {}) out)
        TinyWiring.registers = _
      rw [TinyWiring.canonicalOutput,Expr.eval,if_pos active]
      rfl
    · change (TinyWiring.canonicalOutput .oe).eval (TinyWiring.inputs (embed {}) out)
        TinyWiring.registers = _
      rw [TinyWiring.canonicalOutput,Expr.eval,if_pos active]
      rfl
  unfold drive TinyWiring.Description.observe
  rw [engine_embed,output]
  dsimp only
  rw [(pads _).1,(pads _).2]
  have low3 (bits : BitVec 3) : (0#5 ++ bits).extractLsb' 0 3 = bits := by
    decide +revert +kernel
  rw [low3,low3]
  change ({levels := s.core.pins.levels, enabled := s.core.pins.enabled} : Pins) = s.core.pins
  cases s.core.pins
  rfl

/-- Include the initial observation and the observation after each supplied clock. -/
def driveTrace (s : Package.State a) : List Session.Pins → List Pins
  | [] => [drive s]
  | i :: rest => drive s :: driveTrace (step s i) rest

theorem driveTrace_eq (im : SourceRefinement.Image p) (s : Session.State a)
    (pins : List Session.Pins) (ha : a ≤ 3)
    (runtime : Session.RuntimeTrace p (im.pending.getLsbD 0) s pins)
    (structural : s.core.Structural) :
    driveTrace (SessionCorrespondence.values im s) pins =
      pinTrace p s.core (s.runtimeInputs p (im.pending.getLsbD 0) pins) := by
  induction pins generalizing s with
  | nil => simp [driveTrace,drive_eq,Session.State.runtimeInputs,pinTrace]
  | cons i rest ih =>
    have first := SessionCorrespondence.step_correct im s i ha runtime.1 structural
    simp only [driveTrace,drive_eq,step_eq,first,Session.State.runtimeInputs,pinTrace]
    exact congrArg (s.core.pins :: ·) (ih _ runtime.2 (s.step_structural p _ i structural))

theorem rawTrace_eq (s : Session.State a) (p : Program) (pending : Bool) (pins : List Session.Pins) :
    (s.runtimeInputs p pending pins).map Pinwheel.Program.Streaming.Input.rawInputs =
      pins.map (fun pin => (embed pin).ui.extractLsb' 3 2) := by
  rw [s.runtime_rawInputs]
  apply List.map_congr_left
  intro pin _
  exact (congrArg Pinwheel.Program.Streaming.Session.Pins.rawInputs (physical_embed pin)).symm

end Pinwheel.Hardware.StreamingReady.PublicPins
