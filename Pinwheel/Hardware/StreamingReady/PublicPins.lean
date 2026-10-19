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

end Pinwheel.Hardware.StreamingReady.PublicPins
