import Pinwheel.Hardware.Buffered.SerialSourceSession

/-! Physical deselection padding between wire transactions. CS is high and
cold is low on every sample; SCK, MOSI and raw protocol inputs are arbitrary.
Both available and receipt-ready frontend boundaries retain their exact held
response while the controller still receives one quiet input per sample. -/
namespace Pinwheel.Hardware.Buffered.SerialSourceSession
open Pinwheel.Hardware Serial.Frames

def IdlePins (pins : List SerialPackage.Pins) : Prop :=
  ∀ pin ∈ pins, pin.cold = false ∧ pin.csn = true

theorem Frontend.idle_step {before : SerialPackage.State} {frontend : Frontend}
    (held : frontend.Holds before) (pin : SerialPackage.Pins)
    (cold : pin.cold = false) (idle : pin.csn = true) :
    frontend.Holds (before.step pin) ∧ (before.step pin).record.response = before.record.response ∧
      SpiCircuit.Quiet (before.coreInputs pin) := by
  cases frontend
  all_goals
    have quiet := SerialSourceRead.core_quiet before pin cold held.dispatch
    refine ⟨?_, ?_, quiet⟩
  all_goals simp only [Frontend.Holds] at held ⊢
  all_goals rw [before.record_step]
  all_goals try constructor
  all_goals simp [Serial.State.step, SerialPackage.State.inputs, SerialPackage.Pins.inputs,
    cold, idle, held.active, held.dispatch, held.capture, held.ready, held.csnPrev]

theorem Frontend.idle_run {before : SerialPackage.State} {frontend : Frontend}
    (held : frontend.Holds before) (pins : List SerialPackage.Pins) (idle : IdlePins pins) :
    frontend.Holds (before.run pins) ∧ (before.run pins).record.response = before.record.response ∧
      (∀ input ∈ before.commands pins, SpiCircuit.Quiet input) := by
  induction pins generalizing before
  case nil => exact ⟨held, rfl, by simp [SerialPackage.State.commands]⟩
  case cons pin rest ih =>
    have physical := idle pin (by simp)
    have first := Frontend.idle_step held pin physical.1 physical.2
    have tail := ih first.1 (fun p member => idle p (List.mem_cons_of_mem _ member))
    refine ⟨tail.1, tail.2.1.trans first.2.1, ?_⟩
    intro input member
    rcases List.mem_cons.mp member with equal | member
    · subst input
      exact first.2.2
    · exact tail.2.2 input member

/-- A concrete padding list retaining every supplied SCK, MOSI and raw value. -/
def deselected (samples : List SerialPackage.Pins) : List SerialPackage.Pins :=
  samples.map (fun pin => {pin with cold := false, csn := true})

theorem deselected_idle (samples : List SerialPackage.Pins) : IdlePins (deselected samples) := by
  intro pin member
  obtain ⟨original, _, rfl⟩ := List.mem_map.mp member
  exact ⟨rfl, rfl⟩

theorem deselected_length (samples : List SerialPackage.Pins) :
    (deselected samples).length = samples.length := List.length_map _

end Pinwheel.Hardware.Buffered.SerialSourceSession
