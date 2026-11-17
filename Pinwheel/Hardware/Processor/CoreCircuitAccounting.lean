import Pinwheel.Hardware.Processor.CoreCircuitEvents

/-! Ordered instruction accounting and conditional progress from physical
handshakes. Canceled held words remain in the accounting ledger without being
reported as retired. Service counts exclude stalls and reset; they assert no
eventual provider readiness or wall-clock bound. -/
namespace Pinwheel.Hardware.Processor.CoreCircuit.Events

open CoreInterface
set_option backward.isDefEq.respectTransparency false

def heldWord (raw : Values Register) : Option RV32I.Word :=
  if raw phase = 2 ∨ raw phase = 3 ∨ raw phase = 4 ∨ raw phase = 5 then some (raw instruction) else none

def enteredWords (i : Values Input) (raw : Values Register) : List RV32I.Word :=
  if circuit.observe i raw fetchResponseReady = 1 ∧ i fetchResponseValid = 1 ∧ i fetchResponseFault = 0
  then [i fetchResponseData] else []

def exitedWords (i : Values Input) (raw : Values Register) : List RV32I.Word :=
  if circuit.observe i raw cancel = 1 then (heldWord raw).toList
  else (events i raw).flatMap (fun event => (CoreModel.finishedWord (some event)).toList)

theorem heldWord_represents (raw : Values Register) (state : CoreModel.State) (rep : Represents raw state) :
    heldWord raw = CoreModel.heldWord state := by
  rcases state with ⟨a,p⟩
  rcases rep with ⟨_,hp⟩
  cases p with
  | fetchRequest => change raw phase = 0 at hp; simp [heldWord, hp, CoreModel.heldWord]
  | fetchResponse => change raw phase = 1 at hp; simp [heldWord, hp, CoreModel.heldWord]
  | execute word => simp [heldWord, hp.1, hp.2, CoreModel.heldWord]
  | dataRequest q | dataResponse q => simp [heldWord, hp.1, ← hp.2.2.1, CoreModel.heldWord]
  | fence context => simp [heldWord, hp.1, ← hp.2.2.1, CoreModel.heldWord]
  | terminal fault => simp [heldWord, hp.1, CoreModel.heldWord]

theorem heldWord_eq (raw : Values Register) (valid : Valid raw) : heldWord raw = CoreModel.heldWord (view raw) := by
  obtain ⟨state,_,rep⟩ := valid
  rw [view_of_represents raw state rep]
  exact heldWord_represents raw state rep

theorem enteredWords_eq (i : Values Input) (raw : Values Register) (valid : Valid raw) :
    enteredWords i raw = CoreModel.enteredWords (decode i) (view raw) := by
  unfold enteredWords
  rw [output_eq i raw valid]
  change (if BitVec.ofBool (CoreModel.observe (decode i) (view raw)).fetchResponseReady = 1 ∧
    i fetchResponseValid = 1 ∧ i fetchResponseFault = 0 then [i fetchResponseData] else []) = _
  cases ready : (CoreModel.observe (decode i) (view raw)).fetchResponseReady
  all_goals rcases BitVec.eq_zero_or_eq_one (i fetchResponseValid) with hv | hv
  all_goals rcases BitVec.eq_zero_or_eq_one (i fetchResponseFault) with hf | hf
  all_goals simp only [CoreModel.enteredWords, ready]
  all_goals simp [decode, hv, hf]

theorem exitedWords_eq (i : Values Input) (raw : Values Register) (valid : Valid raw) :
    exitedWords i raw = CoreModel.exitedWords (decode i) (view raw) := by
  have cancel_eq : circuit.observe i raw cancel = i reset := rfl
  simp only [exitedWords, cancel_eq, heldWord_eq raw valid, events_eq i raw valid]
  rcases BitVec.eq_zero_or_eq_one (i reset) with hr | hr
  all_goals simp only [CoreModel.exitedWords, show (decode i).reset = (i reset == 1) from rfl, hr]
  · cases he : CoreModel.event (decode i) (view raw) with
    | none => simp [CoreModel.events, CoreModel.observe, he, CoreModel.finishedWord]
    | some event => cases event <;> simp [CoreModel.events, CoreModel.observe, he, CoreModel.finishedWord]
  · rfl

theorem word_edge (i : Values Input) (raw : Values Register) (valid : Valid raw) :
    exitedWords i raw ++ (heldWord (circuit.step i raw)).toList =
      (heldWord raw).toList ++ enteredWords i raw := by
  rw [exitedWords_eq i raw valid, heldWord_eq _ (preserved i raw valid), step_eq i raw valid,
    heldWord_eq raw valid, enteredWords_eq i raw valid]
  exact CoreModel.word_edge (decode i) (view raw)

/-- Ordered accounting includes repeated identical instruction words. Every
accepted fetch exits by one completion/cancellation or remains the held word. -/
theorem word_conservation (raw : Values Register) (valid : Valid raw) (traffic : List (Values Input)) :
    circuit.component.eventTrace exitedWords raw traffic ++ (heldWord (circuit.component.run raw traffic)).toList =
      (heldWord raw).toList ++ circuit.component.eventTrace enteredWords raw traffic := by
  induction traffic generalizing raw with
  | nil => simp [Timed.Component.eventTrace, Timed.Component.run]
  | cons i rest ih =>
    change (exitedWords i raw ++ circuit.component.eventTrace exitedWords (circuit.step i raw) rest) ++
      (heldWord (circuit.component.run (circuit.step i raw) rest)).toList =
      (heldWord raw).toList ++ (enteredWords i raw ++ circuit.component.eventTrace enteredWords (circuit.step i raw) rest)
    rw [List.append_assoc, ih _ (preserved i raw valid), ← List.append_assoc, word_edge i raw valid, List.append_assoc]

/-- All raw encodings, including malformed phase7: actual cancel wins and no
retirement/trap event is fabricated on reset. No pre-reset Valid premise. -/
theorem reset_events (i : Values Input) (raw : Values Register) (resetHigh : i reset = 1) :
    events i raw = [.reset] := by
  have cancel_eq : circuit.observe i raw cancel = 1 := resetHigh
  simp only [events,extract,cancel_eq,↓reduceIte]

theorem reset_cancellation (i : Values Input) (raw : Values Register) (resetHigh : i reset = 1) :
    exitedWords i raw = (heldWord raw).toList := by
  have cancel_eq : circuit.observe i raw cancel = 1 := resetHigh
  simp only [exitedWords,cancel_eq,↓reduceIte]

/-- Stuttering of the actual event extractor preserves the complete architectural
snapshot. Pending provider transactions may still move between protocol phases. -/
theorem no_event_no_update (i : Values Input) (raw : Values Register) (valid : Valid raw)
    (silent : events i raw = []) : snapshot (circuit.step i raw) = snapshot raw := by
  have path := edge_path i raw valid
  rw [silent] at path
  exact (Timed.EventSpec.Path.nil_iff.mp path).symm

end Pinwheel.Hardware.Processor.CoreCircuit.Events
