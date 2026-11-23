import Pinwheel.Hardware.Processor.CoreCircuitAccounting

/-! Conditional retirement/trap progress measured from actual service pins.
Reset is excluded. An insufficiently served or terminal core is not promised
to retire; autonomous timer/device activity does not count as core service. -/
namespace Pinwheel.Hardware.Processor.CoreCircuit.Events

open CoreInterface
set_option backward.isDefEq.respectTransparency false

def rank (raw : Values Register) : Nat :=
  if raw phase = 0 then 4 else if raw phase = 1 then 3 else if raw phase = 2 then 2
  else if raw phase = 3 then 1 else 0

def service (i : Values Input) (raw : Values Register) : Bool :=
  if i reset = 1 then false else
  if raw phase = 0 then i fetchReady == 1
  else if raw phase = 1 then i fetchResponseValid == 1
  else if raw phase = 2 then true
  else if raw phase = 3 then i dataServiceValid == 1
  else if raw phase = 4 then i dataResponseValid == 1
  else if raw phase = 5 then true else false

def finished (i : Values Input) (raw : Values Register) : Prop :=
  circuit.observe i raw retireValid = 1 ∨ circuit.observe i raw trapValid = 1

theorem rank_represents (raw : Values Register) (state : CoreModel.State) (rep : Represents raw state) :
    rank raw = CoreModel.rank state := by
  rcases state with ⟨a,p⟩
  rcases rep with ⟨_,hp⟩
  cases p with
  | fetchRequest => change raw phase = 0 at hp; simp [rank,hp,CoreModel.rank]
  | fetchResponse => change raw phase = 1 at hp; simp [rank,hp,CoreModel.rank]
  | execute _ | dataRequest _ | dataResponse _ | fence _ | terminal _ => simp [rank,hp.1,CoreModel.rank]

theorem rank_eq (raw : Values Register) (valid : Valid raw) : rank raw = CoreModel.rank (view raw) := by
  obtain ⟨state,_,rep⟩ := valid
  rw [view_of_represents raw state rep]
  exact rank_represents raw state rep

theorem service_represents (i : Values Input) (raw : Values Register) (state : CoreModel.State)
    (rep : Represents raw state) : service i raw = CoreModel.service (decode i) state := by
  rcases state with ⟨a,p⟩
  rcases rep with ⟨_,hp⟩
  cases p with
  | fetchRequest => change raw phase = 0 at hp; simp [service,hp,CoreModel.service,decode]
  | fetchResponse =>
    change raw phase = 1 at hp
    by_cases response : i fetchResponseValid = (1#1) <;> simp [service,hp,CoreModel.service,decode,response]
  | execute _ | fence _ | terminal _ => simp [service,hp.1,CoreModel.service,decode]
  | dataRequest _ =>
    by_cases response : i dataServiceValid = (1#1) <;> simp [service,hp.1,CoreModel.service,decode,response]
  | dataResponse _ =>
    by_cases response : i dataResponseValid = (1#1) <;> simp [service,hp.1,CoreModel.service,decode,response]

theorem service_eq (i : Values Input) (raw : Values Register) (valid : Valid raw) :
    service i raw = CoreModel.service (decode i) (view raw) := by
  obtain ⟨state,_,rep⟩ := valid
  rw [view_of_represents raw state rep]
  exact service_represents i raw state rep

theorem finished_iff (i : Values Input) (raw : Values Register) (valid : Valid raw) :
    finished i raw ↔ CoreModel.finished (decode i) (view raw) := by
  unfold finished
  rw [output_eq i raw valid, output_eq i raw valid]
  change (BitVec.ofBool (CoreInterface.retired (CoreModel.event (decode i) (view raw))) = 1 ∨
    BitVec.ofBool (CoreInterface.trapped (CoreModel.event (decode i) (view raw))).isSome = 1) ↔ _
  cases he : CoreModel.event (decode i) (view raw) with
  | none => simp [CoreModel.finished,he,CoreInterface.retired,CoreInterface.trapped]
  | some event => cases event <;> simp [CoreModel.finished,he,CoreInterface.retired,CoreInterface.trapped]

def progress : Timed.ProgressBound circuit.component (fun i raw => Valid raw ∧ i reset = 0) finished service where
  rank := rank
  step i raw allowed unfinished := by
    change rank (circuit.step i raw) + (if service i raw then 1 else 0) ≤ rank raw
    rw [rank_eq _ (preserved i raw allowed.1), step_eq i raw allowed.1,
      service_eq i raw allowed.1, rank_eq raw allowed.1]
    exact CoreModel.progress_edge (decode i) (view raw)
      (by simp [decode,allowed.2]) (fun finish => unfinished ((finished_iff i raw allowed.1).mpr finish))

theorem valid_legal (raw : Values Register) (valid : Valid raw) (traffic : List (Values Input))
    (legal : circuit.component.Legal (fun i _ => i reset = 0) raw traffic) :
    circuit.component.Legal (fun i raw => Valid raw ∧ i reset = 0) raw traffic := by
  induction traffic generalizing raw with
  | nil => trivial
  | cons i rest ih => exact ⟨⟨valid,legal.1⟩,ih _ (preserved i raw valid) legal.2⟩

/-- More actual service opportunities than the initial rank force an actual
retire/trap port pulse. This does not assume or establish eventual service. -/
theorem completion_of_service (raw : Values Register) (valid : Valid raw) (traffic : List (Values Input))
    (resetLow : circuit.component.Legal (fun i _ => i reset = 0) raw traffic)
    (enough : rank raw < circuit.component.serviceCount service raw traffic) :
    circuit.component.Occurs finished raw traffic :=
  progress.occurs_of_service_count raw traffic (valid_legal raw valid traffic resetLow) enough

theorem rank_le_four (raw : Values Register) : rank raw ≤ 4 := by
  by_cases h0 : raw phase = (0#3)
  · simp [rank,h0]
  by_cases h1 : raw phase = (1#3)
  · simp [rank,h1]
  by_cases h2 : raw phase = (2#3)
  · simp [rank,h2]
  by_cases h3 : raw phase = (3#3) <;> simp [rank,h0,h1,h2,h3]

theorem completion_with_five_services (raw : Values Register) (valid : Valid raw) (traffic : List (Values Input))
    (resetLow : circuit.component.Legal (fun i _ => i reset = 0) raw traffic)
    (enough : 5 ≤ circuit.component.serviceCount service raw traffic) :
    circuit.component.Occurs finished raw traffic :=
  completion_of_service raw valid traffic resetLow (by have := rank_le_four raw; omega)

end Pinwheel.Hardware.Processor.CoreCircuit.Events
