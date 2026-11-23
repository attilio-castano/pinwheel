import Pinwheel.Hardware.Processor.CoreCircuitProgress
import Pinwheel.Hardware.Processor.SystemCircuitEvents

/-! Architectural events of the actual connected core ports, joined with the
actual RAM/MMIO completion extractors. The complete circuit certificate proves
the bus replies used here are the owned RAM/ROM/device replies. Device effects
and architectural completion share their proved atomic/deferred edge; timer
and serial-interface events remain separately observable on every edge.
-/
namespace Pinwheel.Hardware.Processor.SystemCircuit

variable (layout : AddressMap.Layout rw aw) (rom : SystemModel.Rom rw)
  (romFits : rw ≤ 30) (ramFits : aw ≤ 30)

/-- Actual system core ports, with the actual bound input network and raw core
registers. No model event appears in this definition. -/
def coreEvents (i : Values Input) (s : Values (Register aw)) : List CoreModel.Event :=
  CoreCircuit.Events.extract (corePins layout rom romFits ramFits i s) (coreValues s)
    (fun o => (circuit layout rom romFits ramFits).observe i s (.left o))

def architectureEvents (i : Values Input) (s : Values (Register aw)) : SystemModel.Events aw :=
  ⟨coreEvents layout rom romFits ramFits i s, ramEvents layout ramFits i s, mmioEvents layout i s⟩

theorem coreEvents_component (i : Values Input) (s : Values (Register aw)) :
    coreEvents layout rom romFits ramFits i s =
      CoreCircuit.Events.events (corePins layout rom romFits ramFits i s) (coreValues s) := by
  unfold coreEvents CoreCircuit.Events.events
  congr 1
  funext b o
  exact core_output layout rom romFits ramFits i s o

theorem coreEvents_eq (i : Values Input) (s : Values (Register aw)) (h : Valid layout rom s) :
    coreEvents layout rom romFits ramFits i s = (SystemModel.events layout rom (decode i) (view s)).core := by
  rw [coreEvents_component, CoreCircuit.Events.events_eq _ _ h.1]
  rcases BitVec.eq_zero_or_eq_one (i reset) with hr | hr
  · rw [corePins_decode layout rom romFits ramFits i s hr h.1]
    rfl
  · have actual : (CoreInterface.decode (corePins layout rom romFits ramFits i s)).reset = true := by
      simp [CoreInterface.decode, hr]
    simp [SystemModel.events, CoreModel.events, CoreModel.observe, CoreModel.event, CoreModel.tick,
      actual, SystemModel.coreInput, decode, hr]

theorem architectureEvents_eq (i : Values Input) (s : Values (Register aw)) (h : Valid layout rom s) :
    architectureEvents layout rom romFits ramFits i s = SystemModel.events layout rom (decode i) (view s) := by
  unfold architectureEvents
  rw [coreEvents_eq layout rom romFits ramFits i s h, ramEvents_eq layout rom ramFits i s h.1,
    mmioEvents_eq layout rom i s h.1]

def architecturalSnapshot (s : Values (Register aw)) : CoreModel.Architectural :=
  CoreModel.snapshot (view s).core

theorem coreEvents_path (i : Values Input) (s : Values (Register aw)) (h : Valid layout rom s) :
    CoreModel.architecture.Path (architecturalSnapshot s) (coreEvents layout rom romFits ramFits i s)
      (architecturalSnapshot ((circuit layout rom romFits ramFits).step i s)) := by
  rw [coreEvents_eq layout rom romFits ramFits i s h]
  unfold architecturalSnapshot
  rw [view_step layout rom romFits ramFits i s h]
  exact SystemModel.core_edge_path layout rom (decode i) (view s) h.2

def architecturalRefinement : Timed.EventRefinement (circuit layout rom romFits ramFits).component
    CoreModel.architecture (coreEvents layout rom romFits ramFits) (fun _ _ => True) where
  Rel raw logical := Valid layout rom raw ∧ architecturalSnapshot raw = logical
  edge i raw logical related _ := by
    rcases related with ⟨valid,rfl⟩
    exact ⟨architecturalSnapshot ((circuit layout rom romFits ramFits).step i raw),
      coreEvents_path layout rom romFits ramFits i raw valid,
      preserved layout rom romFits ramFits i raw valid, rfl⟩

theorem architecture_trace_path (s : Values (Register aw)) (h : Valid layout rom s)
    (traffic : List (Values Input)) :
    CoreModel.architecture.Path (architecturalSnapshot s)
      ((circuit layout rom romFits ramFits).component.eventTrace (coreEvents layout rom romFits ramFits) s traffic)
      (architecturalSnapshot ((circuit layout rom romFits ramFits).component.run s traffic)) := by
  induction traffic generalizing s with
  | nil => exact .nil _
  | cons i rest ih =>
    exact (coreEvents_path layout rom romFits ramFits i s h).append
      (ih _ (preserved layout rom romFits ramFits i s h))

theorem architecture_trace_replay (s : Values (Register aw)) (h : Valid layout rom s)
    (traffic : List (Values Input)) :
    CoreModel.replay (architecturalSnapshot s)
      ((circuit layout rom romFits ramFits).component.eventTrace (coreEvents layout rom romFits ramFits) s traffic) =
      architecturalSnapshot ((circuit layout rom romFits ramFits).component.run s traffic) :=
  CoreModel.path_replay _ _ _ (architecture_trace_path layout rom romFits ramFits s h traffic)

/-- The actual RAM completion and architectural completion occur together,
with data obtained from the owned pre-edge RAM word, not a free reply value. -/
theorem ram_architectural_completion (i : Values Input) (s : Values (Register aw))
    (valid : Valid layout rom s) (resetLow : i reset = 0)
    (request : CoreModel.DataRequest) (phase : (view s).core.phase = .dataResponse request) :
    ∃ physical, SystemModel.plan layout rom request.intent = .ram physical ∧
      ramEvents layout ramFits i s =
        [⟨physical, physical.response ((view s).ram.memory.contents physical.address)⟩] ∧
      ((view ((circuit layout rom romFits ramFits).step i s)).core, coreEvents layout rom romFits ramFits i s) =
        let action := CoreModel.acceptOutcome (view s).core
          (.data .deferred request.intent (SystemModel.ramReply (physical.response ((view s).ram.memory.contents physical.address))))
          (request.finish (SystemModel.ramReply (physical.response ((view s).ram.memory.contents physical.address))))
        (action.1, action.2.toList) := by
  obtain ⟨physical,route,_,ramEvent,coreEvent⟩ := SystemModel.ram_completion layout rom (decode i) (view s)
    valid.2 (by simp [decode,resetLow]) request phase
  refine ⟨physical,route,?_,?_⟩
  · rw [ramEvents_eq layout rom ramFits i s valid.1]
    exact ramEvent
  · rw [view_step layout rom romFits ramFits i s valid, coreEvents_eq layout rom romFits ramFits i s valid]
    exact congrArg (fun pair : CoreModel.State × Option CoreModel.Event => (pair.1,pair.2.toList)) coreEvent

/-- Actual atomic MMIO response, CPU completion and device CPU-effect share
one edge. Independent autonomous events follow in their specified order. -/
theorem mmio_architectural_completion (i : Values Input) (s : Values (Register aw))
    (valid : Valid layout rom s) (resetLow : i reset = 0)
    (request : CoreModel.DataRequest) (physical : MmioModel.Request)
    (phase : (view s).core.phase = .dataRequest request)
    (route : SystemModel.plan layout rom request.intent = .mmio physical) :
    let response := (MmioModel.access (decode i).gpio physical (view s).mmio).1
    ((view ((circuit layout rom romFits ramFits).step i s)).core, coreEvents layout rom romFits ramFits i s) =
      (let action := CoreModel.acceptOutcome (view s).core
        (.data .atomic request.intent (SystemModel.mmioReply response)) (request.finish (SystemModel.mmioReply response))
       (action.1,action.2.toList)) ∧
    (view ((circuit layout rom romFits ramFits).step i s)).mmio =
      MmioModel.autonomous (SystemModel.mmioInput layout rom (decode i) (view s)) (view s).mmio
        (MmioModel.access (decode i).gpio physical (view s).mmio).2 ∧
    mmioEvents layout i s = .cpu physical (decode i).gpio response ::
      MmioModel.autonomousEvents (SystemModel.mmioInput layout rom (decode i) (view s)) (view s).mmio
        (MmioModel.access (decode i).gpio physical (view s).mmio).2 := by
  obtain ⟨coreEvent,device,events⟩ := SystemModel.mmio_completion layout rom (decode i) (view s)
    (by simp [decode,resetLow]) request physical phase route
  refine ⟨?_,?_,?_⟩
  · rw [view_step layout rom romFits ramFits i s valid, coreEvents_eq layout rom romFits ramFits i s valid]
    exact congrArg (fun pair : CoreModel.State × Option CoreModel.Event => (pair.1,pair.2.toList)) coreEvent
  · rw [view_step layout rom romFits ramFits i s valid]
    exact device
  · rw [mmioEvents_eq layout rom i s valid.1]
    exact events

/-- Core rank/service are evaluated from actual connected inputs and registers.
Autonomous MMIO events never count as architectural service. -/
def architecturalRank (s : Values (Register aw)) : Nat := CoreCircuit.Events.rank (coreValues s)
def architecturalService (i : Values Input) (s : Values (Register aw)) : Bool :=
  CoreCircuit.Events.service (corePins layout rom romFits ramFits i s) (coreValues s)
def architecturalFinished (i : Values Input) (s : Values (Register aw)) : Prop :=
  (circuit layout rom romFits ramFits).observe i s (.left CoreInterface.retireValid) = 1 ∨
    (circuit layout rom romFits ramFits).observe i s (.left CoreInterface.trapValid) = 1

def architecturalProgress : Timed.ProgressBound (circuit layout rom romFits ramFits).component
    (fun i s => Valid layout rom s ∧ i reset = 0) (architecturalFinished layout rom romFits ramFits)
    (architecturalService layout rom romFits ramFits) where
  rank := architecturalRank
  step i s allowed unfinished := by
    change CoreCircuit.Events.rank (coreValues ((circuit layout rom romFits ramFits).step i s)) +
      (if architecturalService layout rom romFits ramFits i s then 1 else 0) ≤ CoreCircuit.Events.rank (coreValues s)
    rw [core_step]
    apply CoreCircuit.Events.progress.step
    · exact ⟨allowed.1.1, by simpa using allowed.2⟩
    · intro finished
      apply unfinished
      simpa only [architecturalFinished, core_output, CoreCircuit.Events.finished] using finished

theorem architectural_valid_legal (s : Values (Register aw)) (valid : Valid layout rom s)
    (traffic : List (Values Input))
    (legal : (circuit layout rom romFits ramFits).component.Legal (fun i _ => i reset = 0) s traffic) :
    (circuit layout rom romFits ramFits).component.Legal (fun i s => Valid layout rom s ∧ i reset = 0) s traffic := by
  induction traffic generalizing s with
  | nil => trivial
  | cons i rest ih => exact ⟨⟨valid,legal.1⟩,ih _ (preserved layout rom romFits ramFits i s valid) legal.2⟩

theorem architectural_completion_of_service (s : Values (Register aw)) (valid : Valid layout rom s)
    (traffic : List (Values Input))
    (resetLow : (circuit layout rom romFits ramFits).component.Legal (fun i _ => i reset = 0) s traffic)
    (enough : architecturalRank s < (circuit layout rom romFits ramFits).component.serviceCount
      (architecturalService layout rom romFits ramFits) s traffic) :
    (circuit layout rom romFits ramFits).component.Occurs (architecturalFinished layout rom romFits ramFits) s traffic :=
  (architecturalProgress layout rom romFits ramFits).occurs_of_service_count s traffic
    (architectural_valid_legal layout rom romFits ramFits s valid traffic resetLow) enough

def coreEnteredWords (i : Values Input) (s : Values (Register aw)) : List RV32I.Word :=
  let pins : Values CoreInterface.Input := corePins layout rom romFits ramFits i s
  if (circuit layout rom romFits ramFits).observe i s (.left CoreInterface.fetchResponseReady) = 1 ∧
    pins CoreInterface.fetchResponseValid = 1 ∧ pins CoreInterface.fetchResponseFault = 0
  then [pins CoreInterface.fetchResponseData] else []

def coreExitedWords (i : Values Input) (s : Values (Register aw)) : List RV32I.Word :=
  if (circuit layout rom romFits ramFits).observe i s (.left CoreInterface.cancel) = 1 then
    (CoreCircuit.Events.heldWord (coreValues s)).toList
  else (coreEvents layout rom romFits ramFits i s).flatMap (fun event => (CoreModel.finishedWord (some event)).toList)

theorem coreEnteredWords_component (i : Values Input) (s : Values (Register aw)) :
    coreEnteredWords layout rom romFits ramFits i s =
      CoreCircuit.Events.enteredWords (corePins layout rom romFits ramFits i s) (coreValues s) := by
  simp only [coreEnteredWords,CoreCircuit.Events.enteredWords,core_output]

theorem coreExitedWords_component (i : Values Input) (s : Values (Register aw)) :
    coreExitedWords layout rom romFits ramFits i s =
      CoreCircuit.Events.exitedWords (corePins layout rom romFits ramFits i s) (coreValues s) := by
  simp only [coreExitedWords,CoreCircuit.Events.exitedWords,core_output,coreEvents_component]

theorem architectural_word_edge (i : Values Input) (s : Values (Register aw)) (valid : Valid layout rom s) :
    coreExitedWords layout rom romFits ramFits i s ++
      (CoreCircuit.Events.heldWord (coreValues ((circuit layout rom romFits ramFits).step i s))).toList =
      (CoreCircuit.Events.heldWord (coreValues s)).toList ++ coreEnteredWords layout rom romFits ramFits i s := by
  rw [coreExitedWords_component,coreEnteredWords_component,core_step]
  exact CoreCircuit.Events.word_edge _ _ valid.1

theorem architectural_word_conservation (s : Values (Register aw)) (valid : Valid layout rom s)
    (traffic : List (Values Input)) :
    (circuit layout rom romFits ramFits).component.eventTrace (coreExitedWords layout rom romFits ramFits) s traffic ++
      (CoreCircuit.Events.heldWord (coreValues ((circuit layout rom romFits ramFits).component.run s traffic))).toList =
      (CoreCircuit.Events.heldWord (coreValues s)).toList ++
        (circuit layout rom romFits ramFits).component.eventTrace (coreEnteredWords layout rom romFits ramFits) s traffic := by
  induction traffic generalizing s with
  | nil => simp [Timed.Component.eventTrace,Timed.Component.run]
  | cons i rest ih =>
    change (coreExitedWords layout rom romFits ramFits i s ++
      (circuit layout rom romFits ramFits).component.eventTrace (coreExitedWords layout rom romFits ramFits)
        ((circuit layout rom romFits ramFits).step i s) rest) ++
      (CoreCircuit.Events.heldWord (coreValues ((circuit layout rom romFits ramFits).component.run
        ((circuit layout rom romFits ramFits).step i s) rest))).toList =
      (CoreCircuit.Events.heldWord (coreValues s)).toList ++
        (coreEnteredWords layout rom romFits ramFits i s ++
          (circuit layout rom romFits ramFits).component.eventTrace (coreEnteredWords layout rom romFits ramFits)
            ((circuit layout rom romFits ramFits).step i s) rest)
    rw [List.append_assoc, ih _ (preserved layout rom romFits ramFits i s valid), ← List.append_assoc,
      architectural_word_edge layout rom romFits ramFits i s valid, List.append_assoc]

theorem architecturalInitialCoverage :
    (architecturalRefinement layout rom romFits ramFits).InitialCoverage (Valid layout rom) (fun _ => True) where
  nonempty := ⟨encode (SystemModel.initial (fun _ => 0) 0) (fun _ => 0) (fun _ => 0),
    valid_encode layout rom _ (SystemModel.initial_valid _ _ _ _) _ _⟩
  covered s valid := ⟨architecturalSnapshot s,trivial,valid,rfl⟩

theorem architectural_logical_coverage (state : SystemModel.State aw) (valid : SystemModel.Valid layout rom state)
    (ramInactive : Values (Memory.ByteAdapterCircuit.Metadata aw)) (fetchInactive : Values Fetch) :
    ∃ raw : Values (Register aw), Valid layout rom raw ∧ architecturalSnapshot raw = CoreModel.snapshot state.core := by
  refine ⟨encode state ramInactive fetchInactive, valid_encode layout rom state valid _ _, ?_⟩
  simp only [architecturalSnapshot,view_encode state valid.core]

theorem architectural_trace_after_reset (i : Values Input) (s : Values (Register aw)) (resetHigh : i reset = 1)
    (traffic : List (Values Input)) :
    CoreModel.architecture.Path (CoreModel.snapshot CoreModel.initial)
      ((circuit layout rom romFits ramFits).component.eventTrace (coreEvents layout rom romFits ramFits)
        ((circuit layout rom romFits ramFits).step i s) traffic)
      (architecturalSnapshot ((circuit layout rom romFits ramFits).component.run
        ((circuit layout rom romFits ramFits).step i s) traffic)) := by
  have result := architecture_trace_path layout rom romFits ramFits
    ((circuit layout rom romFits ramFits).step i s) (reset_valid layout rom romFits ramFits i s resetHigh) traffic
  simpa only [architecturalSnapshot,reset_view layout rom romFits ramFits i s resetHigh,resetState,SystemModel.initial] using result

variable {rtl : Timed.Component (Values Input) (Values (Register aw)) (Values Output)}

/-- Imported architectural events read actual imported core outputs. Completion
provenance uses retained raw state and the proved connected provider network;
all raw endpoints must be covered by the supplied correspondence. -/
def artifactCoreEvents (rtl : Timed.Component (Values Input) (Values (Register aw)) (Values Output))
    (i : Values Input) (s : Values (Register aw)) : List CoreModel.Event :=
  CoreCircuit.Events.extract (corePins layout rom romFits ramFits i s) (coreValues s)
    (fun o => rtl.observe i s (.left o))

theorem artifact_core_trace_eq (artifact : Artifact.Correspondence (circuit layout rom romFits ramFits) rtl)
    (s : Values (Register aw)) (traffic : List (Values Input)) :
    rtl.eventTrace (artifactCoreEvents layout rom romFits ramFits rtl) s traffic =
      (circuit layout rom romFits ramFits).component.eventTrace (coreEvents layout rom romFits ramFits) s traffic := by
  induction traffic generalizing s with
  | nil => rfl
  | cons i rest ih =>
    change artifactCoreEvents layout rom romFits ramFits rtl i s ++
      rtl.eventTrace (artifactCoreEvents layout rom romFits ramFits rtl) (rtl.step i s) rest = _
    simp only [artifactCoreEvents,artifact.output_eq,artifact.step_eq,ih]
    rfl

theorem artifact_architecture_trace_path (artifact : Artifact.Correspondence (circuit layout rom romFits ramFits) rtl)
    (s : Values (Register aw)) (valid : Valid layout rom s) (traffic : List (Values Input)) :
    CoreModel.architecture.Path (architecturalSnapshot s)
      (rtl.eventTrace (artifactCoreEvents layout rom romFits ramFits rtl) s traffic)
      (architecturalSnapshot (rtl.run s traffic)) := by
  rw [artifact_core_trace_eq layout rom romFits ramFits artifact, artifact.run_eq]
  exact architecture_trace_path layout rom romFits ramFits s valid traffic

theorem artifact_architecture_trace_replay (artifact : Artifact.Correspondence (circuit layout rom romFits ramFits) rtl)
    (s : Values (Register aw)) (valid : Valid layout rom s) (traffic : List (Values Input)) :
    CoreModel.replay (architecturalSnapshot s)
      (rtl.eventTrace (artifactCoreEvents layout rom romFits ramFits rtl) s traffic) = architecturalSnapshot (rtl.run s traffic) :=
  CoreModel.path_replay _ _ _ (artifact_architecture_trace_path layout rom romFits ramFits artifact s valid traffic)

/-- Reset has priority for every raw register pattern. There is no CPU
retirement, RAM completion/store, or MMIO CPU operation on the reset edge. -/
theorem reset_architectureEvents (i : Values Input) (s : Values (Register aw)) (resetHigh : i reset = 1) :
    (architectureEvents layout rom romFits ramFits i s).core = [.reset] ∧
    (architectureEvents layout rom romFits ramFits i s).ram = [] ∧
    (architectureEvents layout rom romFits ramFits i s).mmio = [.reset] := by
  refine ⟨?_,?_,?_⟩
  · change coreEvents layout rom romFits ramFits i s = _
    rw [coreEvents_component]
    exact CoreCircuit.Events.reset_events _ _ (by simpa using resetHigh)
  · change ramEvents layout ramFits i s = _
    unfold ramEvents
    rw [Memory.ByteAdapterRefinement.events_eq]
    simp [Memory.ByteAdapterEffects.events,Memory.ByteAdapterModel.completedRequests,
      Memory.ByteAdapterInterface.decode,resetHigh]
  · change mmioEvents layout i s = _
    simp [mmioEvents,MmioCircuit.physicalEvents,MmioInterface.decode,resetHigh]

theorem architectural_no_event_no_update (i : Values Input) (s : Values (Register aw))
    (valid : Valid layout rom s) (silent : coreEvents layout rom romFits ramFits i s = []) :
    architecturalSnapshot ((circuit layout rom romFits ramFits).step i s) = architecturalSnapshot s := by
  have path := coreEvents_path layout rom romFits ramFits i s valid
  rw [silent] at path
  exact (Timed.EventSpec.Path.nil_iff.mp path).symm

theorem artifact_architecture_after_reset (artifact : Artifact.Correspondence (circuit layout rom romFits ramFits) rtl)
    (i : Values Input) (s : Values (Register aw)) (resetHigh : i reset = 1) (traffic : List (Values Input)) :
    CoreModel.architecture.Path (CoreModel.snapshot CoreModel.initial)
      (rtl.eventTrace (artifactCoreEvents layout rom romFits ramFits rtl) (rtl.step i s) traffic)
      (architecturalSnapshot (rtl.run (rtl.step i s) traffic)) := by
  rw [artifact_core_trace_eq layout rom romFits ramFits artifact,artifact.run_eq,artifact.step_eq]
  exact architectural_trace_after_reset layout rom romFits ramFits i s resetHigh traffic

end Pinwheel.Hardware.Processor.SystemCircuit
