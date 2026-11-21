import Lean
import Pinwheel.Hardware.Timed.Events
import Pinwheel.Hardware.Memory.TransferModel

open Lean Elab Command
open Pinwheel.Hardware
open Pinwheel.Hardware.Timed

namespace HardwareEventRefinementTests

structure Counter where
  value : Nat
  pending : Bool
  deriving DecidableEq, Repr

/-- Two enabled edges per event; disabled edges and the first enabled edge
are genuine abstract stutters. -/
def counter : Component Bool Counter (Option Nat) where
  step enabled s :=
    if enabled then
      if s.pending then ⟨s.value+1, false⟩ else ⟨s.value, true⟩
    else s
  observe enabled s := if enabled && s.pending then some (s.value+1) else none

def counterSpec : EventSpec Nat Nat := ⟨fun a event b => event = a+1 ∧ b = event⟩
def counterEvents (enabled : Bool) (s : Counter) : List Nat :=
  (counter.observe enabled s).toList
def unrestricted (_ : Bool) (_ : Counter) : Prop := True

def counterRefinement : EventRefinement counter counterSpec counterEvents unrestricted where
  Rel s a := s.value = a
  edge := by
    intro enabled s a h _
    subst a
    cases enabled <;> cases hp : s.pending
    all_goals simp [counterEvents, counter, hp]
    · exact .nil _
    · exact .nil _
    · exact .nil _
    · exact .cons ⟨rfl, rfl⟩ (.nil _)

theorem counterCoverage : counterRefinement.InitialCoverage
    (fun s => s = ⟨0, false⟩) (fun a => a = 0) where
  nonempty := ⟨⟨0, false⟩, rfl⟩
  covered := by
    intro s h
    cases h
    exact ⟨0, rfl, rfl⟩

def wrappedCounter : Component Bool (Counter × Unit) (Option Nat) where
  step enabled s := (counter.step enabled s.1, ())
  observe enabled s := counter.observe enabled s.1

def wrappedRefinement : Refinement wrappedCounter counter where
  Rel s t := s.1 = t
  step := by intro i s t h; cases h; rfl
  observe := by intro i s t h; cases h; rfl

def wrappedEvents (i : Bool) (s : Counter × Unit) : List Nat :=
  (wrappedCounter.observe i s).toList

def wrappedEventRefinement : EventRefinement wrappedCounter counterSpec wrappedEvents
    (fun _ _ => True) :=
  counterRefinement.ofLockstep wrappedRefinement wrappedEvents (fun _ _ => True)
    (fun i s t h => wrappedRefinement.port_events (fun _ o => o.toList) i s t h)
    (fun _ _ _ _ _ => True.intro)

def counterProgress : ProgressBound counter unrestricted
    (fun enabled s => enabled = true ∧ s.pending = true) (fun enabled _ => enabled) where
  rank s := if s.pending then 0 else 1
  step := by
    intro enabled s _ hn
    cases enabled <;> cases hp : s.pending <;> simp_all [counter]

example (s : Counter) (inputs : List Bool) (legal : counter.Legal unrestricted s inputs)
    (enough : counterProgress.rank s < counter.serviceCount (fun enabled _ => enabled) s inputs) :
    counter.Occurs (fun enabled s => enabled = true ∧ s.pending = true) s inputs :=
  counterProgress.occurs_of_service_count s inputs legal enough

namespace Transfer
open Memory

structure View (a wi wo : Nat) where
  source : Contents a wi
  destination : Contents a wo

inductive Event (a wi wo : Nat) where
  | read (address : BitVec a) (sample : BitVec wi)
  | write (address : BitVec a) (data : BitVec wo)
  | abort
  | complete (count : Nat)
  deriving DecidableEq, Repr

def view (s : TransferModel.State a wi wo) : View a wi wo :=
  ⟨s.source.memory.contents, s.destination.memory.contents⟩

/-- Read samples are checked against the source snapshot. Writes change the
destination at their actual acceptance edge. Abort and completion are trace
markers, not claims that memory was rolled back or that a job was correct;
the latter remains the separate TransferModel.Session/completed_patch result. -/
def interpret (s : View a wi wo) : Event a wi wo → Option (View a wi wo)
  | .read address sample => if s.source address = sample then some s else none
  | .write address data => some { s with destination := s.destination.write ⟨true, address, data⟩ }
  | .abort => some s
  | .complete _ => some s

def spec (a wi wo : Nat) : EventSpec (View a wi wo) (Event a wi wo) :=
  ⟨fun s event next => interpret s event = some next⟩

/-- Extract actual accepted memory requests and post-edge status. Offers that
are blocked, or canceled by reset, do not become read/write events. -/
def events (m : Stream.Map wi wo) (i : TransferModel.HostInput a) (s : TransferModel.State a wi wo) :
    List (Event a wi wo) :=
  let reads := (StreamModel.acceptedRequests (TransferModel.sourceInput m i s) s.source).filterMap
    (fun r => match r with
      | .read address => some (.read address (s.source.memory.contents address))
      | .write _ _ => none)
  let writes := (StreamModel.acceptedRequests (TransferModel.destinationInput m i s) s.destination).filterMap
    (fun r => match r with
      | .write address data => some (.write address data)
      | .read _ => none)
  reads ++ writes ++ (if i.reset then [.abort] else []) ++
    (if !i.reset && (TransferModel.closedStep m i s).control.done then
      [.complete (TransferModel.closedStep m i s).control.index] else [])

def replay (s : View a wi wo) : List (Event a wi wo) → Option (View a wi wo)
  | [] => some s
  | event :: rest => (interpret s event).bind (fun next => replay next rest)

theorem replay_path (s t : View a wi wo) (es : List (Event a wi wo))
    (h : replay s es = some t) : (spec a wi wo).Path s es t := by
  induction es generalizing s with
  | nil => cases h; exact .nil _
  | cons event rest ih =>
    cases he : interpret s event with
    | none => simp [replay, he] at h
    | some next =>
      exact .cons he (ih next (by simpa [replay, he] using h))

theorem replay_complete_if (s : View a wi wo) (condition : Prop) [Decidable condition] (n : Nat) :
    replay s (if condition then [.complete n] else []) = some s := by
  split <;> rfl

theorem event_effects (m : Stream.Map wi wo) (i : TransferModel.HostInput a)
    (s : TransferModel.State a wi wo) :
    replay (view s) (events m i s) = some (view (TransferModel.closedStep m i s)) := by
  cases hr : i.reset
  · cases hp : s.control.phase <;> cases hs : s.source.pending
    all_goals simp [events, StreamModel.acceptedRequests, Stream.accepted, StreamModel.component,
      StreamModel.machine, Stream.Machine.component, TransferModel.sourceInput,
      TransferModel.destinationInput, TransferModel.observe, TransferModel.feedback,
      TransferModel.closedStep, TransferModel.step, StreamModel.ready, StreamModel.offer,
      StreamModel.step, StreamModel.command, StreamModel.Request.command,
      StreamModel.Request.isRead, SinglePort.step, Sram.State.step, hr, hp, hs,
      replay, interpret, view, replay_complete_if]
  · simp [events, StreamModel.acceptedRequests, Stream.accepted, TransferModel.sourceInput,
      TransferModel.destinationInput, TransferModel.observe, TransferModel.feedback,
      hr, TransferModel.reset_state m i s hr, TransferModel.initialState, replay,
      interpret, view]

def refinement (m : Stream.Map wi wo) : EventRefinement (TransferModel.component m)
    (spec a wi wo) (events m) (fun _ _ => True) where
  Rel s a := view s = a
  edge := by
    intro i s a h _
    subst a
    exact ⟨view (TransferModel.closedStep m i s),
      replay_path _ _ _ (event_effects m i s), rfl⟩

theorem coverage (m : Stream.Map wi wo) (seed : TransferModel.State a wi wo) :
    (refinement (a := a) m).InitialCoverage (fun _ => True) (fun _ => True) where
  nonempty := ⟨seed, True.intro⟩
  covered s _ := ⟨view s, True.intro, rfl⟩

theorem allLegal (c : Component I S O) (s : S) (inputs : List I) :
    c.Legal (fun _ _ => True) s inputs := by
  induction inputs generalizing s with
  | nil => trivial
  | cons i rest ih => exact ⟨True.intro, ih _⟩

theorem trace_effects (m : Stream.Map wi wo) (s : TransferModel.State a wi wo)
    (inputs : List (TransferModel.HostInput a)) :
    ∃ next, (spec a wi wo).Path (view s)
        ((TransferModel.component m).eventTrace (events m) s inputs) next ∧
      view ((TransferModel.component m).run s inputs) = next :=
  (refinement m).trace s (view s) inputs rfl (allLegal _ _ _)

def inversion (w : Nat) : Stream.Map w w :=
  ⟨.inv (.input .data), fun value => ~~~value, fun _ => rfl⟩

def values (a : Nat) (contents : Contents a w) : Array Nat :=
  (Array.range (2^a)).map (fun k => (contents (BitVec.ofNat a k)).toNat)

def sameView (a : Nat) (left right : View a wi wo) : Bool :=
  values a left.source == values a right.source &&
    values a left.destination == values a right.destination

def runChecked (a : Nat) (m : Stream.Map wi wo) (initial : TransferModel.State a wi wo)
    (inputs : List (TransferModel.HostInput a)) : IO (List (Event a wi wo) × Nat) := do
  let mut physical := initial
  let mut abstract := view initial
  let mut trace := []
  let mut edges := 0
  for i in inputs do
    let emitted := events m i physical
    physical := TransferModel.closedStep m i physical
    match replay abstract emitted with
    | none => throw (IO.userError "transfer emitted a read inconsistent with its source snapshot")
    | some next => abstract := next
    unless sameView a abstract (view physical) do
      throw (IO.userError s!"edge {edges}: events do not reconstruct the actual memory effects")
    trace := trace ++ emitted
    edges := edges+1
  return (trace, edges)

def commandMatrix (a w : Nat) : IO Nat := do
  let m := inversion w
  let mut edges := 0
  for sourceSeed in [0:3] do
    for destinationSeed in [0:2] do
      let source : Contents a w := fun address => BitVec.ofNat w (sourceSeed+address.toNat*7)
      let destination : Contents a w := fun address => BitVec.ofNat w (destinationSeed+address.toNat*13)
      let initial := TransferModel.initialState
        (⟨source, BitVec.ofNat w 91⟩ : Sram.State a w)
        (⟨destination, BitVec.ofNat w 201⟩ : Sram.State a w)
      for sourceBase in [0:2^a] do
        for destinationBase in [0:2^a] do
          for length in [0:2^(a+1)] do
            let command : TransferModel.RawCommand a :=
              ⟨BitVec.ofNat a sourceBase, BitVec.ofNat a destinationBase, BitVec.ofNat (a+1) length⟩
            let valid := length ≤ 2^a-sourceBase && length ≤ 2^a-destinationBase
            let (actual, count) ← runChecked a m initial
              (⟨false, some command⟩ :: List.replicate (if valid then 2*length+2 else 2) TransferModel.quiet)
            let expected : List (Event a w w) := if valid then
              (List.range length).flatMap (fun k =>
                let address := BitVec.ofNat a (sourceBase+k)
                [.read address (source address),
                  .write (BitVec.ofNat a (destinationBase+k))
                    (BitVec.ofNat w ((2^w-1)-(source address).toNat))]) ++ [.complete length]
              else []
            unless decide (actual = expected) do
              throw (IO.userError s!"command {sourceBase}/{destinationBase}/{length}: wrong event trace")
            edges := edges+count
  return edges

def abortChecks : IO Nat := do
  let source : Contents 2 8 := fun address => BitVec.ofNat 8 (17+address.toNat*11)
  let destination : Contents 2 8 := fun address => BitVec.ofNat 8 (91+address.toNat*9)
  let initial := TransferModel.initialState
    (⟨source, 199⟩ : Sram.State 2 8) (⟨destination, 233⟩ : Sram.State 2 8)
  let m := inversion 8
  let command : TransferModel.RawCommand 2 := ⟨0, 0, 4⟩
  let normal : List (Event 2 8 8) := (List.range 4).flatMap (fun k =>
    [.read (BitVec.ofNat 2 k) (source (BitVec.ofNat 2 k)),
      .write (BitVec.ofNat 2 k) (BitVec.ofNat 8 (255-(source (BitVec.ofNat 2 k)).toNat))])
  let mut edges := 0
  for cut in [0:9] do
    let (actual, count) ← runChecked 2 m initial
      ([⟨false, some command⟩] ++ List.replicate cut TransferModel.quiet ++
        [⟨true, some command⟩, TransferModel.quiet, TransferModel.quiet])
    let expected := normal.take cut ++ (if cut == 8 then [.complete 4] else []) ++ [.abort]
    unless decide (actual = expected) do
      throw (IO.userError s!"reset after {cut} edges lost an effect, invented retirement, or leaked stale work")
    edges := edges+count
  -- These controls exercise the independent interpreter, not a reflexive
  -- comparison between two uses of the same event extractor.
  unless (replay (view initial) [.read 0 18]).isNone do
    throw (IO.userError "negative control: corrupted read sample was accepted")
  let good ← match replay (view initial) [.write 0 238] with
    | some state => pure state
    | none => throw (IO.userError "valid write unexpectedly rejected")
  let bad ← match replay (view initial) [.write 0 239] with
    | some state => pure state
    | none => throw (IO.userError "write mutation unexpectedly rejected before comparison")
  if sameView 2 good bad || sameView 2 good (view initial) then
    throw (IO.userError "negative control: mutated or dropped write was invisible")
  return edges

end Transfer

example : ¬ counterSpec.Path 0 [] 1 := by
  simp [EventSpec.Path.nil_iff]

/-- A permanently stalled implementation can have a safety relation, but it
cannot claim this always-serviced progress contract. -/
theorem stuck_has_no_progress :
    ¬ Nonempty (ProgressBound (⟨fun (_ : Unit) (s : Nat) => s, fun _ s => s⟩ : Component Unit Nat Nat)
      (fun _ _ => True) (fun _ _ => False) (fun _ _ => true)) := by
  intro ⟨p⟩
  have h := p.step () 0 True.intro (fun h => h)
  simp only [↓reduceIte] at h
  omega

def counterChecks : IO Nat := do
  let mut count : Nat := 0
  for size in [0:10] do
    for bits in [0:2^size] do
      let inputs := (List.range size).map (fun k => bits / 2^k % 2 == 1)
      for initialPending in [false, true] do
        let initial : Counter := ⟨7, initialPending⟩
        let mut expectedValue := 7
        let mut pending := initialPending
        let mut expected := []
        for enabled in inputs do
          if enabled then
            if pending then
              expectedValue := expectedValue+1
              expected := expected ++ [expectedValue]
            pending := !pending
        unless counter.eventTrace counterEvents initial inputs == expected &&
            wrappedCounter.eventTrace wrappedEvents (initial, ()) inputs == expected &&
            decide (counter.run initial inputs = ⟨expectedValue, pending⟩) do
          throw (IO.userError "stuttering counter or lockstep event transport mismatch")
        count := count+1
  return count

end HardwareEventRefinementTests

elab "#audit_event_refinement" : command => do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let selected := name.toString.startsWith "Pinwheel.Hardware.Timed.EventSpec" ||
      name.toString.startsWith "Pinwheel.Hardware.Timed.EventRefinement" ||
      name.toString.startsWith "Pinwheel.Hardware.Timed.ProgressBound" ||
      name.toString.startsWith "Pinwheel.Hardware.Timed.Component.eventTrace" ||
      name.toString.startsWith "Pinwheel.Hardware.Timed.Component.Legal" ||
      name.toString.startsWith "Pinwheel.Hardware.Timed.Component.serviceCount" ||
      name.toString.startsWith "Pinwheel.Hardware.Timed.Component.Occurs" ||
      name.toString.startsWith "Pinwheel.Hardware.Timed.Refinement.port_events" ||
      name.toString.startsWith "HardwareEventRefinementTests." ||
      name.toString.startsWith "_private.Pinwheel.Hardware.Timed.Events." ||
      name.toString.startsWith "_private.test.HardwareEventRefinement."
    if selected then
      count := count+1
      let axioms ← collectAxioms name
      let bad := axioms.filter fun a => a != ``propext && a != ``Classical.choice && a != ``Quot.sound
      unless bad.isEmpty do throwError "Unapproved axioms in {name}: {bad}"
  if count == 0 then throwError "Empty event-refinement audit"
  logInfo m!"Event refinement audit: {count} declarations, standard axioms only."

#audit_event_refinement

def main : IO Unit := do
  let counters ← HardwareEventRefinementTests.counterChecks
  let mut edges := 0
  for (a, w) in [(0, 0), (1, 2), (2, 8)] do
    edges := edges + (← HardwareEventRefinementTests.Transfer.commandMatrix a w)
  let aborts ← HardwareEventRefinementTests.Transfer.abortChecks
  IO.println s!"Event refinement: {counters} stuttering/lockstep traces, {edges} transfer-command edges, {aborts} reset/prefix edges; read/write/abort/completion event oracle and three mutation controls passed."
