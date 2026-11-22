import Pinwheel.Hardware.StreamingReady.I2CReadSuccess

/-! Feedback through the public pads. Each package and environment take
    their next step from the observation made by their own execution. -/
namespace Pinwheel.Hardware.StreamingReady.CausalSession

open Pinwheel.Program Pinwheel.Program.StreamingReady

structure Backend (S : Type) where
  step : S → Session.Pins → S
  observe : S → Session.Pins → TinyWiring.Pad → BitVec 8

/-- Read the protocol drive with the public package enabled. The sampled
    edge also records the pads at the supplied input, including reset. -/
def Backend.drive (backend : Backend S) (state : S) : Pins :=
  let pads := backend.observe state {}
  ⟨(pads .uio).extractLsb' 0 3, (pads .oe).extractLsb' 0 3⟩

def canonical (a : Nat) : Backend (Package.State a) where
  step := PublicPins.step
  observe state pins := (TinyWiring.canonical a).observe (Wiring.canonical a)
    (Package.Components.typed a) state (PublicPins.embed pins)

structure Environment (E : Type) where
  inputs : E → Pins → Session.Pins
  advance : E → Session.Pins → (TinyWiring.Pad → BitVec 8) → E

/-- The host supplies its command pins. SCL and SDA come exclusively from
    resolving the current public drive with the target's current drive. -/
def openDrain (host : E → Session.Pins) (target : E → Pinwheel.I2C.Pins)
    (advance : E → BitVec 2 → (TinyWiring.Pad → BitVec 8) → E) : Environment E where
  inputs env drive := { host env with rawInputs := StreamingI2CRead.resolvedRaw drive (target env) }
  advance env pins pads := advance env pins.rawInputs pads

structure Edge (E : Type) where
  environment : E
  input : Session.Pins
  drive : Pins
  pads : TinyWiring.Pad → BitVec 8

def Backend.sample (backend : Backend S) (env : Environment E) (state : S) (before : E) : Edge E :=
  let drive := backend.drive state
  let input := env.inputs before drive
  ⟨before, input, drive, backend.observe state input⟩

structure Execution (S E : Type) where
  final : S
  environment : E
  edges : List (Edge E)

def Backend.run (backend : Backend S) (env : Environment E) (state : S) (before : E) : Nat → Execution S E
  | 0 => ⟨state, before, []⟩
  | n + 1 =>
    let edge := backend.sample env state before
    let tail := backend.run env (backend.step state edge.input) (env.advance before edge.input edge.pads) n
    ⟨tail.final, tail.environment, edge :: tail.edges⟩

def Backend.atEdge (backend : Backend S) (env : Environment E) (state : S) (before : E) (k : Nat) : Edge E :=
  let cut := backend.run env state before k
  backend.sample env cut.final cut.environment

private theorem Backend.edges_length (backend : Backend S) (env : Environment E)
    (state : S) (before : E) (n : Nat) : (backend.run env state before n).edges.length = n := by
  induction n generalizing state before with
  | zero => rfl
  | succ n ih => simp only [Backend.run, List.length_cons, ih]

private theorem Backend.edges_at (backend : Backend S) (env : Environment E) (state : S) (before : E)
    (n k : Nat) (within : k < n) : (backend.run env state before n).edges[k]? =
      some (backend.atEdge env state before k) := by
  induction n generalizing state before k with
  | zero => omega
  | succ n ih =>
    cases k with
    | zero => rfl
    | succ k => exact ih _ _ k (Nat.lt_of_succ_lt_succ within)

theorem Backend.inputs_eq_clocks (backend : Backend S) (env : Environment E) (state : S)
    (before : E) (n : Nat) : (backend.run env state before n).edges.map Edge.input =
      SessionService.clocks (fun k => (backend.atEdge env state before k).input) n := by
  apply List.ext_getElem?
  intro k
  by_cases within : k < n
  · simp only [SessionService.clocks, List.getElem?_map, List.getElem?_range within,
      backend.edges_at env state before n k within, Option.map_some]
  · have absent : (backend.run env state before n).edges.length ≤ k := by
      rw [backend.edges_length]
      omega
    have notInRange : (List.range n).length ≤ k := by simp; omega
    simp only [SessionService.clocks, List.getElem?_map, List.getElem?_eq_none absent,
      List.getElem?_eq_none notInRange, Option.map_none]

structure Simulates (left : Backend S) (right : Backend T) (related : S → T → Prop) : Prop where
  observe : ∀ s t, related s t → ∀ pins, left.observe s pins = right.observe t pins
  step : ∀ s t, related s t → ∀ pins, related (left.step s pins) (right.step t pins)

private theorem Simulates.sample_eq {left : Backend S} {right : Backend T} {related : S → T → Prop}
    (h : Simulates left right related) (env : Environment E) (s : S) (t : T)
    (rel : related s t) (before : E) : left.sample env s before = right.sample env t before := by
  simp only [Backend.sample, Backend.drive, h.observe s t rel]

/-- Public outputs (including the host reply) agree on every edge of two
    independently generated histories. The environment states also agree. -/
theorem Simulates.run_eq {left : Backend S} {right : Backend T} {related : S → T → Prop}
    (h : Simulates left right related) (env : Environment E) (s : S) (t : T)
    (rel : related s t) (before : E) (n : Nat) :
    let x := left.run env s before n
    let y := right.run env t before n
    related x.final y.final ∧ x.environment = y.environment ∧ x.edges = y.edges := by
  induction n generalizing s t before with
  | zero => exact ⟨rel, rfl, rfl⟩
  | succ n ih =>
    simp only [Backend.run, h.sample_eq env s t rel before]
    let edge := right.sample env t before
    have tail := ih _ _ (h.step s t rel edge.input) (env.advance before edge.input edge.pads)
    exact ⟨tail.1, tail.2.1, congrArg (edge :: ·) tail.2.2⟩

theorem Simulates.atEdge_eq {left : Backend S} {right : Backend T} {related : S → T → Prop}
    (h : Simulates left right related) (env : Environment E) (s : S) (t : T)
    (rel : related s t) (before : E) (k : Nat) :
    left.atEdge env s before k = right.atEdge env t before k := by
  have ends := h.run_eq env s t rel before k
  simp only [Backend.atEdge, ends.2.1, h.sample_eq env _ _ ends.1]

theorem Backend.final_eq (backend : Backend S) (env : Environment E) (state : S) (before : E) (n : Nat) :
    let exec := backend.run env state before n
    (exec.edges.map Edge.input).foldl backend.step state = exec.final := by
  induction n generalizing state before with
  | zero => rfl
  | succ n ih => exact ih _ _

/-- The open-loop drive trace for the inputs produced in feedback is exactly
the recorded drives followed by the drive of the final state. -/
theorem driveTrace_eq (env : Environment E) (actual : Package.State a) (before : E) (n : Nat) :
    let run := (canonical a).run env actual before n
    PublicPins.driveTrace actual (run.edges.map Edge.input) =
      run.edges.map Edge.drive ++ [PublicPins.drive run.final] := by
  induction n generalizing actual before with
  | zero => rfl
  | succ n ih =>
    let edge := (canonical a).sample env actual before
    exact congrArg (edge.drive :: ·) (ih (PublicPins.step actual edge.input)
      (env.advance before edge.input edge.pads))

private theorem openDrain_raw (host : E → Session.Pins) (target : E → Pinwheel.I2C.Pins)
    (advance : E → BitVec 2 → (TinyWiring.Pad → BitVec 8) → E)
    (backend : Backend S) (state : S) (before : E) (n : Nat) :
    ∀ edge ∈ (backend.run (openDrain host target advance) state before n).edges,
      edge.input.rawInputs = StreamingI2CRead.resolvedRaw edge.drive (target edge.environment) := by
  induction n generalizing state before with
  | zero => simp [Backend.run]
  | succ n ih =>
    intro edge member
    simp only [Backend.run, List.mem_cons] at member
    rcases member with rfl | tail
    · rfl
    · exact ih _ _ _ tail

/-- Bridge a causal target execution to the existing protocol theorem's
    public connection premise. No input waveforms are assumed in sync. -/
theorem publicConnection (host : E → Session.Pins) (target : E → Pinwheel.I2C.Pins)
    (advance : E → BitVec 2 → (TinyWiring.Pad → BitVec 8) → E)
    (actual : Package.State a) (before : E) (n : Nat) :
    let backend := canonical a
    let env := openDrain host target advance
    let run := backend.run env actual before n
    I2CReadSession.PublicConnection actual (run.edges.map Edge.input)
      (fun k => target (backend.atEdge env actual before k).environment) := by
  dsimp only
  intro k inRange
  let edges := ((canonical a).run (openDrain host target advance) actual before n).edges
  have within : k < edges.length := by simpa only [List.length_map] using inRange
  rw [driveTrace_eq]
  change (I2CReadSession.rawSamples (edges.map Edge.input))[k]? =
    ((edges.map Edge.drive ++ [PublicPins.drive _])[k]?).map (fun drive =>
      StreamingI2CRead.resolvedRaw drive (target ((canonical a).atEdge (openDrain host target advance)
        actual before k).environment))
  have sampled : (canonical a).atEdge (openDrain host target advance) actual before k = edges[k] := by
    refine Option.some.inj ?_
    rw [← (canonical a).edges_at (openDrain host target advance) actual before n k (by
      rwa [show edges.length = n from (canonical a).edges_length _ _ _ _] at within)]
    exact List.getElem?_eq_getElem within
  have beforeEnd : k < (edges.map Edge.drive).length := by simpa only [List.length_map] using within
  simp only [sampled, I2CReadSession.rawSamples, List.getElem?_append_left beforeEnd, List.getElem?_map,
    List.getElem?_eq_getElem within, Option.map_some]
  have raw := congrArg Pinwheel.Program.Streaming.Session.Pins.rawInputs
    (PublicPins.physical_embed edges[k].input)
  change (PublicPins.embed edges[k].input).ui.extractLsb' 3 2 = edges[k].input.rawInputs at raw
  rw [raw]
  exact congrArg some (openDrain_raw host target advance (canonical a) actual before n edges[k]
    (List.getElem_mem within))

/-- The I²C service theorem can be used with a feedback environment in place
    of an assumed resolved-input waveform. Host service and target deadlines
    are obligations on that one causal execution. -/
theorem completed_i2c (profile : I2cProfile) (actual : Package.State a) (s : Session.State a)
    (reached : InitializedCustody.Reached (i2cImage profile) actual s {})
    (before : State a) (start : Input)
    (started : s.core = before.start (i2cImage profile).program start) (count : start.startCount = 585#16)
    (host : E → Session.Pins) (target : E → Pinwheel.I2C.Pins)
    (advance : E → BitVec 2 → (TinyWiring.Pad → BitVec 8) → E) (initial : E)
    (payload : List (BitVec 8)) (size : payload.length = 64) (ha : a ≤ 3) :
    let env := openDrain host target advance
    let atEdge := (canonical a).atEdge env actual initial
    let traffic := fun k => (atEdge k).input
    let peer := fun k => target (atEdge k).environment
    I2CReadSuccess.ServiceAssumptions profile s traffic payload peer → I2CReadSuccess.DrainService profile s traffic →
      ∃ n drain release,
        I2CReadSuccess.Result profile actual s (((canonical a).run env actual initial n).edges.map Edge.input)
          drain release payload peer := by
  dsimp only
  intro service drain
  have connection (n : Nat) := publicConnection host target advance actual initial n
  simp only [Backend.inputs_eq_clocks] at connection
  obtain ⟨n, drainPins, release, result⟩ := I2CReadSuccess.completed_from_service profile actual s reached
    before start started count _ payload size _ ha service connection drain
  exact ⟨n, drainPins, release, by rwa [Backend.inputs_eq_clocks]⟩

end Pinwheel.Hardware.StreamingReady.CausalSession
