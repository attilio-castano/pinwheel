import Pinwheel.Hardware.StreamingReady.CausalSession
import Pinwheel.Hardware.StreamingReady.RegisteredStorePackage

/-! Lift the store's cycle-exact refinement through public-pin feedback.
    The observation includes clock-indexed wire samples and the host reply. -/
namespace Pinwheel.Hardware.StreamingReady.RegisteredStoreSession

open Pinwheel.Program.StreamingReady CausalSession

def backend (a : Nat) : Backend (RegisteredStorePackage.State a) where
  step state pins := state.physical_step (PublicPins.embed pins)
  observe state pins := state.physical_observe (PublicPins.embed pins)

theorem simulation (a : Nat) :
    Simulates (backend a) (canonical a) (fun registered direct =>
      registered.Related ∧ registered.project = direct) := by
  constructor
  · rintro registered _ ⟨_, rfl⟩ pins
    exact registered.physical_observe_eq (PublicPins.embed pins)
  · rintro registered _ ⟨related, rfl⟩ pins
    exact ⟨registered.preserves _, registered.physical_project_step (PublicPins.embed pins) related⟩

/-- Under any causal host and peer, both stores produce the same timed
    public transcript. The equality preserves every capture aperture and
    applies across loader, START, drain, and RELEASE edges. -/
theorem run_eq (env : Environment E) (registered : RegisteredStorePackage.State a) (valid : registered.Related)
    (initial : E) (clocks : Nat) :
    let reference := (canonical a).run env registered.project initial clocks
    let actual := (backend a).run env registered initial clocks
    actual.final.Related ∧ actual.final.project = reference.final ∧
      actual.environment = reference.environment ∧ actual.edges = reference.edges := by
  have agreement := (simulation a).run_eq env registered registered.project ⟨valid, rfl⟩ initial clocks
  exact ⟨agreement.1.1, agreement.1.2, agreement.2⟩

/-- A public cold-reset edge establishes the relation even with an arbitrary
    value in the instruction-read register. -/
theorem cold_start (registered : RegisteredStorePackage.State a) :
    let after := (backend a).step registered BootPins.coldPin
    after.Related ∧ after.project = PublicPins.step registered.project BootPins.coldPin := by
  change (registered.physical_step (PublicPins.embed BootPins.coldPin)).Related ∧ _
  rw [RegisteredStorePackage.State.physical_step, PublicPins.engine_embed, PublicPins.step_eq]
  exact ⟨registered.preserves _, registered.project_cold _ rfl⟩

theorem atEdge_eq (env : Environment E) (registered : RegisteredStorePackage.State a) (valid : registered.Related)
    (initial : E) (clock : Nat) :
    (backend a).atEdge env registered initial clock = (canonical a).atEdge env registered.project initial clock :=
  (simulation a).atEdge_eq env registered registered.project ⟨valid, rfl⟩ initial clock

/-- Existing loader and protocol theorems can consume the actual pin history
    directly and recover the terminal state of the registered package. -/
theorem project_run (env : Environment E) (registered : RegisteredStorePackage.State a) (valid : registered.Related)
    (initial : E) (clocks : Nat) :
    let actual := (backend a).run env registered initial clocks
    (actual.edges.map Edge.input).foldl PublicPins.step registered.project = actual.final.project := by
  dsimp only
  have same := run_eq env registered valid initial clocks
  rw [same.2.1, same.2.2.2]
  exact (canonical a).final_eq env registered.project initial clocks

/-- A closed-loop contract on the canonical package's visible timed
    execution and terminal state transports without a new protocol proof. -/
theorem preserves_contract (env : Environment E) (registered : RegisteredStorePackage.State a)
    (valid : registered.Related)
    (initial : E) (clocks : Nat) (contract : List (Edge E) → Package.State a → Prop) :
    let reference := (canonical a).run env registered.project initial clocks
    let actual := (backend a).run env registered initial clocks
    contract reference.edges reference.final → contract actual.edges actual.final.project := by
  dsimp only
  have same := run_eq env registered valid initial clocks
  rw [same.2.2.2, same.2.1]
  exact id

/-- The I²C framing and data theorem applies to the independently generated
    registered-store wire history. Its service hypotheses are stated against
    that history, including the target's drive at each capture. -/
theorem completed_i2c (profile : I2cProfile) (registered : RegisteredStorePackage.State a) (valid : registered.Related)
    (s : Session.State a) (reached : InitializedCustody.Reached (i2cImage profile) registered.project s {})
    (before : State a) (start : Input)
    (started : s.core = before.start (i2cImage profile).program start) (count : start.startCount = 585#16)
    (host : E → Session.Pins) (target : E → Pinwheel.I2C.Pins)
    (advance : E → BitVec 2 → (TinyWiring.Pad → BitVec 8) → E) (initial : E)
    (payload : List (BitVec 8)) (size : payload.length = 64) (ha : a ≤ 3) :
    let env := openDrain host target advance
    let atEdge := (backend a).atEdge env registered initial
    let traffic := fun k => (atEdge k).input
    let peer := fun k => target (atEdge k).environment
    I2CReadSuccess.ServiceAssumptions profile s traffic payload peer → I2CReadSuccess.DrainService profile s traffic →
      ∃ n drain release,
        I2CReadSuccess.Result profile registered.project s
          (((backend a).run env registered initial n).edges.map Edge.input) drain release payload peer := by
  dsimp only
  simp only [atEdge_eq _ _ valid]
  intro service drain
  obtain ⟨n, drainPins, release, read⟩ := CausalSession.completed_i2c profile registered.project s reached
    before start started count host target advance initial payload size ha service drain
  exact ⟨n, drainPins, release, by rwa [(run_eq _ _ valid initial n).2.2.2]⟩

end Pinwheel.Hardware.StreamingReady.RegisteredStoreSession
