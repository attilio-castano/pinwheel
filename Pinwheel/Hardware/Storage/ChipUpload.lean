import Pinwheel.Hardware.Storage.ChipBackend
import Pinwheel.Hardware.Storage.ProgramUpload

/-! From the serial pins to a running program.

The pieces, in order: a host session on the pins delivers its commands to the
core (`Chip.session_delivers`); an upload's commands leave the reference machine
holding the program with its engine reset (`Readiness.program_loads`); the chip's
pins show that reference machine (`Policy.chip_trace`); and a machine that holds
a program runs it, edge for edge, as the instruction-level engine does
(`Machine.runs_program`). `chip_runs_upload` puts them in one statement. -/
namespace Pinwheel.Hardware.Storage.Backend
open Loader

/-- The reference the backends refine is the machine behind the capacity check. -/
theorem reference_run (m : Machine.State) (history : List Machine.Inputs) :
    referenceComponent.run m history = Machine.runWith Small.capacity m history := by
  induction history generalizing m with
  | nil => rfl
  | cons i rest ih => exact ih _

/-- **From a session on the pins to a loaded program.** Samplers idle, receiver
between frames, engine stopped: a session carrying the stream of a fitting
program `p`, then two more samples of anything, leaves the reference machine
with `p` committed and its engine reset on `p`. -/
theorem chip_program_loads {p : Execution.Image} {ws : List (BitVec 64)}
    (h : Readiness.upload p = some ws) (hfits : Readiness.Fits p) (d₀ d₁ : BitVec 64)
    (x : Chip.State) (hcount : x.receiver.count = 0) (hfire : x.receiver.fire = false)
    (hfirst : Serial.Idle x.first) (hsecond : Serial.Idle x.second)
    (pins : List Chip.Pins) (a b : Chip.Pins)
    (hs : Serial.Session (pins.map Chip.wired) (Machine.uploadCommands ws d₀ d₁))
    (m : Machine.State) (hidle : Reactive.runningValue m.core = false) :
    Machine.Running p (Engine.Reactive.reset p)
      (referenceComponent.run m (Chip.consumed x (pins ++ [a, b]))) := by
  rw [reference_run]
  exact Readiness.program_loads Small.capacity h (Readiness.upload_fits h hfits) d₀ d₁ _ m hidle
    (Chip.session_delivers x hcount hfire hfirst hsecond pins a b _ hs)

/-- On an upload of a ready program, every push the core consumes is ready: the
one-port rule holds along the session. -/
theorem chip_upload_ready {p : Execution.Image} {ws : List (BitVec 64)}
    (h : Readiness.upload p = some ws) (hready : Readiness.Image p) (d₀ d₁ : BitVec 64)
    (x : Chip.State) (hcount : x.receiver.count = 0) (hfire : x.receiver.fire = false)
    (hfirst : Serial.Idle x.first) (hsecond : Serial.Idle x.second)
    (pins : List Chip.Pins) (a b : Chip.Pins)
    (hs : Serial.Session (pins.map Chip.wired) (Machine.uploadCommands ws d₀ d₁)) :
    ∀ e ∈ Chip.history x (pins ++ [a, b]), OnePort.Rule e.1 := by
  intro e he hc
  have hd := Chip.session_delivers x hcount hfire hfirst hsecond pins a b _ hs
  refine Machine.Delivers.pushes hd (fun d => SinglePort.Ready d = true) (fun d hmem => ?_) e.1
    (List.mem_map_of_mem he) hc
  unfold Machine.uploadCommands at hmem
  rcases List.mem_cons.mp hmem with heq | hmem
  · have : (2 : BitVec 3) = 1 := congrArg Prod.fst heq
    exact absurd this (by decide)
  · rcases List.mem_append.mp hmem with hmem | hmem
    · obtain ⟨w, hw, heq⟩ := List.mem_map.mp hmem
      rw [← (Prod.mk.inj heq).2]
      exact Readiness.upload_ready p hready ws h w hw
    · rcases List.mem_cons.mp hmem with heq | hmem
      · have : (2 : BitVec 3) = 3 := congrArg Prod.fst heq
        exact absurd this (by decide)
      · cases hmem

/-- **From the pins to a running program, in one statement** (two-port chip, any
fitting program). Upload `p` over the serial pins, then let the pins do anything
(`rest`): the chip's pins show the atomic reference machine throughout, and
during `rest` that machine starts from a state with `p` committed and its engine
reset on `p` — from which `Machine.runs_program_with` makes every edge without an
`init` or a commit one edge of the instruction-level engine running `p`. -/
theorem TwoPort.chip_runs_upload {p : Execution.Image} {ws : List (BitVec 64)}
    (h : Readiness.upload p = some ws) (hfits : Readiness.Fits p) (d₀ d₁ : BitVec 64)
    (s : TwoPort.State) (hvalid : TwoPort.Valid s)
    (hidle : Reactive.runningValue s.reference.machine.core = false)
    (x : Chip.State) (hcount : x.receiver.count = 0) (hfire : x.receiver.fire = false)
    (hfirst : Serial.Idle x.first) (hsecond : Serial.Idle x.second)
    (pins : List Chip.Pins) (a b : Chip.Pins)
    (hs : Serial.Session (pins.map Chip.wired) (Machine.uploadCommands ws d₀ d₁))
    (rest : List Chip.Pins) :
    ∃ loaded : Machine.State, Machine.Running p (Engine.Reactive.reset p) loaded ∧
      ((Chip.netlist TwoPort.netlist).componentOf Chip.Pins.values).trace
          (Chip.values (s.values TwoPort.values) x) ((pins ++ [a, b]) ++ rest) =
        (referenceComponent.pairTrace s.reference.machine (Chip.history x (pins ++ [a, b]))).map
            Chip.shownEdge ++
          (referenceComponent.pairTrace loaded
            (Chip.history (Chip.advance x (pins ++ [a, b])) rest)).map Chip.shownEdge := by
  refine ⟨referenceComponent.run s.reference.machine (Chip.consumed x (pins ++ [a, b])),
    chip_program_loads h hfits d₀ d₁ x hcount hfire hfirst hsecond pins a b hs _ hidle, ?_⟩
  rw [TwoPort.chip_trace s hvalid x, Chip.history_append, Timed.Component.pairTrace_append,
    List.map_append]
  rfl

/-- The same for the one-port chip, for fitting programs that are ready, as long
as what follows the upload keeps the rule. -/
theorem OnePort.chip_runs_upload {p : Execution.Image} {ws : List (BitVec 64)}
    (h : Readiness.upload p = some ws) (hfits : Readiness.Fits p) (hready : Readiness.Image p)
    (d₀ d₁ : BitVec 64) (s : OnePort.State) (hvalid : OnePort.Valid s)
    (hidle : Reactive.runningValue s.reference.machine.core = false)
    (x : Chip.State) (hcount : x.receiver.count = 0) (hfire : x.receiver.fire = false)
    (hfirst : Serial.Idle x.first) (hsecond : Serial.Idle x.second)
    (pins : List Chip.Pins) (a b : Chip.Pins)
    (hs : Serial.Session (pins.map Chip.wired) (Machine.uploadCommands ws d₀ d₁))
    (rest : List Chip.Pins)
    (hrest : ∀ e ∈ Chip.history (Chip.advance x (pins ++ [a, b])) rest, OnePort.Rule e.1) :
    ∃ loaded : Machine.State, Machine.Running p (Engine.Reactive.reset p) loaded ∧
      ((Chip.netlist OnePort.netlist).componentOf Chip.Pins.values).trace
          (Chip.values (s.values OnePort.values) x) ((pins ++ [a, b]) ++ rest) =
        (referenceComponent.pairTrace s.reference.machine (Chip.history x (pins ++ [a, b]))).map
            Chip.shownEdge ++
          (referenceComponent.pairTrace loaded
            (Chip.history (Chip.advance x (pins ++ [a, b])) rest)).map Chip.shownEdge := by
  refine ⟨referenceComponent.run s.reference.machine (Chip.consumed x (pins ++ [a, b])),
    chip_program_loads h hfits d₀ d₁ x hcount hfire hfirst hsecond pins a b hs _ hidle, ?_⟩
  have hrule : ∀ e ∈ Chip.history x ((pins ++ [a, b]) ++ rest), OnePort.Rule e.1 := by
    intro e he
    rw [Chip.history_append] at he
    rcases List.mem_append.mp he with he | he
    · exact chip_upload_ready h hready d₀ d₁ x hcount hfire hfirst hsecond pins a b hs e he
    · exact hrest e he
  rw [OnePort.chip_trace s hvalid x _ hrule, Chip.history_append,
    Timed.Component.pairTrace_append, List.map_append]
  rfl

end Pinwheel.Hardware.Storage.Backend
