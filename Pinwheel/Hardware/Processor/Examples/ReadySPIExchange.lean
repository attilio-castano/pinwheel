import Pinwheel.Hardware.Processor.Examples.ReadySPI
import Pinwheel.Hardware.Processor.ReadyHostCircuit
import Pinwheel.Hardware.StreamingReady.SPISession

/-! SPI data and timing for a completed exchange driven by the typed CPU.
The host and peer choose their next inputs from their own feedback history. -/
namespace Pinwheel.Hardware.Processor.ReadySPI

open Pinwheel.Program.StreamingReady Pinwheel.Program.StreamingSPI
open Pinwheel.Hardware.StreamingReady CausalSession InitializedCustody

private theorem run_final (env : Environment H) (device : Package.State a) (host : H) (n : Nat) :
    let x := (canonical a).run env device host n
    device.run (Package.Components.typed a) (x.edges.map (SessionCorrespondence.pins ∘ Edge.input)) =
      x.final := by
  induction n generalizing device host with
  | zero => rfl
  | succ n ih =>
    let edge := (canonical a).sample env device host
    change (device.step _ (SessionCorrespondence.pins edge.input)).run _ _ = _
    rw [← PublicPins.step_eq]
    exact ih (PublicPins.step device edge.input) (env.advance host edge.input edge.pads)

private theorem peer_samples (peer : ReadyHost.Peer E) (requests : Array (BitVec 8))
    (frames collect : Nat) (device : Package.State a)
    (host : ReadyHost.RawHost layout (rom requests frames collect) E) (n : Nat) :
    let env := ReadyHost.circuitEnvironment layout (rom requests frames collect) (by decide) (by decide) peer
    let x := (canonical a).run env device host n
    x.edges.map (fun e => (PublicPins.embed e.input).ui.extractLsb' 3 2) =
      x.edges.map (fun e => peer.sample e.environment.2 e.drive) := by
  induction n generalizing host device with
  | zero => rfl
  | succ n ih =>
    let env := ReadyHost.circuitEnvironment layout (rom requests frames collect) (by decide) (by decide) peer
    let edge := (canonical a).sample env device host
    have raw : (PublicPins.embed edge.input).ui.extractLsb' 3 2 = peer.sample host.2 edge.drive :=
      congrArg Pinwheel.Program.Streaming.Session.Pins.rawInputs (PublicPins.physical_embed edge.input)
    change (PublicPins.embed edge.input).ui.extractLsb' 3 2 :: _ = peer.sample host.2 edge.drive :: _
    rw [raw]
    exact congrArg (List.cons _) (ih (PublicPins.step device edge.input) (env.advance host edge.input edge.pads))

/-- Starting at an admitted START, a later accepted RELEASE determines the
entire SPI transaction on the actual feedback history. The engine's accepted
bits are the peer-visible MOSI. Its exported bits are the peer's MISO sampled
on leading edges. Runtime legality and arrival at RELEASE are explicit premises. -/
theorem completed_feedback (mode : Mode) (d : Fin 256) (peer : ReadyHost.Peer E)
    (requests : Array (BitVec 8)) (frames collect : Nat)
    (host : ReadyHost.RawHost layout (rom requests frames collect) E)
    (device : Package.State a) (ready : Session.State a) (n : Nat) (ha : a ≤ 3) :
    let env := ReadyHost.circuitEnvironment layout (rom requests frames collect) (by decide) (by decide) peer
    let backend := canonical a
    let first := backend.sample env device host
    let im := image mode d
    let next := device.step (Package.Components.typed a) (SessionCorrespondence.pins first.input)
    let x := backend.run env next (env.advance host first.input first.pads) n
    let after := x.edges.map Edge.input
    let release := (backend.sample env x.final x.environment).input
    let started := ready.step im.program false first.input
    let final := started.run im.program false after
    let trace := started.traceRun im.program false {} after
    let drives := x.edges.map Edge.drive ++ [PublicPins.drive x.final]
    let raw := 0 :: 0 :: x.edges.map (fun e => peer.sample e.environment.2 e.drive)
    let count := (ready.command first.input).runtime.startCount.toNat
    SessionProof.Started im device ready first.input →
    Session.RuntimeTrace im.program false started after →
    (∀ i ∈ started.runtimeInputs im.program false after, i.command ≠ 4#4) →
    Session.RuntimeInput final release → ActualRelease x.final release →
    events mode drives = .select :: edgesFor count ++ [.deselect] ∧
    activePulses mode d.val drives ∧ (∀ sample ∈ drives, sample.enabled = 7#3) ∧
    trace.accepted = mosiOnLeading mode drives ∧ trace.exported = misoOnLeading mode drives raw ∧
    final.host.ackOffset.toNat = count ∧ final.host.exportBits.toNat = 0 := by
  intro env backend first im next x after release started final trace drives raw count
    admitted runtime noRelease legal released
  let following := env.advance host first.input first.pads
  have last : next.run (Package.Components.typed a) (after.map SessionCorrespondence.pins) = x.final := by
    simpa only [after, List.map_map] using run_final env next following n
  have exchange := SPISession.completed_from_start mode d (Initialization.compiledImage im)
    device ready first.input admitted after release ha runtime noRelease legal (last ▸ released)
  unfold SPISession.Exchange at exchange
  dsimp only at exchange
  have wire : PublicPins.driveTrace next after = drives := CausalSession.driveTrace_eq env next following n
  have samples : after.map (fun pin => (PublicPins.embed pin).ui.extractLsb' 3 2) =
      x.edges.map (fun e => peer.sample e.environment.2 e.drive) := by
    simpa only [after, List.map_map, Function.comp_def] using peer_samples peer requests frames collect next following n
  change events mode (PublicPins.driveTrace next after) = _ ∧ _ at exchange
  rw [wire] at exchange
  simp only [samples] at exchange
  exact exchange

end Pinwheel.Hardware.Processor.ReadySPI
