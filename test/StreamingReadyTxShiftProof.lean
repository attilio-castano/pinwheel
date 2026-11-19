import StreamingReadySessionD2
import ReadyCoreD2ShiftProof
import Pinwheel.Hardware.StreamingReady.TxShiftPackage
import Pinwheel.Hardware.StreamingReady.SPISession
import Pinwheel.Hardware.StreamingReady.I2CReadSession
import Pinwheel.Hardware.StreamingReady.EthernetRefill

/-! Relate independently reconstructed core register layouts through the same
certified package and top-level wiring. -/
namespace Pinwheel.Artifact.StreamingReadyTxShift

open Pinwheel.Hardware Pinwheel.Hardware.StreamingReady
open Pinwheel.Hardware.StreamingReady.InitializedCustody
open Pinwheel.Program.StreamingReady
open StreamingReadySessionD2
open StreamingReadyWrappersD2 (tiny_correct package_correct)

abbrev ring := StreamingReadySessionD2.components

def shift : Package.Components 1 :=
  TxShiftPackage.components ring.frontend StreamingReadyCoreD2Shift.behavior

private theorem shift_behavior :
    StreamingReadyCoreD2Shift.behavior = Package.Behavior.ofCircuit TxShiftCore.circuit := by
  have step :
      @StreamingReadyCoreD2Shift.behavior.step =
        @(Package.Behavior.ofCircuit TxShiftCore.circuit).step := by
    funext i s w reg
    exact StreamingReadyCoreD2Shift.step_correct i s reg
  have observe :
      @StreamingReadyCoreD2Shift.behavior.observe =
        @(Package.Behavior.ofCircuit TxShiftCore.circuit).observe := by
    funext i s w port
    exact StreamingReadyCoreD2Shift.observe_correct i s port
  cases h : StreamingReadyCoreD2Shift.behavior
  simp_all only [Package.Behavior.ofCircuit, Streaming.Package.Behavior.ofCircuit]

theorem ring_correct : ring = Package.Components.typed 1 := components_correct.eq_typed

theorem shift_correct : shift = TxShiftPackage.typed := by
  simp only [shift, ring_correct, shift_behavior]
  rfl

theorem simulates : PackageSimulation.Simulates shift ring TxShiftPackage.RelatedCore := by
  rw [shift_correct, ring_correct]
  exact TxShiftPackage.simulation

/-- One public initialization edge establishes the relation from independent
arbitrary register assignments in the two digital artifacts. -/
theorem cold_related (l r : Package.State 1) :
    let cold := PublicPins.embed BootPins.coldPin
    TxShiftPackage.Related (actualTiny.step actualPackage shift l cold)
      (actualTiny.step actualPackage ring r cold) := by
  simp only [tiny_correct.step_eq package_correct, PublicPins.engine_embed, shift_correct, ring_correct]
  exact TxShiftPackage.cold_related _ _ _ rfl

/-- Every pad value agrees at any observation following a cold edge and an
arbitrary finite public input prefix. The observation may use the same input
as the last edge or the next input in the trace. -/
theorem all_pads_after_cold (l r : Package.State 1) (history : List TinyWiring.Pins)
    (sample : TinyWiring.Pins) :
    let cold := PublicPins.embed BootPins.coldPin
    let afterShift := history.foldl (actualTiny.step actualPackage shift)
      (actualTiny.step actualPackage shift l cold)
    let afterRing := history.foldl (actualTiny.step actualPackage ring)
      (actualTiny.step actualPackage ring r cold)
    actualTiny.observe actualPackage shift afterShift sample =
      actualTiny.observe actualPackage ring afterRing sample :=
  simulates.physical_observe tiny_correct package_correct _
    (simulates.physical_run tiny_correct package_correct _ (cold_related l r))

theorem driveTrace_eq (l r : Package.State 1) (pins : List Session.Pins)
    (related : TxShiftPackage.Related l r) :
    PackageSimulation.driveTrace actualTiny actualPackage shift l pins = PublicPins.driveTrace r pins := by
  rw [simulates.driveTrace_eq tiny_correct package_correct pins related, ring_correct]
  exact PackageSimulation.driveTrace_typed tiny_correct package_correct _ _

/-- Any pin-trace property obtained from the original SPI, I²C, or Ethernet
theorem carries over at a related protocol state. -/
theorem transport (l r : Package.State 1) (pins : List Session.Pins)
    (related : TxShiftPackage.Related l r) (property : List Pins → Prop)
    (reference : property (PublicPins.driveTrace r pins)) :
    property (PackageSimulation.driveTrace actualTiny actualPackage shift l pins) := by
  rw [driveTrace_eq l r pins related]
  exact reference

theorem spi_trace (l : Package.State 1) {rows : List Instruction} (image : Compiled rows idle)
    (s : Session.State 1) (pins : List Session.Pins)
    (related : TxShiftPackage.Related l (SessionCorrespondence.values (Initialization.compiledImage image) s))
    (runtime : Session.RuntimeTrace image.program false s pins) (structural : s.core.Structural) :
    PackageSimulation.driveTrace actualTiny actualPackage shift l pins =
      pinTrace image.program s.core (s.runtimeInputs image.program false pins) := by
  rw [driveTrace_eq _ _ _ related]
  exact SPISession.driveTrace_eq image s pins (by decide) runtime structural

theorem i2c_trace (l r : Package.State 1) (s : Session.State 1) (trace : BitTrace)
    (reached : Reached I2CReadSession.image r s trace) (pins : List Session.Pins)
    (related : TxShiftPackage.Related l r)
    (runtime : Session.RuntimeTrace I2CReadSession.image.program false s pins) :
    PackageSimulation.driveTrace actualTiny actualPackage shift l pins =
      pinTrace I2CReadSession.image.program s.core (s.runtimeInputs I2CReadSession.image.program false pins) := by
  rw [driveTrace_eq _ _ _ related]
  exact I2CReadSession.public_trace r s trace reached pins (by decide) runtime

theorem ethernet_wire (l startup : Package.State 1)
    (policy : Pinwheel.Program.StreamingEthernetRefill.Policy) (width : Nat)
    (execution : Pinwheel.Program.StreamingEthernetRefill.Executed policy width)
    (credit : Pinwheel.Program.StreamingEthernetRefill.checkCredit policy width = true)
    (related : TxShiftPackage.Related l
      ((EthernetSession.beforeWire startup).run (Package.Components.typed 1)
        ((Pinwheel.Program.StreamingEthernetRefill.alignmentPins policy width).map SessionCorrespondence.pins))) :
    PackageSimulation.driveTrace actualTiny actualPackage shift l
      (Pinwheel.Program.StreamingEthernetRefill.activePins policy width) =
      Pinwheel.Program.StreamingEthernetFrame.frameBits.flatMap
        Pinwheel.Program.StreamingEthernetCore.cellPins ++
      [Pinwheel.Program.StreamingEthernetCore.txPins false, Pinwheel.Program.StreamingEthernetCore.idlePins] := by
  rw [driveTrace_eq _ _ _ related]
  exact EthernetRefill.wire_exact startup policy width execution credit

end Pinwheel.Artifact.StreamingReadyTxShift
