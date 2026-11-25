import Pinwheel.Hardware.StreamingReady.LoaderBoot
import Pinwheel.Program.StreamingEthernetSchedule

/-! The certified upload also determines the complete source frontend state
used by the concrete Ethernet host schedule. -/
namespace Pinwheel.Hardware.StreamingReady.EthernetBoot
open Pinwheel.Hardware Pinwheel.Program.StreamingReady Pinwheel.Program.StreamingEthernetCore
open Pinwheel.Program.StreamingEthernetSchedule BootCorrespondence

set_option maxRecDepth 18000 in
theorem initialized (startup : Package.State 1) :
    Initialized image (startup.run (Package.Components.typed 1)
      (SessionCorrespondence.pins BootPins.coldPin :: bootPins.map SessionCorrespondence.pins)) seed := by
  have noRaw : ∀ pin ∈ bootPins, pin.rawInputs = 0 := by
    have checked : (bootPins.all fun pin => pin.rawInputs == 0) = true := by decide +kernel
    intro pin member
    exact beq_iff_eq.mp (List.all_eq_true.mp checked _ member)
  exact LoaderBoot.initialized image bootPins noRaw
    (Pinwheel.Program.Streaming.BootPins.check_sound _ _ _ _ _ _ (by decide +kernel)) startup

end Pinwheel.Hardware.StreamingReady.EthernetBoot
