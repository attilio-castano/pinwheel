import Lean.Data.Json
import Pinwheel.Program.StreamingReadySegments

/-! Host metadata for a checked Ready image. The encoded rows and exit
    descriptions come from the same image certificate. -/
namespace Pinwheel.Program.StreamingReadyManifest

open Lean StreamingReadySegments

private def exitKind : Exit → String
  | .complete => "complete"
  | .discard => "discard"
  | .fault => "fault"

private def exitJson (path : PathEnd) : Json :=
  Json.mkObj [
    ("kind", toJson (exitKind path.exit)),
    ("tx", toJson path.tx),
    ("rx", toJson path.rx),
    ("core_clocks", toJson path.maxCoreClocks),
    ("external_polls", toJson path.externalPolls)]

/-- The host's payload fills the START transmit budget. A path that awaits
    an external poll has no finite static core clock bound. -/
def exportJson (image : Image rows budget) (idle : StreamingReady.Pins)
    (txBits : List Bool) : Except String Json :=
  if txBits.length = image.txBudget then
    .ok (Json.mkObj [
      ("schema", toJson "pinwheel.ready-image.v1"),
      ("words", toJson (image.words.map BitVec.toNat)),
      ("start_count", toJson image.txBudget),
      ("tx_bits", toJson txBits),
      ("idle_levels", toJson idle.levels.toNat),
      ("idle_enabled", toJson idle.enabled.toNat),
      ("exits", toJson (image.outcomes.map exitJson))])
  else .error "Ready manifest TX payload length must equal the checked START budget"

end Pinwheel.Program.StreamingReadyManifest
