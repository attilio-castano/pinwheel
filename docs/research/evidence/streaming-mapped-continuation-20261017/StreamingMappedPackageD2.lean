import Pinwheel.Hardware.StreamingReady.Wiring

namespace Pinwheel.Artifact.StreamingMappedPackageD2
open Pinwheel.Hardware Pinwheel.Hardware.StreamingReady Wiring
def netlistSHA256 : String := "7230add85334400a1e08307c7317ca5610960a63e30a59dbca3ae1fb39966fc9"
def actualFrontend : {w : Nat} → Pinwheel.Hardware.Streaming.Frontend.Input w → FrontSource w
  | _, .initialize => .physical .initialize
  | _, .sck => .physical .sck
  | _, .csn => .physical .csn
  | _, .mosi => .physical .mosi
  | _, .rawInputs => .physical .rawInputs
  | _, .status .valid => .status .valid
  | _, .status .busy => .status .busy
  | _, .status .retained => .status .retained
  | _, .status .pending => .status .pending
  | _, .status .rejected => .status .rejected
  | _, .status .stalled => .status .stalled
  | _, .status .fault => .status .fault
  | _, .status .waitingTX => .status .waitingTX
  | _, .status .waitingRX => .status .waitingRX
  | _, .status .generation => .status .generation
  | _, .status .transfer => .status .transfer
  | _, .status .phase => .status .phase
  | _, .status .pc => .status .pc
  | _, .status .remaining => .status .remaining
  | _, .status .total => .status .total
  | _, .status .levels => .status .levels
  | _, .status .enabled => .status .enabled
  | _, .status .txFree => .status .txFree
  | _, .status .txQueued => .status .txQueued
  | _, .status .rxQueued => .status .rxQueued
  | _, .status .rxData => .status .rxData
  | _, .status .rxBits => .status .rxBits
  | _, .status .txAccepted => .status .txAccepted
  | _, .status .txConsumed => .status .txConsumed
  | _, .status .rxProduced => .status .rxProduced
  | _, .status .rxPopped => .status .rxPopped
  | _, .status .stage1 => .status .stage1
  | _, .status .stage2 => .status .stage2
def actualCore : {w : Nat} → Pinwheel.Hardware.StreamingReady.Core.Input w → Pinwheel.Hardware.Streaming.Frontend.Output w
  | _, .initialize => .core .initialize
  | _, .command => .core .command
  | _, .address => .core .address
  | _, .word => .core .word
  | _, .count => .core .count
  | _, .idleLevels => .core .idleLevels
  | _, .idleEnabled => .core .idleEnabled
  | _, .startCount => .core .startCount
  | _, .expectedGeneration => .core .expectedGeneration
  | _, .expectedTransfer => .core .expectedTransfer
  | _, .txPush => .core .txPush
  | _, .txData => .core .txData
  | _, .txBits => .core .txBits
  | _, .rxPop => .core .rxPop
  | _, .rawInputs => .core .rawInputs
def actualOutput : {w : Nat} → Package.Output w → PublicSource w
  | _, .miso => .frontend (.miso)
  | _, .ready => .frontend (.ready)
  | _, .busy => .status .busy
  | _, .levels => .status .levels
  | _, .enabled => .status .enabled
def actualPackage : Wiring.Description :=
  ⟨"pinwheel_streaming_ready_quad_d2",[⟨"clk",1,true⟩,⟨"initialize",1,true⟩,⟨"csn",1,true⟩,⟨"sck",1,true⟩,⟨"mosi",4,true⟩,⟨"raw_inputs",2,true⟩,⟨"miso",4,false⟩,⟨"ready",1,false⟩,⟨"busy",1,false⟩,⟨"levels",3,false⟩,⟨"enabled",3,false⟩],[⟨"frontend","pinwheel_streaming_quad_frontend"⟩,⟨"core","pinwheel_streaming_ready_core_d2"⟩],"clk","clk",actualFrontend,actualCore,actualOutput⟩
theorem package_correct : Wiring.Certificate 1 actualPackage where
  name := rfl
  interface := rfl
  instances := rfl
  frontendClock := rfl
  coreClock := rfl
  frontend := by
    intro w port
    cases port <;> try rfl
    case status o => cases o <;> rfl
  core := by intro w port; cases port <;> rfl
  outputs := by intro w port; cases port <;> rfl
end Pinwheel.Artifact.StreamingMappedPackageD2
