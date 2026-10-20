import Pinwheel.Hardware.StreamingMapped.Comparison
import Pinwheel.Hardware.StreamingMapped.ReductionLogic
import Pinwheel.Hardware.StreamingMapped.ReductionAnd
import Pinwheel.Hardware.StreamingMapped.Clauses
import Pinwheel.Hardware.StreamingMapped.Ports
import Pinwheel.Hardware.StreamingMapped.TinyWiring
import Pinwheel.Hardware.StreamingMapped.UARTTiming

/-! Generic kernel infrastructure for certificates reconstructed from actual
mapped cells. Artifact-specific word, register/output and complete-device
theorems are generated and checked by the separate fresh mapping gate. -/
