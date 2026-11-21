import Pinwheel.Hardware.BankImplementation
import Pinwheel.Hardware.Artifact
import Pinwheel.Hardware.TypedModule
import Pinwheel.Hardware.TypedHierarchy
import Pinwheel.Hardware.Stream.Bundle
import Pinwheel.Hardware.Stream.Implementation
import Pinwheel.Hardware.Stream.Timing
import Pinwheel.Hardware.Stream.Diamond
import Pinwheel.Hardware.Arbitration.RoundRobinMasked
import Pinwheel.Hardware.Switch.Certified
import Pinwheel.Hardware.Switch.Contract
import Pinwheel.Hardware.Switch.Progress
import Pinwheel.Hardware.Stream.BackendLane
import Pinwheel.Hardware.Stream.CircularFifo3
import Pinwheel.Hardware.Switch.Backend

/-! Reusable synchronous hardware: typed circuits and interfaces, register
banks, stream components and composition, arbitration, multiport contracts,
and implementation/artifact certificates. This entry point does not import
Pinwheel's protocol processor, retained tapeout, or physical-design packages.
Memory and processor integration APIs remain separate campaign work.
-/
