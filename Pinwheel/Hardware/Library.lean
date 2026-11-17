import Pinwheel.Hardware.BankImplementation
import Pinwheel.Hardware.Artifact
import Pinwheel.Hardware.Stream.Bundle
import Pinwheel.Hardware.Stream.Implementation
import Pinwheel.Hardware.Stream.Timing
import Pinwheel.Hardware.Stream.Diamond
import Pinwheel.Hardware.Arbitration.RoundRobinMasked
import Pinwheel.Hardware.Arbitration.OneHotSelect
import Pinwheel.Hardware.Switch.Certified
import Pinwheel.Hardware.Switch.Contract
import Pinwheel.Hardware.Switch.Progress
import Pinwheel.Hardware.Memory.CommandFlopsProofs
import Pinwheel.Hardware.Memory.StreamFlopsProofs

/-! Reusable synchronous hardware: typed circuits and interfaces, register
banks, stream components and composition, arbitration, multiport and memory contracts,
and implementation/artifact certificates. This entry point does not import
Pinwheel's protocol processor, retained tapeout, or physical-design packages.
Memory-transfer and processor integration remain separate campaign work.
-/
