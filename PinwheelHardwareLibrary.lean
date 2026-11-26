import Pinwheel.Hardware.Library
import Pinwheel.Hardware.Memory.TransferHostOwnershipCandidate
import Pinwheel.Hardware.Processor.Examples.ReadySPIExchange
import Pinwheel.Hardware.Processor.Examples.ReadySPISampling
import Pinwheel.Hardware.Processor.LoadableSystemExportProofs
import Pinwheel.Hardware.Processor.MmioRefinement
import Pinwheel.Hardware.Processor.RV32I.RegisterFile
import Pinwheel.Hardware.Processor.SerialRefinement
import Pinwheel.Hardware.Processor.SerialSystemBoot
import Pinwheel.Hardware.Processor.SystemCircuitArchitecture
import Pinwheel.Hardware.Stream.Replay
import Pinwheel.Hardware.Switch.Export
import Pinwheel.Hardware.Switch.SharedSelectionCandidate
import Pinwheel.Hardware.Timebase.Tx
import Pinwheel.Hardware.Uart.FractionalRxTiming

/-! The reusable Lean hardware library: typed circuits with proofs for
memory adapters, the RV32I processor and its systems, stream composition,
packet switches and UART timebases. It is independent of the streaming chip
stack in `Pinwheel` and takes about nine CPU-minutes to build (one module,
`Processor.CoreCircuitOutputs`, takes five), so `lake build` skips it. Build it
with `lake build PinwheelHardwareLibrary`; the foundation gate builds and
audits it. -/
