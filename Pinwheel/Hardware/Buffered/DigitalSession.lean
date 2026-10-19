import Pinwheel.Hardware.Buffered.I2cSessionTrace
import Pinwheel.Hardware.Buffered.I2cUploadAdequacy
import Pinwheel.Hardware.Buffered.I2cSimulation
import Pinwheel.Hardware.Buffered.LifecycleRestart
import Pinwheel.Hardware.Buffered.SerialSourceStart
import Pinwheel.Hardware.Buffered.SerialSourceRelease
import Pinwheel.Hardware.Buffered.SerialSourceAdministrative
import Pinwheel.Hardware.Buffered.SerialSourceIndexedRead
import Pinwheel.Hardware.Buffered.SerialCorrespondenceEncoding
import Pinwheel.Hardware.Buffered.SerialSourceRetry
import Pinwheel.Hardware.Buffered.I2cTimingSimulation
import Pinwheel.Hardware.Buffered.I2cTimingUpload
import Pinwheel.Hardware.Buffered.SerialSourceSession
import Pinwheel.Hardware.Buffered.SerialWireConcrete
import Pinwheel.Hardware.Buffered.LogicalSessionRound
import Pinwheel.Hardware.Buffered.LogicalSessionTrace
import Pinwheel.Hardware.Buffered.LogicalSessionRead
import Pinwheel.Hardware.Buffered.SerialUploadConcrete
import Pinwheel.Hardware.Buffered.SerialUploadReset
import Pinwheel.Hardware.Buffered.LogicalSessionAbortTrace
import Pinwheel.Hardware.Buffered.SerialInitializedSession
import Pinwheel.Hardware.Buffered.SerialStartAdmission
import Pinwheel.Hardware.Buffered.LogicalWireAbort
import Pinwheel.Hardware.Buffered.SerialSessionWitnessReuse
import Pinwheel.Hardware.Buffered.SerialSessionWitnessLogical

/-! Entry point for source-grounded digital buffered sessions. Static layout,
initialization, execution, owned read/release, reset epochs and sampled serial
receipts remain separate named contracts, composed by the session theorems.
Physical timing, electrical peer behavior and emitter equivalence are outside
these digital recurrence proofs. -/
