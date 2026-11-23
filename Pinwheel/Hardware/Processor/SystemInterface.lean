import Pinwheel.Hardware.Processor.CoreInterface
import Pinwheel.Hardware.Processor.MmioInterface

namespace Pinwheel.Hardware.Processor.SystemInterface

abbrev inputPorts : Stream.Ports where
  size := 6
  widths := fun k => #[1,32,1,1,8,1][k]
  names := fun k => #["reset", "gpio_input", "tx_complete", "rx_valid", "rx_data", "framing_error"][k]
  distinct := by decide +kernel
abbrev Input := inputPorts.Signal
def inputs : Interface Input := inputPorts.interface
def reset : Input 1 := .at ⟨0,by decide⟩
def gpioInput : Input 32 := .at ⟨1,by decide⟩
def txComplete : Input 1 := .at ⟨2,by decide⟩
def rxValid : Input 1 := .at ⟨3,by decide⟩
def rxData : Input 8 := .at ⟨4,by decide⟩
def framingError : Input 1 := .at ⟨5,by decide⟩

abbrev fetchPorts : Stream.Ports where
  size := 3
  widths := fun k => if k.val = 2 then 32 else 1
  names := fun k => #["fetch_valid", "fetch_fault", "fetch_data"][k]
  distinct := by decide +kernel
abbrev Fetch := fetchPorts.Signal

end Pinwheel.Hardware.Processor.SystemInterface
