import Pinwheel.Hardware.Switch.Interface

open Pinwheel.Hardware
open Pinwheel.Hardware.Switch
open Pinwheel.Hardware.Switch.Physical

namespace SwitchInterfaceTests

set_option backward.isDefEq.respectTransparency false

def dest3 : DestinationEncoding 3 := ⟨2, by decide, by decide⟩
def dest1 : DestinationEncoding 1 := ⟨1, by decide, by decide⟩

def mixed : Pins 1 2 2 8 where
  reset := 0
  valid := fun _ => 1
  destination := fun k => if k = 0 then 3 else 2
  payload := fun k => if k = 0 then 99 else 42
  ready := fun _ => 1

/-- Invalid asserted destination code 3 is refused by a 3-output switch. The
other input remains independently admissible. -/
example : (decode mixed).offered 0 = none := by decide +kernel
example : Physical.observe 1 mixed initial (inReady 0) = 0 := by decide +kernel
example : Physical.observe 1 mixed initial (inReady 1) = 1 := by decide +kernel
example : ((Physical.component dest3 1).step mixed.values initial).queues 0 = [] := by decide +kernel
example : ((Physical.component dest3 1).step mixed.values initial).queues 1 = [⟨2, 42⟩] := by decide +kernel

/-- Deasserted valid is idle, even when its unused destination bits are invalid. -/
example : Physical.observe 1 { mixed with valid := fun _ => 0 } initial (inReady 0) = 1 := by decide +kernel
example : Physical.observe 1 { mixed with reset := 1 } initial (inReady 1) = 0 := by decide +kernel

example : decodePacket (encodeDestination dest3 2) (42#8) = some (⟨2, 42⟩ : Packet 3 (BitVec 8)) :=
  decodePacket_encode dest3 (⟨2, 42⟩ : Packet 3 (BitVec 8))
example : decodePacket (encodeDestination dest1 0) (17#8) = some (⟨0, 17⟩ : Packet 1 (BitVec 8)) :=
  decodePacket_encode dest1 (⟨0, 17⟩ : Packet 1 (BitVec 8))
example : decodePacket (1#1) (17#8) = (none : Option (Packet 1 (BitVec 8))) := by decide +kernel

example (i : Switch.Input n (m+1) (BitVec w)) (e : DestinationEncoding (m+1)) :
    decode (encode e i) = i := decode_encode e i

example : (inputInterface 1 2 2 8).size = 10 := rfl
example : (outputInterface 1 2 8).size = 8 := rfl
example : ((inputInterface 1 2 2 8).position (inDestination 1)).val = 4 := by decide +kernel
example : ((inputInterface 1 2 2 8).position (inPayload 0)).val = 5 := by decide +kernel
example : ((inputInterface 1 2 2 8).position (outReady 2)).val = 9 := by decide +kernel
example : ((outputInterface 1 2 8).position (outPayload 2)).val = 7 := by decide +kernel
example : (inputInterface 1 2 2 8).label (inDestination 1) = "in_4" := by decide +kernel
example : (outputInterface 1 2 8).label (outPayload 2) = "out_7" := by decide +kernel

end SwitchInterfaceTests

def main : IO Unit := IO.println
  "Switch physical interface: typed enumeration, legal codec, invalid admission suppression and idle readiness checked."
