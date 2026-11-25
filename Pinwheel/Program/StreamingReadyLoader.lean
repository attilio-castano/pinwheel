import Pinwheel.Program.StreamingReadyBootPins

/-! A source model of the host frontend while an image is uploaded. Before
COMMIT the engine is free with generation 0, so the frontend state after a
concrete upload can be computed without the full session. Concrete sessions
(the Ethernet schedule, the I²C read witness) start from `seed`. -/
namespace Pinwheel.Program.StreamingReady.Loader

structure State where
  host : Streaming.Host.State := {csnPrev := true}
  written : Bool := false
  installed : Bool := false

def core (s : State) : StreamingReady.State 1 := { generation := if s.installed then 1 else 0 }

def status (s : State) (pin : Session.Pins) : Streaming.Host.Status :=
  { (core s).status (s.written && !s.installed) (s.host.command (pin.host {})).runtime with
    valid := s.installed, rejected := false }

def step (s : State) (pin : Session.Pins) : State :=
  let command := (s.host.command (pin.host {})).runtime.command
  ⟨Streaming.Host.step (pin.host (status s pin)) s.host,
    s.written || command == 1, s.installed || command == 2⟩

/-- The session state after uploading with `pins` from the cold frontend. -/
def seed (pins : List Session.Pins) : Session.State 1 :=
  let final := pins.foldl step {}
  ⟨final.host, core final⟩

end Pinwheel.Program.StreamingReady.Loader
