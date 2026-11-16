import Pinwheel.Hardware.Interface

namespace Pinwheel.Hardware.Stream

/-- A declarative interface. Enumeration, names, widths and simulator bindings
are derived from this one vector; distinct labels are a checked obligation. -/
structure Ports where
  size : Nat
  widths : Fin size → Nat
  names : Fin size → String
  distinct : ∀ a b, names a = names b → a = b

inductive Ports.Signal (p : Ports) : Nat → Type where
  | at (k : Fin p.size) : p.Signal (p.widths k)

def Ports.interface (p : Ports) : Interface p.Signal where
  size := p.size
  signal := fun k => ⟨_, .at k⟩
  position := fun s => match s with | .at k => k
  signal_position := fun s => by cases s; rfl
  label := fun s => match s with | .at k => p.names k
  unique := p.distinct

def Ports.Values (p : Ports) := (k : Fin p.size) → BitVec (p.widths k)

def Ports.values (p : Ports) (v : p.Values) : Hardware.Values p.Signal :=
  fun s => match s with | .at k => v k

theorem Ports.values_at (p : Ports) (v : p.Values) (k : Fin p.size) :
    p.values v (.at k) = v k := rfl

/-- All components use the same stream port schema, regardless of payload width. -/
abbrev inputPorts (width : Nat) : Ports where
  size := 4
  widths := fun k => if k.val = 3 then width else 1
  names := fun k => #["reset", "in_valid", "out_ready", "in_data"][k]
  distinct := by decide +kernel

abbrev outputPorts (width : Nat) : Ports where
  size := 3
  widths := fun k => if k.val = 2 then width else 1
  names := fun k => #["in_ready", "out_valid", "out_data"][k]
  distinct := by decide +kernel

abbrev In (w : Nat) := (inputPorts w).Signal
abbrev Out (w : Nat) := (outputPorts w).Signal

def reset : In w 1 := Ports.Signal.at (p := inputPorts w) ⟨0, by simp⟩
def valid : In w 1 := Ports.Signal.at (p := inputPorts w) ⟨1, by simp⟩
def ready : In w 1 := Ports.Signal.at (p := inputPorts w) ⟨2, by simp⟩
def payload : In w w := Ports.Signal.at (p := inputPorts w) ⟨3, by simp⟩
def inReady : Out w 1 := Ports.Signal.at (p := outputPorts w) ⟨0, by simp⟩
def outValid : Out w 1 := Ports.Signal.at (p := outputPorts w) ⟨1, by simp⟩
def outData : Out w w := Ports.Signal.at (p := outputPorts w) ⟨2, by simp⟩

end Pinwheel.Hardware.Stream
