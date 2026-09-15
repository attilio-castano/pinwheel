import Pinwheel.Hardware.Reactive.State
import Pinwheel.Hardware.Interface

namespace Pinwheel.Hardware.Reactive

def inputs : Array (Sigma Input) :=
  #[⟨1, .reset⟩, ⟨1, .start⟩, ⟨2, .incoming⟩, ⟨3, .idleLevels⟩,
    ⟨3, .idleEnabled⟩, ⟨8, .last⟩, ⟨64, .current⟩, ⟨64, .successor⟩]

def inputLabel : {w : Nat} → Input w → String
  | _, .reset => "reset" | _, .start => "start" | _, .incoming => "incoming"
  | _, .idleLevels => "idle_levels" | _, .idleEnabled => "idle_enabled" | _, .last => "last"
  | _, .current => "current" | _, .successor => "successor"

def inputPosition : {w : Nat} → Input w → Fin inputs.size
  | _, .reset => ⟨0, by decide⟩ | _, .start => ⟨1, by decide⟩
  | _, .incoming => ⟨2, by decide⟩ | _, .idleLevels => ⟨3, by decide⟩
  | _, .idleEnabled => ⟨4, by decide⟩ | _, .last => ⟨5, by decide⟩
  | _, .current => ⟨6, by decide⟩ | _, .successor => ⟨7, by decide⟩

theorem input_at_position (p : Input w) : inputs[(inputPosition p).val] = ⟨w, p⟩ := by
  cases p <;> rfl

def inputInterface : Hardware.Interface Input where
  size := inputs.size
  signal := fun k => inputs[k.val]
  position := inputPosition
  signal_position := input_at_position
  label := inputLabel
  unique := by decide

def registers : Array (Sigma Register) :=
  #[⟨3, .mode⟩, ⟨8, .pc⟩, ⟨8, .remaining⟩, ⟨8, .waitLeft⟩, ⟨3, .levels⟩, ⟨3, .enabled⟩] ++
    Array.ofFn (fun k : Fin 16 => ⟨1, .sample k⟩)

def registerLabel : {w : Nat} → Register w → String
  | _, .mode => "mode" | _, .pc => "pc" | _, .remaining => "remaining" | _, .waitLeft => "wait_left"
  | _, .levels => "levels" | _, .enabled => "enabled" | _, .sample k => s!"sample{k.val}"

def registerPosition : {w : Nat} → Register w → Fin registers.size
  | _, .mode => ⟨0, by decide⟩ | _, .pc => ⟨1, by decide⟩
  | _, .remaining => ⟨2, by decide⟩ | _, .waitLeft => ⟨3, by decide⟩
  | _, .levels => ⟨4, by decide⟩ | _, .enabled => ⟨5, by decide⟩
  | _, .sample k => ⟨6 + k.val, by simpa [registers] using Nat.add_lt_add_left k.isLt 6⟩

theorem register_at_position (p : Register w) :
    registers[(registerPosition p).val] = ⟨w, p⟩ := by
  cases p <;> simp [registers, registerPosition]
  done

def registerInterface : Hardware.Interface Register where
  size := registers.size
  signal := fun k => registers[k.val]
  position := registerPosition
  signal_position := register_at_position
  label := registerLabel
  unique := by decide

def outputs : Array (Sigma Output) := registers.map (fun ⟨w, r⟩ => ⟨w, .state r⟩) ++
  #[⟨8, .readA⟩, ⟨8, .readB⟩, ⟨1, .busy⟩]

def outputLabel : {w : Nat} → Output w → String
  | _, .state r => registerLabel r | _, .readA => "read_a" | _, .readB => "read_b" | _, .busy => "busy"

def outputPosition : {w : Nat} → Output w → Fin outputs.size
  | _, .state r => ⟨(registerPosition r).val, by simpa [outputs] using Nat.lt_add_right 3 (registerPosition r).isLt⟩
  | _, .readA => ⟨22, by simp [outputs, registers]⟩
  | _, .readB => ⟨23, by simp [outputs, registers]⟩
  | _, .busy => ⟨24, by simp [outputs, registers]⟩

theorem output_at_position (p : Output w) : outputs[(outputPosition p).val] = ⟨w, p⟩ := by
  cases p <;> simp [outputs, outputPosition, registers]
  rename_i r
  cases r <;> simp [registerPosition]
  done

def outputInterface : Hardware.Interface Output where
  size := outputs.size
  signal := fun k => outputs[k.val]
  position := outputPosition
  signal_position := output_at_position
  label := outputLabel
  unique := by decide +kernel

end Pinwheel.Hardware.Reactive
