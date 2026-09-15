import Pinwheel.Binary.ImageProofs
import Pinwheel.Compile.I2CLoopCorrectness

namespace Pinwheel.Binary
open Engine.Reactive

def load (m : Fetch.Machine) (bytes : List Byte) : Fetch.Machine × Bool :=
  match decode bytes with
  | none => (m, false)
  | some image => Fetch.load m image.store

def execute (bytes : List Byte) (incoming : Nat → Inputs) (n : Nat) : Option State := do
  let image ← decode bytes
  return Fetch.run image.store (Fetch.start image.store (incoming 0)) incoming n

theorem execute_encode (image : Image) (incoming : Nat → Inputs) (n : Nat) :
    execute (encode image) incoming n =
      some (Fetch.run image.store (Fetch.start image.store (incoming 0)) incoming n) := by
  simp [execute, decode_encode]
  done

theorem load_encode (m : Fetch.Machine) (image : Image) :
    load m (encode image) = Fetch.load m image.store := by
  simp [load, decode_encode]
  done

theorem load_reject (m : Fetch.Machine) (bytes : List Byte) (h : decode bytes = none) :
    load m bytes = (m, false) := by
  simp [load, h]
  done

theorem counted_i2c_eq (cfg : Pinwheel.I2C.Config) (r : Pinwheel.I2C.Request)
    (incoming : Nat → Pinwheel.I2C.Bus) (n : Nat) :
    execute (encode (.counted (Compile.I2CLoop.program cfg r)))
      (fun t => Compile.I2C.encodeInputs (incoming t)) n = some (Compile.I2C.execute cfg r incoming n) := by
  simpa only [execute_encode, Image.store, Compile.I2CLoop.execute] using
    congrArg some (Compile.I2CLoop.execute_eq cfg r incoming n)
  done

theorem explicit_agrees (p : Program) : Fetch.Agrees (Fetch.Store.ofProgram p) p := by
  exact ⟨fun _ => rfl, rfl, rfl⟩
  done

theorem execute_explicit (p : Program) (incoming : Nat → Inputs) (n : Nat) :
    execute (encode (.explicit p)) incoming n = some (run p (start p (incoming 0)) incoming n) := by
  simp only [execute_encode, Image.store, Fetch.run_eq _ _ (explicit_agrees p), Fetch.start,
    Fetch.enter_eq _ _ (explicit_agrees p), start]
  done

/-- The two binary images preserve the same complete state for every sampled bus history. -/
theorem binary_i2c_eq (cfg : Pinwheel.I2C.Config) (r : Pinwheel.I2C.Request)
    (incoming : Nat → Pinwheel.I2C.Bus) (n : Nat) :
    execute (encode (.counted (Compile.I2CLoop.program cfg r)))
      (fun t => Compile.I2C.encodeInputs (incoming t)) n =
    execute (encode (.explicit (Compile.I2C.program cfg r)))
      (fun t => Compile.I2C.encodeInputs (incoming t)) n := by
  simp only [counted_i2c_eq, execute_explicit, Compile.I2C.execute]
  done

end Pinwheel.Binary
