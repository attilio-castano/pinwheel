import Pinwheel.Hardware.Execution.Stores
import Pinwheel.Hardware.Execution.DecodeProofs
import Pinwheel.Compile.I2CReadProofs

namespace Pinwheel.Hardware.Execution
open Engine.Reactive

/-- Raw port writes: busy blocks both banks; only the addressed register changes. -/
theorem write_correct (old new : Expr Input R w) (index : Bool) (address : BitVec 8)
    (i : Inputs) (registers : Values R) :
    (writeWord old new index address).eval i.values registers =
      writeValue i (old.eval i.values registers) (new.eval i.values registers) index address := by
  cases hw : i.write <;> cases hb : i.busy <;> cases hi : i.indexBank <;> cases index <;>
    by_cases ha : i.address = address <;> simp [writeWord, accept, Expr.eval, Inputs.values, writeValue, hw, hb, hi, ha]
  done

theorem direct_tick (i : Inputs) (words : Words) (r : DirectReg w) :
    directCircuit.step i.values (directValues words) r = directValues (directTick i words) r := by
  cases r <;> simp [Circuit.step, directCircuit, write_correct, directValues, directTick, Expr.eval, Inputs.values]
  done

theorem indexed_tick (i : Inputs) (image : Indexed) (r : IndexedReg w) :
    indexedCircuit.step i.values (indexedValues image) r = indexedValues (indexedTick i image) r := by
  cases r <;> simp [Circuit.step, indexedCircuit, write_correct, indexedValues, indexedTick, Expr.eval, Inputs.values]
  done

theorem direct_observe (i : Inputs) (words : Words) (p : Port w) :
    directCircuit.observe i.values (directValues words) (.a p) = value words[i.readA.toNat] p ∧
    directCircuit.observe i.values (directValues words) (.b p) = value words[i.readB.toNat] p := by
  simp [Circuit.observe, directCircuit, logic_correct, directRead, readTree_correct, Expr.eval, Inputs.values, directValues]
  done

theorem indexed_observe (i : Inputs) (image : Indexed) (p : Port w) :
    indexedCircuit.observe i.values (indexedValues image) (.a p) =
      value image.dictionary[image.addresses[i.readA.toNat].toNat] p ∧
    indexedCircuit.observe i.values (indexedValues image) (.b p) =
      value image.dictionary[image.addresses[i.readB.toNat].toNat] p := by
  simp [Circuit.observe, indexedCircuit, logic_correct, indexedRead, readTree_correct, Expr.eval, Inputs.values, indexedValues]
  done

theorem direct_busy (i : Inputs) (words : Words) (h : i.busy = true) : directTick i words = words := by
  simp [directTick, writeValue, h]
  done

theorem indexed_busy (i : Inputs) (image : Indexed) (h : i.busy = true) : indexedTick i image = image := by
  simp [indexedTick, writeValue, h]
  done

theorem direct_run (p : Image) (s : State 255 15) (incoming : Nat → Engine.Reactive.Inputs) (n : Nat) :
    Fetch.run (directStore (imageWords p) p.idle p.last) s incoming n = run p s incoming n := by
  exact Fetch.run_eq _ _ (direct_agrees p) s incoming n

theorem indexed_run (p : Image) (lowered : {image : Indexed // image.expand = imageWords p})
    (s : State 255 15) (incoming : Nat → Engine.Reactive.Inputs) (n : Nat) :
    Fetch.run (lowered.val.store p.idle p.last) s incoming n = run p s incoming n := by
  exact Fetch.run_eq _ _ (indexed_agrees p lowered.val lowered.property) s incoming n

/-- Compose packed/indexed execution with the universal register-read compiler proof. -/
theorem indexed_read (cfg : Pinwheel.I2C.Config) (request : Pinwheel.I2C.RegisterRead.Request)
    (lowered : {image : Indexed // image.expand = imageWords (Compile.I2CRead.program cfg request)})
    (incoming : Nat → Pinwheel.I2C.Bus) (n : Nat) :
    Fetch.run (lowered.val.store {} 154)
      (start (Compile.I2CRead.program cfg request) (Compile.I2C.encodeInputs (incoming 0)))
      (fun t => Compile.I2C.encodeInputs (incoming t)) n =
      Compile.I2CRead.lift request (Pinwheel.I2C.RegisterRead.run cfg
        (Pinwheel.I2C.RegisterRead.initial cfg) incoming n) := by
  exact (indexed_run _ lowered _ _ n).trans (Compile.I2CRead.run_simulation cfg request incoming n)

end Pinwheel.Hardware.Execution
