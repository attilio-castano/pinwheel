import Pinwheel.Hardware.Processor.SerialSystemCircuit
import Pinwheel.Hardware.Processor.SerialCircuitProofs
import Pinwheel.Hardware.Processor.LoadableSystemProofs

/-! All-raw shared-MMIO wiring identities. UART pulses cannot affect CPU
request admission: the request network only reads effective reset and the held
core state. The one MMIO register bank sees exactly SerialCircuit's feedback.
-/
namespace Pinwheel.Hardware.Processor.SerialSystemCircuit
open SerialSystemInterface
set_option backward.isDefEq.respectTransparency false

@[simp] theorem effectiveReset_eval (i : Values (Input aw)) (s : Values (Register aw d)) :
    effectiveReset.eval i s = i reset ||| i mode := by
  exact WordOps.wordOr_eval (.input reset) (.input mode) i s

@[simp] theorem quiet_reset (i : Values (Input aw)) (s : Values (Register aw d)) :
    quietPins i s SystemInterface.reset = i reset ||| i mode := effectiveReset_eval i s
@[simp] theorem quiet_gpio (i : Values (Input aw)) (s : Values (Register aw d)) :
    quietPins i s SystemInterface.gpioInput = i gpio := rfl
@[simp] theorem serial_reset (layout : AddressMap.Layout rw aw) (i : Values (Input aw)) (s : Values (Register aw d)) :
    serialPins layout i s SerialInterface.reset = i reset ||| i mode := effectiveReset_eval i s

/-- The request-only core instance has no provider response inputs. This
independence is unconditional, including malformed pre-reset register bits. -/
theorem system_offer_same (a b : Values SystemInterface.Input) (raw : Values (SystemCircuit.Register aw))
    (sameReset : a SystemInterface.reset = b SystemInterface.reset) (o : CoreInterface.Output w) :
    (SystemCircuit.offer o).eval a raw = (SystemCircuit.offer o).eval b raw := by
  have pins : @Eq (Values CoreInterface.Input) (SystemCircuit.requestPins a) (SystemCircuit.requestPins b) := by
    funext width p
    match p with
    | .at ⟨0,_⟩ => exact sameReset
    | .at ⟨k+1,_⟩ => rfl
  simp only [SystemCircuit.offer,Expr.eval_bind,SystemCircuit.requestInput_eval,Expr.eval,pins]

theorem mmio_cpu_same (layout : AddressMap.Layout rw aw) (a b : Values SystemInterface.Input)
    (raw : Values (SystemCircuit.Register aw)) (sameReset : a SystemInterface.reset = b SystemInterface.reset)
    (sameGpio : a SystemInterface.gpioInput = b SystemInterface.gpioInput)
    (p : MmioInterface.Input w) (cpu : (MmioInterface.inputs.position p).val < 7) :
    SystemCircuit.mmioPins layout a raw p = SystemCircuit.mmioPins layout b raw p := by
  match p with
  | .at ⟨0,_⟩ | .at ⟨1,_⟩ | .at ⟨2,_⟩ | .at ⟨3,_⟩ | .at ⟨4,_⟩ | .at ⟨5,_⟩ | .at ⟨6,_⟩ =>
    simp only [SystemCircuit.mmioPins,SystemCircuit.mmioInput,SystemWiring.mmioInput,
      SystemWiring.both,SystemWiring.peripheral,SystemWiring.either,WordOps.wordOr_eval,
      SystemWiring.region,SystemWiring.route,SystemWiring.peripheralBase,
      AddressDecode.runtime_eval,SystemCircuit.requestNetwork,Expr.eval,
      system_offer_same a b raw sameReset,sameReset,sameGpio]
  | .at ⟨k+7,_⟩ => exact False.elim (by change k+7 < 7 at cpu; omega)

theorem cpuMmioInput_eval (layout : AddressMap.Layout rw aw) (i : Values (Input aw))
    (s : Values (Register aw d)) (p : MmioInterface.Input w) :
    (cpuMmioInput layout p).eval i s = SystemCircuit.mmioPins layout (quietPins i s) (systemState s) p := by
  simp only [cpuMmioInput,Expr.eval_bind,Expr.eval]
  rfl

theorem serial_cpu_pins (layout : AddressMap.Layout rw aw) (i : Values (Input aw)) (s : Values (Register aw d))
    (p : MmioInterface.Input w) :
    SerialInterface.cpuPins (serialPins layout i s) p = SystemCircuit.mmioPins layout (quietPins i s) (systemState s) p := by
  match p with
  | .at ⟨0,_⟩ => rfl
  | .at ⟨1,_⟩ | .at ⟨2,_⟩ | .at ⟨3,_⟩ | .at ⟨4,_⟩ | .at ⟨5,_⟩ => exact cpuMmioInput_eval layout i s _
  | .at ⟨6,_⟩ | .at ⟨7,_⟩ | .at ⟨8,_⟩ | .at ⟨9,_⟩ | .at ⟨10,_⟩ => rfl
  | .at ⟨k+11,h⟩ => exact False.elim (by change k+11 < 11 at h; omega)

theorem serialOutput_eval (layout : AddressMap.Layout rw aw) (d : Uart.Timing)
    (i : Values (Input aw)) (s : Values (Register aw d)) (o : SerialInterface.Output w) :
    (serialOutput layout d o).eval i s = (SerialCircuit.circuit d).observe (serialPins layout i s) (serialState s) o := by
  simp only [serialOutput,Expr.eval_bind,Expr.eval]
  rfl

@[simp] theorem loadable_system_reset (layout : AddressMap.Layout rw aw) (d : Uart.Timing)
    (i : Values (Input aw)) (s : Values (Register aw d)) :
    LoadableSystem.systemPins (loadablePins layout d i s) SystemInterface.reset = i reset ||| i mode := rfl
@[simp] theorem loadable_system_gpio (layout : AddressMap.Layout rw aw) (d : Uart.Timing)
    (i : Values (Input aw)) (s : Values (Register aw d)) :
    LoadableSystem.systemPins (loadablePins layout d i s) SystemInterface.gpioInput = i gpio := rfl

/-- Exact shared-bank pins, including all four actual UART frontend outputs.
The CPU-side half is proved independent of these feedback pulses. -/
theorem shared_mmio_pins (layout : AddressMap.Layout rw aw) (d : Uart.Timing)
    (i : Values (Input aw)) (s : Values (Register aw d)) (p : MmioInterface.Input w) :
    SystemCircuit.mmioPins layout (LoadableSystem.systemPins (loadablePins layout d i s)) (systemState s) p =
      SerialCircuit.boundMmioPins d (serialPins layout i s) (serialState s) p := by
  match p with
  | .at ⟨0,_⟩ | .at ⟨1,_⟩ | .at ⟨2,_⟩ | .at ⟨3,_⟩ | .at ⟨4,_⟩ | .at ⟨5,_⟩ | .at ⟨6,_⟩ =>
    rw [mmio_cpu_same layout _ (quietPins i s) (systemState s) (by simp) (by simp) _ (by simp [MmioInterface.inputs,Stream.Ports.interface] <;> decide)]
    rw [← serial_cpu_pins]
    exact (SerialCircuit.cpu_input_eval _ _ _).symm
  | .at ⟨7,_⟩ | .at ⟨8,_⟩ | .at ⟨9,_⟩ | .at ⟨10,_⟩ =>
    exact serialOutput_eval layout d i s _
  | .at ⟨k+11,h⟩ => exact False.elim (by change k+11 < 11 at h; omega)

end Pinwheel.Hardware.Processor.SerialSystemCircuit
