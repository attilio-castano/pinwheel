import Pinwheel.Hardware.Processor.SystemCircuit
import Pinwheel.Hardware.Processor.CoreCertified
import Pinwheel.Hardware.Processor.MmioCircuitProofs
import Pinwheel.Hardware.Processor.SystemModelProofs
import Pinwheel.Hardware.Memory.ByteAdapterRefinement

/-! Raw component projections and reset composition. No ROM/provider invariant
is assumed before reset; RAM contents/Q and inactive byte metadata are retained. -/
namespace Pinwheel.Hardware.Processor.SystemCircuit

set_option backward.isDefEq.respectTransparency false

abbrev coreValues (s : Values (Register aw)) : Values CoreCircuit.Register := fun r => s (core r)
abbrev ramValues (s : Values (Register aw)) : Values (Memory.ByteAdapterCircuit.Register aw) := fun r => s (ram r)
abbrev mmioValues (s : Values (Register aw)) : Values MmioCircuit.Register := fun r => s (mmio r)
abbrev fetchValues (s : Values (Register aw)) : Values Fetch := fun r => s (fetch r)

def decode (i : Values Input) : SystemModel.Input :=
  ⟨i reset == 1, i gpioInput, i txComplete == 1,
    if i rxValid = 1 then some (i rxData) else none, i framingError == 1⟩

def fetchView (s : Values (Register aw)) : Option CoreModel.FetchReply :=
  if s fetchValid = 1 then
    some (if s fetchFault = 1 then .accessFault else .instruction (s fetchData)) else none

def view (s : Values (Register aw)) : SystemModel.State aw :=
  ⟨CoreCircuit.view (coreValues s), Memory.ByteAdapterCircuit.view (ramValues s),
    MmioCircuit.view (mmioValues s), fetchView s⟩

/-- Physical core representation and connected ownership/snapshot coherence.
Inactive byte/MMIO/fetch payload latches need not be canonical. -/
def Valid (layout : AddressMap.Layout rw aw) (rom : SystemModel.Rom rw)
    (s : Values (Register aw)) : Prop :=
  CoreCircuit.Valid (coreValues s) ∧ SystemModel.Valid layout rom (view s)

variable (layout : AddressMap.Layout rw aw) (rom : SystemModel.Rom rw)
  (romFits : rw ≤ 30) (ramFits : aw ≤ 30)

def corePins (i : Values Input) (s : Values (Register aw)) : Values CoreInterface.Input :=
  fun p => (coreInput layout rom romFits ramFits p).eval i s

def ramPins (i : Values Input) (s : Values (Register aw)) : Values (Memory.ByteAdapterInterface.Input aw) :=
  fun p => (ramInput layout ramFits p).eval i s

def mmioPins (i : Values Input) (s : Values (Register aw)) : Values MmioInterface.Input :=
  fun p => (mmioInput layout p).eval i s

@[simp] theorem corePins_reset (i : Values Input) (s : Values (Register aw)) :
    corePins layout rom romFits ramFits i s CoreInterface.reset = i reset := rfl
@[simp] theorem ramPins_reset (i : Values Input) (s : Values (Register aw)) :
    ramPins layout ramFits i s Memory.ByteAdapterInterface.reset = i reset := rfl
@[simp] theorem mmioPins_reset (i : Values Input) (s : Values (Register aw)) :
    mmioPins layout i s MmioInterface.reset = i reset := rfl

theorem core_step (i : Values Input) (s : Values (Register aw)) :
    @Eq (Values CoreCircuit.Register)
      (coreValues ((circuit layout rom romFits ramFits).step i s))
      (CoreCircuit.circuit.step (corePins layout rom romFits ramFits i s) (coreValues s)) := by
  funext b r
  simp only [coreValues, core, Circuit.step, circuit, Expr.eval_bind, Expr.eval]
  rfl

theorem ram_step (i : Values Input) (s : Values (Register aw)) :
    @Eq (Values (Memory.ByteAdapterCircuit.Register aw))
      (ramValues ((circuit layout rom romFits ramFits).step i s))
      ((Memory.ByteAdapterCircuit.circuit aw).step (ramPins layout ramFits i s) (ramValues s)) := by
  funext b r
  simp only [ramValues, ram, Circuit.step, circuit, Expr.eval_bind, Expr.eval]
  rfl

theorem mmio_step (i : Values Input) (s : Values (Register aw)) :
    @Eq (Values MmioCircuit.Register)
      (mmioValues ((circuit layout rom romFits ramFits).step i s))
      (MmioCircuit.circuit.step (mmioPins layout i s) (mmioValues s)) := by
  funext b r
  simp only [mmioValues, mmio, Circuit.step, circuit, Expr.eval_bind, Expr.eval]
  rfl

theorem core_output (i : Values Input) (s : Values (Register aw)) (o : CoreInterface.Output b) :
    (circuit layout rom romFits ramFits).observe i s (.left o) =
      CoreCircuit.circuit.observe (corePins layout rom romFits ramFits i s) (coreValues s) o := by
  simp only [Circuit.observe, circuit, Expr.eval_bind, Expr.eval]
  rfl

theorem mmio_output (i : Values Input) (s : Values (Register aw)) (o : MmioInterface.Output b) :
    (circuit layout rom romFits ramFits).observe i s (.right o) =
      MmioCircuit.circuit.observe (mmioPins layout i s) (mmioValues s) o := by
  simp only [Circuit.observe, circuit, mmioOutput, Expr.eval_bind, Expr.eval]
  rfl

/-- The reset image depends on the pre-edge RAM image, never on a zero-memory
assumption or unused request inputs. -/
def resetState (s : Values (Register aw)) : SystemModel.State aw :=
  SystemModel.initial (view s).ram.memory.contents (view s).ram.memory.q

theorem reset_fetch (i : Values Input) (s : Values (Register aw)) (h : i reset = 1) :
    fetchView ((circuit layout rom romFits ramFits).step i s) = none := by
  simp [fetchView, fetchValid, fetch, Circuit.step, circuit, fetchNext, SystemWiring.fetchNext,
    SystemWiring.both, requestNetwork, Expr.eval, h]

theorem reset_view (i : Values Input) (s : Values (Register aw)) (h : i reset = 1) :
    view ((circuit layout rom romFits ramFits).step i s) = resetState s := by
  unfold view
  rw [core_step, ram_step, mmio_step,
    CoreCircuit.reset_view _ _ (by simpa using h),
    Memory.ByteAdapterCircuit.reset_view _ _ (by simpa using h),
    MmioCircuit.reset_view _ _ (by simpa using h), reset_fetch layout rom romFits ramFits i s h]
  rfl

theorem reset_valid (i : Values Input) (s : Values (Register aw)) (h : i reset = 1) :
    Valid layout rom ((circuit layout rom romFits ramFits).step i s) := by
  refine ⟨?_, ?_⟩
  · rw [core_step]
    exact (CoreCircuit.reset_recovery _ _ (by simpa using h)).1
  · rw [reset_view layout rom romFits ramFits i s h]
    exact SystemModel.initial_valid _ _ _ _

end Pinwheel.Hardware.Processor.SystemCircuit
