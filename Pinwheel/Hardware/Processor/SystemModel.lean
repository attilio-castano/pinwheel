import Pinwheel.Hardware.Processor.AddressMap
import Pinwheel.Hardware.Processor.CoreModel
import Pinwheel.Hardware.Processor.MmioModel
import Pinwheel.Hardware.Memory.ByteAdapterModel

/-! The serialized core connected to its checked ROM/RAM/device environment.
ROM is an explicit immutable word image. RAM is exclusively owned by the byte
adapter. A RAM acknowledgement commits its effect on the core's completion edge;
MMIO has atomic request/effect/completion. Serial frontend events remain inputs.
Loading an image requires a separate quiescent loader contract. -/
namespace Pinwheel.Hardware.Processor.SystemModel

abbrev Word := BitVec 32
abbrev Rom (rw : Nat) := BitVec rw → Word

structure State (aw : Nat) where
  core : CoreModel.State
  ram : Memory.ByteAdapterModel.State aw
  mmio : MmioModel.State
  fetch : Option CoreModel.FetchReply

structure Input where
  reset : Bool := false
  gpio : Word := 0
  txComplete : Bool := false
  rxArrival : Option (BitVec 8) := none
  framingError : Bool := false

inductive Plan (aw : Nat) where
  | ram (request : Memory.ByteAdapterModel.Request aw)
  | atomic (reply : CoreModel.DataReply)
  | mmio (request : MmioModel.Request)

def sizeCode : Memory.ByteAccess.Size → BitVec 2
  | .byte => 0 | .half => 1 | .word => 2

def faultReply : AddressMap.Fault → CoreModel.DataReply
  | .misaligned => .fault .misaligned | .access => .fault .accessFault

def plan (layout : AddressMap.Layout rw aw) (rom : Rom rw) (intent : RV32I.Semantics.Intent) : Plan aw :=
  match intent with
  | .fenceAll => .atomic (.success 0)
  | .load address size signed =>
      match AddressMap.route layout ⟨.load,size,address⟩ with
      | .error error => .atomic (faultReply error)
      | .ok hit =>
          match hit.region with
          | .rom => .atomic (.success (Memory.ByteAccess.loadCore size signed hit.offset
              (rom (BitVec.ofNat rw hit.wordIndex))))
          | .ram => .ram (.read signed (sizeCode size) (BitVec.ofNat aw hit.wordIndex) hit.offset)
          | .gpio => .mmio ⟨.gpio,BitVec.ofNat 6 hit.wordIndex,false,0⟩
          | .timer => .mmio ⟨.timer,BitVec.ofNat 6 hit.wordIndex,false,0⟩
          | .uart => .mmio ⟨.uart,BitVec.ofNat 6 hit.wordIndex,false,0⟩
  | .store address size data =>
      match AddressMap.route layout ⟨.store,size,address⟩ with
      | .error error => .atomic (faultReply error)
      | .ok hit =>
          match hit.region with
          | .rom => .atomic (.fault .accessFault)
          | .ram => .ram (.store (sizeCode size) (BitVec.ofNat aw hit.wordIndex) hit.offset data)
          | .gpio => .mmio ⟨.gpio,BitVec.ofNat 6 hit.wordIndex,true,data⟩
          | .timer => .mmio ⟨.timer,BitVec.ofNat 6 hit.wordIndex,true,data⟩
          | .uart => .mmio ⟨.uart,BitVec.ofNat 6 hit.wordIndex,true,data⟩

def pendingPlan (layout : AddressMap.Layout rw aw) (rom : Rom rw) (s : State aw) : Option (Plan aw) :=
  match s.core.phase with
  | .dataRequest request => some (plan layout rom request.intent)
  | _ => none

def mmioInput (layout : AddressMap.Layout rw aw) (rom : Rom rw) (i : Input) (s : State aw) : MmioModel.Input :=
  ⟨i.reset, match pendingPlan layout rom s with | some (.mmio request) => some request | _ => none,
    i.gpio,i.txComplete,i.rxArrival,i.framingError⟩

def mmioReply : MmioModel.Response → CoreModel.DataReply
  | .read data => .success data | .stored => .success 0 | .fault _ => .fault .accessFault
def ramReply : Memory.ByteAdapterModel.Response → CoreModel.DataReply
  | .read data => .success data | .stored => .success 0
  | .fault .misaligned => .fault .misaligned | .fault .reservedSize => .fault .accessFault

def ramInput (layout : AddressMap.Layout rw aw) (rom : Rom rw) (i : Input) (s : State aw) : Memory.ByteAdapterModel.Input aw :=
  { reset := i.reset
    offered := match pendingPlan layout rom s with | some (.ram request) => some request | _ => none
    ready := s.core.phase matches .dataResponse _ }

def coreInput (layout : AddressMap.Layout rw aw) (rom : Rom rw) (i : Input) (s : State aw) : CoreModel.Input :=
  { reset := i.reset
    fetchReady := true
    fetchResponse := s.fetch
    dataService := match pendingPlan layout rom s with
      | none => none
      | some (.ram _) => if Memory.ByteAdapterModel.ready s.ram then some .deferred else none
      | some (.atomic reply) => some (.atomic reply)
      | some (.mmio _) => (MmioModel.observe (mmioInput layout rom i s) s.mmio).map (fun r => .atomic (mmioReply r))
    dataResponse := (Memory.ByteAdapterModel.offer s.ram).map ramReply }

def fetchReply (layout : AddressMap.Layout rw aw) (rom : Rom rw) (address : Word) : CoreModel.FetchReply :=
  match AddressMap.route layout ⟨.fetch,.word,address⟩ with
  | .error _ => .accessFault
  | .ok hit => .instruction (rom (BitVec.ofNat rw hit.wordIndex))

def fetchStep (layout : AddressMap.Layout rw aw) (rom : Rom rw) (i : Input) (s : State aw) : Option CoreModel.FetchReply :=
  if i.reset then none else
    match s.core.phase with
    | .fetchRequest => if CoreModel.aligned s.core.arch then some (fetchReply layout rom s.core.arch.pc) else none
    | .fetchResponse => none
    | _ => s.fetch

def step (layout : AddressMap.Layout rw aw) (rom : Rom rw) (i : Input) (s : State aw) : State aw :=
  ⟨CoreModel.step (coreInput layout rom i s) s.core,
    Memory.ByteAdapterModel.step (ramInput layout rom i s) s.ram,
    MmioModel.step (mmioInput layout rom i s) s.mmio,
    fetchStep layout rom i s⟩

structure Output where
  core : CoreModel.Output
  gpio : Word
  tx : Option (BitVec 8)

def observe (layout : AddressMap.Layout rw aw) (rom : Rom rw) (i : Input) (s : State aw) : Output :=
  ⟨CoreModel.observe (coreInput layout rom i s) s.core,
    if i.reset then 0 else s.mmio.gpioOut, if i.reset then none else s.mmio.tx⟩

def component (layout : AddressMap.Layout rw aw) (rom : Rom rw) : Timed.Component Input (State aw) Output :=
  ⟨step layout rom,observe layout rom⟩

def initial (contents : BitVec aw → Word) (q : Word) : State aw :=
  ⟨CoreModel.initial,⟨⟨contents,q⟩,none⟩,MmioModel.initial,none⟩

theorem reset_core (layout : AddressMap.Layout rw aw) (rom : Rom rw) (i : Input) (s : State aw)
    (h : i.reset = true) : (step layout rom i s).core = CoreModel.initial := by
  exact CoreModel.reset_step _ _ h

theorem reset_mmio (layout : AddressMap.Layout rw aw) (rom : Rom rw) (i : Input) (s : State aw)
    (h : i.reset = true) : (step layout rom i s).mmio = MmioModel.initial := by
  simp [step,MmioModel.step,mmioInput,h]

theorem reset_ram (layout : AddressMap.Layout rw aw) (rom : Rom rw) (i : Input) (s : State aw)
    (h : i.reset = true) : (step layout rom i s).ram.memory = s.ram.memory ∧
      (step layout rom i s).ram.pending = none := by
  simp [step,Memory.ByteAdapterModel.step,Memory.ByteAdapterModel.command,ramInput,h,Memory.SinglePort.step]

end Pinwheel.Hardware.Processor.SystemModel
