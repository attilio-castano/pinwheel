import Pinwheel.Hardware.Storage.SramController
import Pinwheel.Hardware.Interface

/-! Shared composition and physical ownership description of the existing SRAM chips.
This module adds no pipeline state or placement constraints. -/
namespace Pinwheel.Hardware.Storage.SramAssembly
open Pinwheel.Hardware Pinwheel.Hardware.Storage Pinwheel.Hardware.Loader
open Pinwheel.Hardware.Storage.SramController
abbrev Register := SramController.Register

def observerExpr (e : HostResult.E w) :
    Expr (Observed (Reads Chip.Pin) (Out Machine.Output)) HostResult.Register w :=
  e.bind (fun p => match p with
    | .input p => .input (.input (.base p))
    | .output o => .input (.output (.base o))) (.reg)

def observer : Observer (Reads Chip.Pin) (Out Machine.Output) HostResult.Register (Out Chip.Output) where
  next := fun r => observerExpr (HostResult.observer.next r)
  output := fun o => match o with
    | .base p => observerExpr (HostResult.observer.output p)
    | .port p => .input (.output (.port p))

def chip (direct : Bool) := observer.wrap
  ((bypass Chip.pinMap).wrap ((bypass Feeder.sampler).wrap ((bypass Serial.receiver).wrap (core direct))))

def extras (direct : Bool) : Array (Sigma Extra) :=
  (if direct then Array.ofFn (fun k : Fin 32 => ⟨55, .scratch (BitVec.ofFin k)⟩) else #[]) ++
    #[⟨64, .startWord⟩, ⟨1, .startPending⟩]

def extraLabel : {w : Nat} → Extra w → String
  | _, .scratch k => s!"scratch_word{k.toNat}"
  | _, .startWord => "start_word"
  | _, .startPending => "start_pending"

/-- Omitted storage registers must never be referenced by the emitted
controller. moduleText rejects any such reference instead of tying it to zero. -/
def registers (direct : Bool) : Array (Sigma Register) :=
  (Backend.registers.filter fun ⟨_, r⟩ => match r with
    | .word _ _ => false | .index _ _ => !direct | _ => true).map
      (fun ⟨w, r⟩ => ⟨w, .inner r⟩) ++
    (extras direct).map (fun ⟨w, r⟩ => ⟨w, .extra r⟩)

def chipRegisters (direct : Bool) : Array (Sigma (Chip.Register Register)) :=
  (registers direct).map (fun ⟨w, r⟩ => ⟨w, .inner (.inner (.inner r))⟩) ++
    Backend.Policy.serialRegisters.map (fun ⟨w, r⟩ => ⟨w, .inner (.inner (.extra r))⟩) ++
    Backend.Policy.sampledRegisterList.map (fun ⟨w, r⟩ => ⟨w, .inner (.extra r)⟩)

def ports : Array (Sigma Port) :=
  #[⟨9, .address false⟩, ⟨9, .address true⟩, ⟨64, .data⟩, ⟨1, .write⟩, ⟨1, .read⟩]
def portLabel : {w : Nat} → Port w → String
  | _, .address b => if b then "mem_addr1" else "mem_addr0"
  | _, .data => "mem_data" | _, .write => "mem_write" | _, .read => "mem_read"

def portPosition : {w : Nat} → Port w → Fin ports.size
  | _, .address false => ⟨0, by decide⟩
  | _, .address true => ⟨1, by decide⟩
  | _, .data => ⟨2, by decide⟩
  | _, .write => ⟨3, by decide⟩
  | _, .read => ⟨4, by decide⟩

theorem port_at_position (p : Port w) : ports[(portPosition p).val] = ⟨w, p⟩ := by
  cases p with
  | address b => exact Bool.rec rfl rfl b
  | data | write | read => rfl

/-- Completeness and unique names for the actual controller request ports. -/
def requestInterface : Interface Port where
  size := ports.size
  signal := fun k => ports[k.val]
  position := portPosition
  signal_position := port_at_position
  label := portLabel
  unique := by decide

def inputs (is : Array (Sigma I)) : Array (Sigma (Reads I)) :=
  is.map (fun ⟨w, p⟩ => ⟨w, .base p⟩) ++ #[⟨64, .q false⟩, ⟨64, .q true⟩]
def inputLabel (label : {w : Nat} → I w → String) : {w : Nat} → Reads I w → String
  | _, .base p => label p | _, .q b => if b then "mem_q1" else "mem_q0"
def outputs (os : Array (Sigma O)) : Array (Sigma (Out O)) :=
  os.map (fun ⟨w, o⟩ => ⟨w, .base o⟩) ++ requestInterface.ports.map (fun ⟨w, p⟩ => ⟨w, .port p⟩)
def outputLabel (label : {w : Nat} → O w → String) : {w : Nat} → Out O w → String
  | _, .base o => label o | _, .port p => portLabel p

def coreText (direct : Bool) : Except String String :=
  Netlist.moduleText "pinwheel_sram_core_controller" (core direct)
    (inputs Machine.inputs) (registers direct) (outputs Machine.outputs)
    (inputLabel Machine.inputLabel) (Backend.Policy.registerLabel extraLabel) (outputLabel Machine.outputLabel)

abbrev FullRegister := Extended (Chip.Register Register) HostResult.Register

def fullRegisters (direct : Bool) : Array (Sigma FullRegister) :=
  (chipRegisters direct).map (fun ⟨w, r⟩ => ⟨w, Extended.inner r⟩) ++
    HostResult.registers.map (fun ⟨w, r⟩ => ⟨w, Extended.extra r⟩)

def registerLabel : {w : Nat} → FullRegister w → String
  | _, .inner q => Backend.Policy.chipRegisterLabel extraLabel q
  | _, .extra q => HostResult.label q

/-- Semantic state owners, not a placement partition. `referenceImage` is the
proof's dictionary bookkeeping and must never occur in emitted state. -/
inductive Owner where
  | indexMaps | uploadScratch | imageMetadata | loader | fetchState | execution
  | pinSampler | serialReceiver | resultObserver | referenceImage
  deriving DecidableEq, BEq, Repr

def Owner.label : Owner → String
  | .indexMaps => "index_maps" | .uploadScratch => "upload_scratch"
  | .imageMetadata => "image_metadata" | .loader => "loader"
  | .fetchState => "fetch_state" | .execution => "execution"
  | .pinSampler => "pin_sampler" | .serialReceiver => "serial_receiver"
  | .resultObserver => "result_observer" | .referenceImage => "reference_image"

def physicalOwners : Array Owner :=
  #[.indexMaps, .uploadScratch, .imageMetadata, .loader, .fetchState, .execution,
    .pinSampler, .serialReceiver, .resultObserver]

def coreOwner : {w : Nat} → Register w → Owner
  | _, .inner (.word _ _) => .referenceImage
  | _, .inner (.index _ _) => .indexMaps
  | _, .inner (.idle _) | _, .inner (.last _) => .imageMetadata
  | _, .inner (.control _) => .loader
  | _, .inner (.core _) => .execution
  | _, .inner .current | _, .extra .startWord | _, .extra .startPending => .fetchState
  | _, .extra (.scratch _) => .uploadScratch

def chipOwner : {w : Nat} → Chip.Register Register w → Owner
  | _, .inner (.inner (.inner r)) => coreOwner r
  | _, .inner (.inner (.extra _)) => .serialReceiver
  | _, .inner (.extra _) => .pinSampler
  | _, .extra r => nomatch r

/-- Exhaustive typed classification: renaming a register cannot change its owner. -/
def owner : {w : Nat} → FullRegister w → Owner
  | _, .inner r => chipOwner r
  | _, .extra _ => .resultObserver

/-- Preserve the logical map coordinates without interpreting emitted names. -/
def indexLocation : {w : Nat} → FullRegister w → Option (Bool × BitVec 8)
  | _, .inner (.inner (.inner (.inner (.inner (.index bank word))))) => some (bank, word)
  | _, _ => none

structure StateSlot where
  name : String
  width : Nat
  owner : Owner
  indexLocation : Option (Bool × BitVec 8)
  deriving Repr

/-- The same register list and labels consumed by `chipText`, including all
named pre-mapping bits. Mapped-away bits are identified by the artifact census. -/
def stateSlots (direct : Bool) : Array StateSlot :=
  (fullRegisters direct).map fun ⟨w, r⟩ =>
    ⟨"controller.r_" ++ registerLabel r, w, owner r, indexLocation r⟩

def ownerBits (direct : Bool) (o : Owner) : Nat :=
  (stateSlots direct).foldl (fun n slot => if slot.owner == o then n + slot.width else n) 0

def macroName (b : Bool) : String := if b then "memory.storage1" else "memory.storage0"
def response (b : Bool) : Reads I 64 := .q b
def macroAddress (b : Bool) : Port 9 := .address b

structure Crossing where
  name : String
  width : Nat
  producer : String
  consumers : Array String
  phase : Interface.Phase
  macroPort : String
  physicalWidth : Nat
  deriving Repr

/-- Requests settle before the SRAM edge; Q is produced after that edge.
These are interface phases, not added registers or nanosecond timing bounds. -/
def crossings (direct : Bool) : Array Crossing :=
  requestInterface.ports.map (fun ⟨w, p⟩ =>
    ⟨portLabel p, w, "controller", (match p with
      | .address b => #[macroName b]
      | _ => #[macroName false, macroName true]), .before,
      (match p with
        | .address _ => "A_ADDR" | .data => "A_DIN" | .read => "A_REN" | .write => "A_WEN"),
      (match p with | .address _ => if direct then 9 else 6 | _ => w)⟩) ++
  #[false, true].map (fun b =>
    ⟨inputLabel Backend.Policy.chipInputLabel (response (I := Chip.Pin) b), 64, macroName b,
      #["controller"], .after, "A_DOUT", 64⟩)

def chipText (direct : Bool) : Except String String :=
  Netlist.moduleText "pinwheel_sram_controller" (chip direct)
    (inputs Backend.Policy.chipInputs) (fullRegisters direct) (outputs Backend.Policy.chipOutputs)
    (inputLabel Backend.Policy.chipInputLabel) registerLabel (outputLabel Backend.Policy.chipOutputLabel)

/-- Proposed locality groups. Shared combinational producers are assigned by
their actual consumers in the mapped graph; these are not placement constraints. -/
def Owner.region : Owner → String
  | .indexMaps | .fetchState | .execution => "fetch"
  | .uploadScratch | .imageMetadata | .loader => "configuration"
  | .pinSampler | .serialReceiver | .resultObserver => "interface"
  | .referenceImage => "unimplemented"

inductive Computation : Nat → Type where
  | successor : Computation 64
  | candidate : Bool → Computation 8
  | readAddress : Bool → Computation 9
  | writeAddress : Computation 9
  | writeData : Computation 64
  | write : Computation 1

def computations : Array (Sigma Computation) :=
  #[⟨64, .successor⟩, ⟨8, .candidate false⟩, ⟨8, .candidate true⟩,
    ⟨9, .readAddress false⟩, ⟨9, .readAddress true⟩,
    ⟨9, .writeAddress⟩, ⟨64, .writeData⟩, ⟨1, .write⟩]

def Computation.label : {w : Nat} → Computation w → String
  | _, .successor => "successor"
  | _, .candidate b => if b then "candidate1" else "candidate0"
  | _, .readAddress b => if b then "read_address1" else "read_address0"
  | _, .writeAddress => "write_address"
  | _, .writeData => "write_data"
  | _, .write => "write_enable"

/-- Expand only the existing shared successor binding for expression lookup.
The emitter's cache restores sharing; the circuit is never emitted from this. -/
def resolve (e : Expr W Register w) : SramController.E w :=
  e.bind (fun p => match p with
    | .input q => .input q | .wire => SramController.successor) (.reg)

def computationExpr (direct : Bool) : {w : Nat} → Computation w → SramController.E w
  | _, .successor => SramController.successor
  | _, .candidate b => resolve (if b then sched (Dispatch.candidateExpr true) else address0)
  | _, .readAddress b => resolve (SramController.readAddress direct b)
  | _, .writeAddress => SramController.writeAddress direct
  | _, .writeData => SramController.writeData direct
  | _, .write => SramController.write direct

private def throughFeeder (f : Feeder J X I) (e : Expr I R w) : Expr J (Extended R X) w :=
  e.inner (fun p => Feeder.outer (f.input p))

/-- Apply exactly the assembly's existing input adapters and register lifts. -/
def chipExpr (e : SramController.E w) : Expr (Reads Chip.Pin) FullRegister w :=
  (throughFeeder (bypass Chip.pinMap)
    (throughFeeder (bypass Feeder.sampler)
      (throughFeeder (bypass Serial.receiver) e))).inner (fun p => .input p)

/-- Locate computations in the actual emitted operation cache. A changed
expression that would require another operation is rejected, not emitted. -/
def computationNames (direct : Bool) : Except String (Array (String × Nat × String)) := do
  let rn : {w : Nat} → FullRegister w → String := fun r => "%r_" ++ registerLabel r
  let names : {w : Nat} → Reads Chip.Pin w → String :=
    fun p => "%" ++ inputLabel Backend.Policy.chipInputLabel p
  let (_, buffer) ← (Netlist.emitBody (fullRegisters direct) (outputs Backend.Policy.chipOutputs)
    rn (chip direct) names).run {}
  let (probes, after) ← (computations.mapM fun ⟨w, c⟩ => do
    let value ← Emit.expression names rn (chipExpr (computationExpr direct c))
    return (c.label, w, value) : Emit.M _).run buffer
  if after.serial != buffer.serial then
    throw "Computation description is not present in the emitted circuit"
  return probes

end Pinwheel.Hardware.Storage.SramAssembly
