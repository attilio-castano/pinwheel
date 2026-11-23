import Pinwheel.Hardware.Processor.CoreModel
import Pinwheel.Hardware.Stream.Ports

/-! Serialized core pins. A data service is either deferred acceptance or an
atomic completion. A deferred reply is consumed only after acceptance. Fault
codes0/1/2 mean success/misaligned/access; raw3 also denotes access fault.
Reset cancels provider ownership synchronously. Retirement and trap pulses are
pre-edge observations of the action committed at that edge. -/
namespace Pinwheel.Hardware.Processor.CoreInterface

abbrev inputPorts : Stream.Ports where
  size := 12
  widths := fun k => #[1,1,1,1,32,1,1,2,32,1,2,32][k]
  names := fun k => #["reset", "fetch_ready", "fetch_response_valid", "fetch_response_fault",
    "fetch_response_data", "data_service_valid", "data_service_atomic", "data_service_fault",
    "data_service_data", "data_response_valid", "data_response_fault", "data_response_data"][k]
  distinct := by decide +kernel

abbrev outputPorts : Stream.Ports where
  size := 30
  widths := fun k => #[1,1,32,1,1,1,32,2,1,32,1,1,32,32,32,1,5,32,1,32,1,32,4,32,1,32,1,32,4,32][k]
  names := fun k => #["cancel", "fetch_valid", "fetch_address", "fetch_response_ready",
    "data_valid", "data_write", "data_address", "data_size", "data_signed", "data_store_data",
    "data_response_ready", "retire_valid", "retire_pc", "retire_instruction", "retire_next_pc",
    "retire_write_enable", "retire_write_rd", "retire_write_data", "trap_valid", "trap_pc",
    "trap_instruction_valid", "trap_instruction", "trap_cause", "trap_address", "terminal_valid",
    "terminal_pc", "terminal_instruction_valid", "terminal_instruction", "terminal_cause", "terminal_address"][k]
  distinct := by decide +kernel

abbrev Input := inputPorts.Signal
abbrev Output := outputPorts.Signal
def inputs : Interface Input := inputPorts.interface
def outputs : Interface Output := outputPorts.interface

def reset : Input 1 := .at ⟨0, by decide⟩
def fetchReady : Input 1 := .at ⟨1, by decide⟩
def fetchResponseValid : Input 1 := .at ⟨2, by decide⟩
def fetchResponseFault : Input 1 := .at ⟨3, by decide⟩
def fetchResponseData : Input 32 := .at ⟨4, by decide⟩
def dataServiceValid : Input 1 := .at ⟨5, by decide⟩
def dataServiceAtomic : Input 1 := .at ⟨6, by decide⟩
def dataServiceFault : Input 2 := .at ⟨7, by decide⟩
def dataServiceData : Input 32 := .at ⟨8, by decide⟩
def dataResponseValid : Input 1 := .at ⟨9, by decide⟩
def dataResponseFault : Input 2 := .at ⟨10, by decide⟩
def dataResponseData : Input 32 := .at ⟨11, by decide⟩

def cancel : Output 1 := .at ⟨0, by decide⟩
def fetchValid : Output 1 := .at ⟨1, by decide⟩
def fetchAddress : Output 32 := .at ⟨2, by decide⟩
def fetchResponseReady : Output 1 := .at ⟨3, by decide⟩
def dataValid : Output 1 := .at ⟨4, by decide⟩
def dataWrite : Output 1 := .at ⟨5, by decide⟩
def dataAddress : Output 32 := .at ⟨6, by decide⟩
def dataSize : Output 2 := .at ⟨7, by decide⟩
def dataSigned : Output 1 := .at ⟨8, by decide⟩
def dataStoreData : Output 32 := .at ⟨9, by decide⟩
def dataResponseReady : Output 1 := .at ⟨10, by decide⟩
def retireValid : Output 1 := .at ⟨11, by decide⟩
def retirePC : Output 32 := .at ⟨12, by decide⟩
def retireInstruction : Output 32 := .at ⟨13, by decide⟩
def retireNextPC : Output 32 := .at ⟨14, by decide⟩
def retireWriteEnable : Output 1 := .at ⟨15, by decide⟩
def retireWriteRd : Output 5 := .at ⟨16, by decide⟩
def retireWriteData : Output 32 := .at ⟨17, by decide⟩
def trapValid : Output 1 := .at ⟨18, by decide⟩
def trapPC : Output 32 := .at ⟨19, by decide⟩
def trapInstructionValid : Output 1 := .at ⟨20, by decide⟩
def trapInstruction : Output 32 := .at ⟨21, by decide⟩
def trapCause : Output 4 := .at ⟨22, by decide⟩
def trapAddress : Output 32 := .at ⟨23, by decide⟩
def terminalValid : Output 1 := .at ⟨24, by decide⟩
def terminalPC : Output 32 := .at ⟨25, by decide⟩
def terminalInstructionValid : Output 1 := .at ⟨26, by decide⟩
def terminalInstruction : Output 32 := .at ⟨27, by decide⟩
def terminalCause : Output 4 := .at ⟨28, by decide⟩
def terminalAddress : Output 32 := .at ⟨29, by decide⟩

def reply (fault : BitVec 2) (data : BitVec 32) : CoreModel.DataReply :=
  if fault = 0 then .success data else .fault (if fault = 1 then .misaligned else .accessFault)

def decode (i : Values Input) : CoreModel.Input :=
  { reset := i reset == 1
    fetchReady := i fetchReady == 1
    fetchResponse := if i fetchResponseValid = 1 then
      some (if i fetchResponseFault = 1 then .accessFault else .instruction (i fetchResponseData)) else none
    dataService := if i dataServiceValid = 1 then
      some (if i dataServiceAtomic = 1 then .atomic (reply (i dataServiceFault) (i dataServiceData)) else .deferred) else none
    dataResponse := if i dataResponseValid = 1 then some (reply (i dataResponseFault) (i dataResponseData)) else none }

def causeCode : CoreModel.Cause → BitVec 4
  | .fetchMisaligned => 0 | .fetchAccessFault => 1
  | .instruction .illegalInstruction => 2 | .instruction .environmentCall => 3 | .instruction .breakpoint => 4
  | .instruction (.instructionAddressMisaligned _) => 5
  | .instruction (.loadFault .misaligned _) => 6 | .instruction (.loadFault .accessFault _) => 7
  | .instruction (.storeFault .misaligned _) => 8 | .instruction (.storeFault .accessFault _) => 9

def faultAddress (fault : CoreModel.Fault) : BitVec 32 :=
  match fault.cause with
  | .fetchMisaligned | .fetchAccessFault => fault.pc
  | .instruction (.instructionAddressMisaligned a) | .instruction (.loadFault _ a)
  | .instruction (.storeFault _ a) => a
  | _ => 0

/-- Register destinations with an architectural write. FENCE operand fields
are retained by instruction decoding but do not designate a writeback. -/
def writeDestination : RV32I.Instruction → RV32I.Register
  | .lui d _ | .auipc d _ | .jal d _ | .jalr d _ _ | .load _ d _ _
  | .aluImm _ d _ _ | .shiftImm _ d _ _ | .aluReg _ d _ _ => d
  | _ => 0

def eventWrite (event : Option CoreModel.Event) : RV32I.Register × BitVec 32 :=
  match event with
  | some (.retired word _ after) =>
      match RV32I.decode word with
      | none => (0,0)
      | some instruction =>
          let dest := writeDestination instruction
          (dest, RV32I.Semantics.read after.registers dest)
  | _ => (0,0)

def retired (event : Option CoreModel.Event) : Bool :=
  match event with | some (.retired _ _ _) => true | _ => false
def trapped (event : Option CoreModel.Event) : Option CoreModel.Fault :=
  match event with | some (.trapped fault _) => some fault | _ => none

def outputValues (i : Values Input) (s : CoreModel.State) : Values Output :=
  let observed := CoreModel.observe (decode i) s
  let event := observed.event
  let wb := eventWrite event
  fun o => match o with
  | .at ⟨0, _⟩ => BitVec.ofBool observed.cancel
  | .at ⟨1, _⟩ => BitVec.ofBool observed.fetch.isSome
  | .at ⟨2, _⟩ => observed.fetch.getD 0
  | .at ⟨3, _⟩ => BitVec.ofBool observed.fetchResponseReady
  | .at ⟨4, _⟩ => BitVec.ofBool observed.data.isSome
  | .at ⟨5, _⟩ => BitVec.ofBool (observed.data matches some (.store _ _ _))
  | .at ⟨6, _⟩ => match observed.data with | some (.load a _ _) | some (.store a _ _) => a | _ => 0
  | .at ⟨7, _⟩ => match observed.data with
      | some (.load _ z _) | some (.store _ z _) => match z with | .byte => 0 | .half => 1 | .word => 2
      | _ => 0
  | .at ⟨8, _⟩ => BitVec.ofBool (observed.data matches some (.load _ _ true))
  | .at ⟨9, _⟩ => match observed.data with | some (.store _ _ v) => v | _ => 0
  | .at ⟨10, _⟩ => BitVec.ofBool observed.dataResponseReady
  | .at ⟨11, _⟩ => BitVec.ofBool (retired event)
  | .at ⟨12, _⟩ => if retired event then s.arch.pc else 0
  | .at ⟨13, _⟩ => match event with | some (.retired w _ _) => w | _ => 0
  | .at ⟨14, _⟩ => match event with | some (.retired _ _ a) => a.pc | _ => 0
  | .at ⟨15, _⟩ => BitVec.ofBool (wb.1 != 0)
  | .at ⟨16, _⟩ => wb.1
  | .at ⟨17, _⟩ => wb.2
  | .at ⟨18, _⟩ => BitVec.ofBool (trapped event).isSome
  | .at ⟨19, _⟩ => ((trapped event).map CoreModel.Fault.pc).getD 0
  | .at ⟨20, _⟩ => BitVec.ofBool ((trapped event).bind CoreModel.Fault.word).isSome
  | .at ⟨21, _⟩ => ((trapped event).bind CoreModel.Fault.word).getD 0
  | .at ⟨22, _⟩ => ((trapped event).map (fun f => causeCode f.cause)).getD 0
  | .at ⟨23, _⟩ => ((trapped event).map faultAddress).getD 0
  | .at ⟨24, _⟩ => BitVec.ofBool observed.terminal.isSome
  | .at ⟨25, _⟩ => (observed.terminal.map CoreModel.Fault.pc).getD 0
  | .at ⟨26, _⟩ => BitVec.ofBool (observed.terminal.bind CoreModel.Fault.word).isSome
  | .at ⟨27, _⟩ => (observed.terminal.bind CoreModel.Fault.word).getD 0
  | .at ⟨28, _⟩ => (observed.terminal.map (fun f => causeCode f.cause)).getD 0
  | .at ⟨29, _⟩ => (observed.terminal.map faultAddress).getD 0
  | .at ⟨k+30, h⟩ => False.elim (by change k+30 < 30 at h; omega)

def spec : Timed.Component (Values Input) CoreModel.State (Values Output) :=
  ⟨fun i s => CoreModel.step (decode i) s, outputValues⟩

end Pinwheel.Hardware.Processor.CoreInterface
