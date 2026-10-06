import Pinwheel.Hardware.Storage.PairedStream
import Lean

open Pinwheel.Hardware Pinwheel.Hardware.Storage

/-! The component below exposes the original mailbox's pre-edge inputs and state.
It is combinational: all fourteen outputs are next-state values, with no clock,
hidden state, or changed mailbox equations. The package remains the unchanged
HostResult observer plus the separately proved stream-enabled status overlay. -/
namespace PairedStreamResultComponent

inductive Input : Nat → Type where
  | pinRstN : Input 1 | pinUiIn : Input 8
  | coreBusy : Input 1 | coreMode : Input 3 | coreSamples : Input 16
  | coreStart : Input 1 | coreRejected : Input 1
  | state : HostResult.Register w → Input w

def leaves : {w : Nat} → Observed Chip.Pin Loader.Machine.Output w → Expr Input NoRegister w
  | _, .input .rstN => .input .pinRstN
  | _, .input .uiIn => .input .pinUiIn
  | _, .output (.core .busy) => .input .coreBusy
  | _, .output (.core (.state .mode)) => .input .coreMode
  | _, .output (.core (.state (.sample k))) =>
      .slice k.val 1 (by omega) (.input .coreSamples)
  | _, .output (.control .start) => .input .coreStart
  | _, .output (.control .rejected) => .input .coreRejected
  | _, _ => .lit 0

def circuit : Circuit Input NoRegister HostResult.Register where
  next := fun r => nomatch r
  output := fun r => (HostResult.observer.next r).bind leaves (fun r => .input (.state r))

def observed (input : Values Input) : Values (Observed Chip.Pin Loader.Machine.Output) :=
  fun p => (leaves p).eval input NoRegister.values
def snapshot (input : Values Input) : Values HostResult.Register := fun r => input (.state r)

/-- Every exposed next-state output is exactly the unchanged observer expression
on the supplied pre-edge snapshot. `HostResult.next_correct` identifies that
observer with its functional mailbox model. -/
theorem next_correct (input : Values Input) (r : HostResult.Register w) :
    circuit.observe input NoRegister.values r =
      (HostResult.observer.next r).eval (observed input) (snapshot input) := by
  simp only [circuit, Circuit.observe, Expr.eval_bind, Expr.eval]
  rfl
  done

def inputs : Array (Sigma Input) :=
  #[⟨1,.pinRstN⟩,⟨8,.pinUiIn⟩,⟨1,.coreBusy⟩,⟨3,.coreMode⟩,
    ⟨16,.coreSamples⟩,⟨1,.coreStart⟩,⟨1,.coreRejected⟩] ++
    HostResult.registers.map (fun ⟨w,r⟩ => ⟨w,.state r⟩)
def inputLabel : {w : Nat} → Input w → String
  | _, .pinRstN => "pin_rst_n" | _, .pinUiIn => "pin_ui_in"
  | _, .coreBusy => "core_busy" | _, .coreMode => "core_mode"
  | _, .coreSamples => "core_samples" | _, .coreStart => "core_start"
  | _, .coreRejected => "core_rejected"
  | _, .state r => "state_" ++ HostResult.label r
def outputLabel : {w : Nat} → HostResult.Register w → String :=
  fun r => "next_" ++ HostResult.label r
def text : Except String String := Emit.moduleText "uart_stream_result_component"
  circuit inputs #[] HostResult.registers inputLabel (fun r => nomatch r) outputLabel

end PairedStreamResultComponent

open Lean Elab Command in
elab "#audit_paired_stream" : command => do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    if name.toString.startsWith "Pinwheel.Hardware.Storage.PairedStream." ||
        name.toString.startsWith "PairedStreamResultComponent." then
      count := count + 1
      let axioms ← collectAxioms name
      let unexpected := axioms.filter fun ax =>
        ax != ``propext && ax != ``Classical.choice && ax != ``Quot.sound
      unless unexpected.isEmpty do
        throwError "Unapproved paired-stream axioms: {unexpected}"
  logInfo m!"Paired stream: {count} declarations; standard axioms only."

#audit_paired_stream

private def portJson (ps : Array (Sigma P)) (label : {w : Nat} → P w → String) : Lean.Json :=
  Lean.toJson (ps.map fun ⟨w,p⟩ => Lean.Json.mkObj
    [("name",Lean.toJson (label p)),("width",Lean.toJson w)])
private def registersJson (rs : Array (Sigma R)) (label : {w : Nat} → R w → String) : Lean.Json :=
  Lean.toJson (rs.map fun ⟨w,r⟩ => Lean.Json.mkObj
    [("name",Lean.toJson ("r_" ++ label r)),("reference",Lean.toJson ("r_" ++ label r)),
     ("width",Lean.toJson w)])

def main (args : List String) : IO Unit := do
  let out := args.headD "build/storage/paired-stream"
  IO.FS.createDirAll out
  for (name,text) in [("core",PairedStream.coreText),("chip",PairedStream.chipText),
      ("host-result-component",PairedStreamResultComponent.text)] do
    match text with
    | .error e => throw (IO.userError e)
    | .ok s => IO.FS.writeFile (out ++ "/" ++ name ++ ".mlir") s
  let core := Lean.Json.mkObj [
    ("inputs",portJson (PairedController.inputs Loader.Machine.inputs)
      (SramAssembly.inputLabel Loader.Machine.inputLabel)),
    ("outputs",portJson (PairedController.outputs Loader.Machine.outputs)
      (SramAssembly.outputLabel Loader.Machine.outputLabel)),
    ("registers",registersJson PairedStream.registers PairedStream.label)]
  let chip := Lean.Json.mkObj [
    ("inputs",portJson (PairedController.inputs Backend.Policy.chipInputs)
      (SramAssembly.inputLabel Backend.Policy.chipInputLabel)),
    ("outputs",portJson (PairedController.outputs Backend.Policy.chipOutputs)
      (SramAssembly.outputLabel Backend.Policy.chipOutputLabel)),
    ("registers",registersJson PairedStream.fullRegisters PairedStream.fullLabel)]
  let component := Lean.Json.mkObj [
    ("module",Lean.toJson "uart_stream_result_component"),
    ("inputs",portJson PairedStreamResultComponent.inputs PairedStreamResultComponent.inputLabel),
    ("outputs",portJson HostResult.registers PairedStreamResultComponent.outputLabel),
    ("registers",Lean.toJson (#[] : Array Lean.Json)),
    ("alignment",Lean.toJson "pre-edge snapshot to next state; package completion arrives one edge later")]
  IO.FS.writeFile (out ++ "/assembly.json") ((Lean.Json.mkObj
    [("schema",Lean.toJson (1 : Nat)),("core",core),("chip",chip),
     ("host_result_component",component)]).pretty ++ "\n")
