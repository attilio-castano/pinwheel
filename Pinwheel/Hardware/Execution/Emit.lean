import Pinwheel.Hardware.Execution.StoreProofs
import Pinwheel.Hardware.Emit

namespace Pinwheel.Hardware.Execution

def ports : Array (Sigma Port) :=
  #[⟨1, .valid⟩, ⟨3, .kind⟩, ⟨3, .levels⟩, ⟨3, .enabled⟩, ⟨8, .duration⟩, ⟨8, .budget⟩,
    ⟨4, .check⟩, ⟨6, .entry⟩, ⟨6, .terminal⟩, ⟨2, .finish⟩, ⟨4, .sample⟩, ⟨8, .yes⟩, ⟨8, .no⟩]

def portLabel : {w : Nat} → Port w → String
  | _, .valid => "valid" | _, .kind => "kind" | _, .levels => "levels" | _, .enabled => "enabled"
  | _, .duration => "duration" | _, .budget => "budget" | _, .check => "check"
  | _, .entry => "entry" | _, .terminal => "terminal" | _, .finish => "finish"
  | _, .sample => "sample" | _, .yes => "yes" | _, .no => "no"

def inputs : Array (Sigma Input) :=
  #[⟨1, .write⟩, ⟨1, .busy⟩, ⟨1, .indexBank⟩, ⟨8, .address⟩, ⟨64, .data⟩, ⟨8, .readA⟩, ⟨8, .readB⟩]

def inputLabel : {w : Nat} → Input w → String
  | _, .write => "write" | _, .busy => "busy" | _, .indexBank => "index_bank"
  | _, .address => "address" | _, .data => "data" | _, .readA => "read_a" | _, .readB => "read_b"

def outputs : Array (Sigma Output) :=
  ports.map (fun ⟨w, p⟩ => ⟨w, .a p⟩) ++ ports.map (fun ⟨w, p⟩ => ⟨w, .b p⟩)

def outputLabel : {w : Nat} → Output w → String
  | _, .a p => "a_" ++ portLabel p | _, .b p => "b_" ++ portLabel p

def directRegisters : Array (Sigma DirectReg) := Array.ofFn (fun k : Fin 256 => ⟨64, .word (BitVec.ofFin k)⟩)
def indexedRegisters : Array (Sigma IndexedReg) :=
  Array.ofFn (fun k : Fin 64 => ⟨64, .word (BitVec.ofFin k)⟩) ++
    Array.ofFn (fun k : Fin 256 => ⟨6, .index (BitVec.ofFin k)⟩)

def directRegisterLabel : {w : Nat} → DirectReg w → String
  | _, .word k => s!"word{k.toNat}"
def indexedRegisterLabel : {w : Nat} → IndexedReg w → String
  | _, .word k => s!"word{k.toNat}" | _, .index k => s!"index{k.toNat}"

def directModule : Except String String :=
  Emit.moduleText "pinwheel_e64_direct" directCircuit inputs directRegisters outputs
    inputLabel directRegisterLabel outputLabel

def indexedModule : Except String String :=
  Emit.moduleText "pinwheel_e64_indexed" indexedCircuit inputs indexedRegisters outputs
    inputLabel indexedRegisterLabel outputLabel

inductive WordInput : Nat → Type where | word : WordInput 64

def decoderCircuit : Circuit WordInput Emit.NoRegister Port where
  next := fun r => nomatch r
  output := logic (.input .word)

def decoderModule : Except String String :=
  Emit.moduleText "pinwheel_e64_decoder" decoderCircuit #[⟨64, .word⟩] #[] ports
    (fun _ => "word") (fun r => nomatch r) portLabel

end Pinwheel.Hardware.Execution
