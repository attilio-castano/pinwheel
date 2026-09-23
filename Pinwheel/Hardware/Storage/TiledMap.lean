import Pinwheel.Hardware.Storage.MapTile
import Lean.Data.Json

/-! Shared map interface and selection glue, used by both the controlled map
comparison and the experimental whole-chip composition. The flat circuit remains
the independent structural reference; MapTile owns the local memory proof. -/
open Pinwheel.Hardware Pinwheel.Hardware.Storage

namespace Pinwheel.Hardware.Storage.TiledMap

inductive Input : Nat → Type where
  | write : Input 1 | writeBank : Input 1 | cursor : Input 9 | data : Input 5
  | readBank : Input 1 | pc (port : Fin 2) : Input 8

inductive Register : Nat → Type where
  | index (bank : Bool) (word : BitVec 8) : Register 5

def inputs : Array (Sigma Input) :=
  #[⟨1, .write⟩, ⟨1, .writeBank⟩, ⟨9, .cursor⟩, ⟨5, .data⟩, ⟨1, .readBank⟩,
    ⟨8, .pc 0⟩, ⟨8, .pc 1⟩]

def inputLabel : {w : Nat} → Input w → String
  | _, .write => "write_enable" | _, .writeBank => "write_bank" | _, .cursor => "cursor"
  | _, .data => "write_data" | _, .readBank => "read_bank" | _, .pc p => s!"pc{p.val}"

def outputLabel : {w : Nat} → MapTile.Output w → String
  | _, .data p => s!"index{p.val}"

def outputs : Array (Sigma MapTile.Output) := #[⟨5, .data 0⟩, ⟨5, .data 1⟩]

def flat : Circuit Input Register MapTile.Output where
  next := fun r => match r with
    | .index b k => .mux
        (.band (.band (.input .write) (.equal (.input .writeBank) (.lit (BitVec.ofBool b))))
          (.equal (.input .cursor) (.lit (Loader.Store.offset (.index k)))))
        (.input .data) (.reg (.index b k))
  output := fun o => match o with
    | .data p => .mux (.input .readBank)
        (Execution.readTree 8 (fun k => .reg (.index true k)) (.input (.pc p)))
        (Execution.readTree 8 (fun k => .reg (.index false k)) (.input (.pc p)))

def registers : Array (Sigma Register) :=
  (#[false, true]).flatMap fun bank =>
    Array.ofFn fun k : Fin 256 => ⟨5, .index bank (BitVec.ofFin k)⟩

def registerLabel : {w : Nat} → Register w → String
  | _, .index b k => s!"bank{if b then 1 else 0}_word{k.toNat}"

inductive GlueInput : Nat → Type where
  | base : Input w → GlueInput w
  | result (bank : Bool) (low : BitVec 4) (port : Fin 2) : GlueInput 5

inductive NoRegister : Nat → Type

inductive GlueOutput : Nat → Type where
  | index : MapTile.Output w → GlueOutput w
  | readHi (port : Fin 2) : GlueOutput 4
  | writeHi : GlueOutput 4
  | enable (bank : Bool) (low : BitVec 4) : GlueOutput 1

def glue : Circuit GlueInput NoRegister GlueOutput where
  next := fun r => nomatch r
  output := fun o => match o with
    | .index (.data p) => .mux (.input (.base .readBank))
        (Execution.readTree 4 (fun k => .input (.result true k p))
          (.slice 0 4 (by decide) (.input (.base (.pc p)))))
        (Execution.readTree 4 (fun k => .input (.result false k p))
          (.slice 0 4 (by decide) (.input (.base (.pc p)))))
    | .readHi p => .slice 4 4 (by decide) (.input (.base (.pc p)))
    | .writeHi => .slice 4 4 (by decide) (.sub (.input (.base .cursor)) (.lit 64))
    | .enable b low =>
        .band (.band (.input (.base .write))
          (.equal (.input (.base .writeBank)) (.lit (BitVec.ofBool b))))
          (.band (.band (.inv (.ult (.input (.base .cursor)) (.lit 64)))
            (.ult (.input (.base .cursor)) (.lit 320)))
            (.equal (.slice 0 4 (by decide) (.input (.base .cursor))) (.lit low)))

def lows : Array (BitVec 4) := Array.ofFn fun k : Fin 16 => BitVec.ofFin k

def glueInputs : Array (Sigma GlueInput) :=
  inputs.map (fun ⟨w, p⟩ => ⟨w, .base p⟩) ++
    (#[false, true]).flatMap (fun b => lows.flatMap fun k =>
      #[⟨5, .result b k 0⟩, ⟨5, .result b k 1⟩])

def glueOutputs : Array (Sigma GlueOutput) :=
  outputs.map (fun ⟨w, p⟩ => ⟨w, .index p⟩) ++
    #[⟨4, .readHi 0⟩, ⟨4, .readHi 1⟩, ⟨4, .writeHi⟩] ++
    (#[false, true]).flatMap (fun b => lows.map fun k => ⟨1, .enable b k⟩)

def tileName (bank : Bool) (low : BitVec 4) : String :=
  s!"tile_b{if bank then 1 else 0}_l{low.toNat}"

def glueInputLabel : {w : Nat} → GlueInput w → String
  | _, .base p => inputLabel p
  | _, .result b k p => tileName b k ++ s!"_index{p.val}"

def glueOutputLabel : {w : Nat} → GlueOutput w → String
  | _, .index p => outputLabel p | _, .readHi p => s!"read_hi{p.val}"
  | _, .writeHi => "write_hi" | _, .enable b k => tileName b k ++ "_enable"

def tileInputs : Array (Sigma MapTile.Input) :=
  #[⟨1, .enable⟩, ⟨4, .address⟩, ⟨5, .data⟩, ⟨4, .read 0⟩, ⟨4, .read 1⟩]

def tileInputLabel : {w : Nat} → MapTile.Input w → String
  | _, .enable => "write_enable" | _, .address => "write_hi" | _, .data => "write_data"
  | _, .read p => s!"read_hi{p.val}"

def tileRegisters : Array (Sigma MapTile.Register) :=
  Array.ofFn fun k : Fin 16 => ⟨5, .word (BitVec.ofFin k)⟩

def tileRegisterLabel : {w : Nat} → MapTile.Register w → String
  | _, .word k => s!"word{k.toNat}"

def portsJson (ports : Array (Sigma P)) (label : {w : Nat} → P w → String) : Lean.Json :=
  Lean.toJson (ports.map fun ⟨w, p⟩ => Lean.Json.mkObj [("name", Lean.toJson (label p)),
    ("width", Lean.toJson w)])

end Pinwheel.Hardware.Storage.TiledMap
