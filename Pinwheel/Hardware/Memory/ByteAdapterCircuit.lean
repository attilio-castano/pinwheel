import Pinwheel.Hardware.Memory.ByteAdapterInterface
import Pinwheel.Hardware.Memory.CommandFlops

/-! One word RAM with its existing Q, six retained request metadata fields,
and one pending bit. Only request acceptance enables the metadata registers.
Reset cancels pending work and performs no RAM command or metadata clearing.
-/
namespace Pinwheel.Hardware.Memory.ByteAdapterCircuit
open ByteAdapterInterface

abbrev metadataPorts (a : Nat) : Hardware.Stream.Ports where
  size := 7
  widths := fun k => if k.val = 2 ∨ k.val = 4 then 2 else if k.val = 3 then a else if k.val = 5 then 32 else 1
  names := fun k => #["write", "signed", "size", "address", "offset", "data", "pending"][k]
  distinct := by decide +kernel

abbrev Metadata (a : Nat) := (metadataPorts a).Signal
abbrev Register (a : Nat) := Hardware.Stream.Joint (CommandFlops.Register a 32) (Metadata a)

def metaWrite : Metadata a 1 := .at ⟨0, by simp⟩
def metaSigned : Metadata a 1 := .at ⟨1, by simp⟩
def metaSize : Metadata a 2 := .at ⟨2, by simp⟩
def metaAddress : Metadata a a := .at ⟨3, by simp⟩
def metaOffset : Metadata a 2 := .at ⟨4, by simp⟩
def metaData : Metadata a 32 := .at ⟨5, by simp⟩
def metaPending : Metadata a 1 := .at ⟨6, by simp⟩
def pending : Register a 1 := .right metaPending

def registers (a : Nat) : Interface (Register a) :=
  Hardware.Stream.Joint.interface (CommandFlops.registers a 32) (metadataPorts a).interface

theorem register_count (a : Nat) : (registers a).size = 2^a + 8 := by rfl

def memoryValues (s : Values (Register a)) : Values (CommandFlops.Register a 32) := fun r => s (.left r)
def storedRequest (s : Values (Register a)) : ByteAdapterModel.Request a :=
  request (s (.right metaWrite)) (s (.right metaSigned)) (s (.right metaSize))
    (s (.right metaAddress)) (s (.right metaOffset)) (s (.right metaData))

def view (s : Values (Register a)) : ByteAdapterModel.State a :=
  ⟨CommandFlops.view (memoryValues s), if s pending = 1 then some (storedRequest s) else none⟩

def select4 (offset : Expr I R 2) (x0 x1 x2 x3 : Expr I R w) : Expr I R w :=
  .mux (.equal offset (.lit 0)) x0 (.mux (.equal offset (.lit 1)) x1 (.mux (.equal offset (.lit 2)) x2 x3))

def legal (size offset : Expr I R 2) : Expr I R 1 :=
  (Expr.equal size (.lit 0)).bor
    ((Expr.band (.equal size (.lit 1)) ((Expr.equal offset (.lit 0)).bor (.equal offset (.lit 2)))).bor
      (.band (.equal size (.lit 2)) (.equal offset (.lit 0))))

def selectedByte (offset : Expr I R 2) (word : Expr I R 32) : Expr I R 8 :=
  select4 offset (.slice 0 8 (by decide) word) (.slice 8 8 (by decide) word)
    (.slice 16 8 (by decide) word) (.slice 24 8 (by decide) word)

def loadExpr (size offset : Expr I R 2) (signed : Expr I R 1) (word : Expr I R 32) : Expr I R 32 :=
  let b := selectedByte offset word
  let h := Expr.mux (.equal offset (.lit 0)) (.slice 0 16 (by decide) word) (.slice 16 16 (by decide) word)
  let bHigh := Expr.mux (.band signed (.slice 7 1 (by decide) b)) (.lit (-1 : BitVec 24)) (.lit 0)
  let hHigh := Expr.mux (.band signed (.slice 15 1 (by decide) h)) (.lit (-1 : BitVec 16)) (.lit 0)
  .mux (.equal size (.lit 0)) (.concat bHigh b)
    (.mux (.equal size (.lit 1)) (.concat hHigh h) word)

def storeExpr (size offset : Expr I R 2) (word data : Expr I R 32) : Expr I R 32 :=
  let b := Expr.slice 0 8 (by decide) data
  let h := Expr.slice 0 16 (by decide) data
  let b0 : Expr I R 32 := .concat (.slice 8 24 (by decide) word) b
  let b1 : Expr I R 32 := .concat (.slice 16 16 (by decide) word) (.concat b (.slice 0 8 (by decide) word))
  let b2 : Expr I R 32 := .concat (.slice 24 8 (by decide) word) (.concat b (.slice 0 16 (by decide) word))
  let b3 : Expr I R 32 := .concat b (.slice 0 24 (by decide) word)
  let bytes := select4 offset b0 b1 b2 b3
  let halves := Expr.mux (.equal offset (.lit 0)) (.concat (.slice 16 16 (by decide) word) h)
    (.concat h (.slice 0 16 (by decide) word))
  .mux (.equal size (.lit 0)) bytes (.mux (.equal size (.lit 1)) halves data)

def requestReadyExpr : Expr (Input a) (Register a) 1 := .band (.inv (.input reset)) (.inv (.reg pending))
def accept : Expr (Input a) (Register a) 1 := .band requestReadyExpr (.input requestValid)
def responseValidExpr : Expr (Input a) (Register a) 1 := .band (.inv (.input reset)) (.reg pending)
def storedLegal : Expr (Input a) (Register a) 1 := legal (.reg (.right metaSize)) (.reg (.right metaOffset))
def commit : Expr (Input a) (Register a) 1 :=
  .band responseValidExpr (.band (.input responseReady) (.band (.reg (.right metaWrite)) storedLegal))
def sample : Expr (Input a) (Register a) 1 := .band accept (legal (.input size) (.input offset))

def memoryInput : {b : Nat} → CommandInterface.Input a 32 b → Expr (Input a) (Register a) b
  | _, .enable => sample.bor commit
  | _, .write => .reg pending
  | _, .address => .mux (.reg pending) (.reg (.right metaAddress)) (.input address)
  | _, .data => storeExpr (.reg (.right metaSize)) (.reg (.right metaOffset))
      (.reg (.left CommandFlops.q)) (.reg (.right metaData))

def memoryPins (i : Values (Input a)) (s : Values (Register a)) : Values (CommandInterface.Input a 32) :=
  fun p => (memoryInput p).eval i s

def metadataInput : {b : Nat} → Metadata a b → Expr (Input a) (Register a) b
  | _, .at ⟨0, _⟩ => .input write
  | _, .at ⟨1, _⟩ => .input signed
  | _, .at ⟨2, _⟩ => .input size
  | _, .at ⟨3, _⟩ => .input address
  | _, .at ⟨4, _⟩ => .input offset
  | _, .at ⟨5, _⟩ => .input data
  | _, .at ⟨6, _⟩ => .lit 0
  | _, .at ⟨k+7, h⟩ => False.elim (by change k+7 < 7 at h; omega)

def codeExpr : Expr (Input a) (Register a) 2 :=
  .mux (.equal (.reg (.right metaSize)) (.lit 3)) (.lit 2)
    (.mux storedLegal (.mux (.reg (.right metaWrite)) (.lit 1) (.lit 0)) (.lit 3))

def metadataNext : {b : Nat} → Metadata a b → Expr (Input a) (Register a) b
  | _, .at ⟨0, _⟩ => .mux accept (.input write) (.reg (.right metaWrite))
  | _, .at ⟨1, _⟩ => .mux accept (.input signed) (.reg (.right metaSigned))
  | _, .at ⟨2, _⟩ => .mux accept (.input size) (.reg (.right metaSize))
  | _, .at ⟨3, _⟩ => .mux accept (.input address) (.reg (.right metaAddress))
  | _, .at ⟨4, _⟩ => .mux accept (.input offset) (.reg (.right metaOffset))
  | _, .at ⟨5, _⟩ => .mux accept (.input data) (.reg (.right metaData))
  | _, .at ⟨6, _⟩ => .band (.inv (.input reset))
      (.mux (.reg pending) (.inv (.input responseReady)) (.input requestValid))
  | _, .at ⟨k+7, h⟩ => False.elim (by change k+7 < 7 at h; omega)

def circuit (a : Nat) : Circuit (Input a) (Register a) Output where
  next := fun {b} r => match b, r with
    | _, .left r => ((CommandFlops.circuit a 32).next r).bind memoryInput (fun r => .reg (.left r))
    | _, .right r => metadataNext r
  output := fun {b} o => match o with
    | .at ⟨0, _⟩ => requestReadyExpr
    | .at ⟨1, _⟩ => responseValidExpr
    | .at ⟨2, _⟩ => .mux responseValidExpr codeExpr (.lit 0)
    | .at ⟨3, _⟩ => .mux (.band responseValidExpr (.band storedLegal (.inv (.reg (.right metaWrite)))))
        (loadExpr (.reg (.right metaSize)) (.reg (.right metaOffset)) (.reg (.right metaSigned))
          (.reg (.left CommandFlops.q))) (.lit 0)
    | .at ⟨k+4, h⟩ => False.elim (by change k+4 < 4 at h; omega)

end Pinwheel.Hardware.Memory.ByteAdapterCircuit
