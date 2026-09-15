import Pinwheel.Hardware.Loader.Emit

namespace Pinwheel.Hardware.Storage

structure Indexed32 where
  dictionary : Vector (BitVec 64) 32
  addresses : Vector (BitVec 5) 256
  deriving DecidableEq, Repr

def Indexed32.expand (image : Indexed32) : Execution.Words :=
  Vector.ofFn fun pc => image.dictionary[image.addresses[pc.val].toNat]

/-- Capacity is checked before conversion; every accepted image carries full lookup equality. -/
def lower32 (words : Execution.Words) : Option {m : Indexed32 // m.expand = words} := do
  let unique := words.toList.eraseDups
  if unique.length > 32 then none else do
    let m : Indexed32 := {
      dictionary := Vector.ofFn fun k => unique[k.val]?.getD 4
      addresses := words.map fun word => BitVec.ofNat 5 (unique.idxOf word) }
    if h : m.expand = words then some ⟨m, h⟩ else none

theorem lower32_rejects (words : Execution.Words) (h : words.toList.eraseDups.length > 32) :
    lower32 words = none := by
  simp [lower32, h]
  done

def Indexed32.store (m : Indexed32) (p : Reactive.Program) : Engine.Reactive.Fetch.Store 255 15 :=
  ⟨fun pc => Execution.decode m.expand[pc.val], p.idle, p.last⟩

theorem indexed32_agrees (p : Reactive.Program) (m : Indexed32)
    (h : m.expand = Execution.imageWords p) : Engine.Reactive.Fetch.Agrees (m.store p) p := by
  constructor <;> simp [Indexed32.store, h, Execution.imageWords, Engine.Reactive.Program.fetch, Execution.decode_encode]
  done

end Pinwheel.Hardware.Storage
