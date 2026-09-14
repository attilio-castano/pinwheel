import Pinwheel.Binary.Image

namespace Pinwheel.Binary
open Engine.Reactive

/-- Count actual V0 bytes. These are serialized-image costs, not physical memory allocation. -/
structure Storage where
  header : Nat
  instructions : Nat
  layout : Nat
  data : Nat
  padding : Nat
  total : Nat
  deriving Repr

def storage : Image → Storage
  | .explicit p =>
    let used := p.memory.toList.take (p.last.val + 1)
    let padding := p.memory.toList.drop (p.last.val + 1)
    ⟨8, (putList putInstruction used).length, 0, 0,
      (putList putInstruction padding).length, (encode (.explicit p)).length⟩
  | .counted p =>
    let layout := p.code.nodes + p.code.loops
    let body := (putCode p.code).length
    ⟨7, body - layout, layout, 2, 0, (encode (.counted p)).length⟩

end Pinwheel.Binary
