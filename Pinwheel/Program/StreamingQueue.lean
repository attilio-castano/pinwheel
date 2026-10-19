import Pinwheel.Engine.Reactive

/-! Fixed-storage word queues for the opt-in streaming engine. -/
namespace Pinwheel.Program.Streaming

/-- TX uses the most significant `validBits` bits; RX uses the least significant ones. -/
structure Chunk where
  data : BitVec 32 := 0
  validMinusOne : Fin 32 := 31
  deriving DecidableEq, Repr

def Chunk.validBits (c : Chunk) : Nat := c.validMinusOne.val + 1

theorem Chunk.validBits_positive (c : Chunk) : 0 < c.validBits := by
  simp [validBits]

theorem Chunk.validBits_le (c : Chunk) : c.validBits ≤ 32 := by
  have := c.validMinusOne.isLt
  unfold validBits
  omega

def queueDepth (addrBits : Nat) : Nat := 2 ^ addrBits

theorem queueDepth_positive (addrBits : Nat) : 0 < queueDepth addrBits := by
  exact Nat.two_pow_pos addrBits

/-- Storage is a fixed vector, including when the queue is empty. -/
structure Queue (addrBits : Nat) where
  memory : Vector Chunk (queueDepth addrBits)
  head : Fin (queueDepth addrBits)
  tail : Fin (queueDepth addrBits)
  count : Fin (queueDepth addrBits + 1)
  deriving DecidableEq, Repr

def Queue.empty (addrBits : Nat) : Queue addrBits :=
  ⟨Vector.replicate (queueDepth addrBits) {},
    ⟨0, queueDepth_positive addrBits⟩, ⟨0, queueDepth_positive addrBits⟩, 0⟩

def Queue.readable (q : Queue addrBits) : Bool := q.count.val != 0
def Queue.writable (q : Queue addrBits) : Bool := q.count.val < queueDepth addrBits

def Queue.peek (q : Queue addrBits) : Chunk := q.memory[q.head.val]

def Queue.willPush (q : Queue addrBits) (incoming : Option Chunk) : Bool :=
  incoming.isSome && q.writable

def Queue.willPop (q : Queue addrBits) (outgoing : Bool) : Bool :=
  outgoing && q.readable

def Queue.nextIndex (i : Fin (queueDepth addrBits)) : Fin (queueDepth addrBits) :=
  ⟨(i.val + 1) % queueDepth addrBits, Nat.mod_lt _ (queueDepth_positive _)⟩

private theorem count_step_bound (n depth : Nat) (bound : n < depth + 1)
    (put take : Bool) (putBound : put = true → n < depth) :
    n + (if put then 1 else 0) - (if take then 1 else 0) < depth + 1 := by
  cases put <;> cases take <;> simp_all <;> omega

/-- Both permissions inspect the pre-edge queue: there is no boundary bypass. -/
def Queue.tick (q : Queue addrBits) (incoming : Option Chunk) (outgoing : Bool) : Queue addrBits :=
  let put := q.willPush incoming
  let take := q.willPop outgoing
  { memory := if put then q.memory.set q.tail.val (incoming.getD {}) else q.memory
    head := if take then nextIndex q.head else q.head
    tail := if put then nextIndex q.tail else q.tail
    count := ⟨q.count.val + (if put then 1 else 0) - (if take then 1 else 0), by
      have putBound : put = true → q.count.val < queueDepth addrBits := by
        simp [put, willPush, writable]
      exact count_step_bound _ _ q.count.isLt put take putBound⟩ }

end Pinwheel.Program.Streaming
