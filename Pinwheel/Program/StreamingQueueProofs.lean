import Pinwheel.Program.StreamingQueue

namespace Pinwheel.Program.Streaming

theorem Queue.no_empty_bypass (q : Queue addrBits) (empty : q.count.val = 0)
    (_incoming : Option Chunk) : q.willPop true = false := by
  simp [willPop, readable, empty]

theorem Queue.no_full_bypass (q : Queue addrBits)
    (full : q.count.val = queueDepth addrBits) (incoming : Option Chunk) :
    q.willPush incoming = false := by
  simp [willPush, writable, full]

theorem Queue.tick_count (q : Queue addrBits) (incoming : Option Chunk) (outgoing : Bool) :
    (q.tick incoming outgoing).count.val = q.count.val +
      (if q.willPush incoming then 1 else 0) - (if q.willPop outgoing then 1 else 0) := rfl

theorem Queue.tick_count_le (q : Queue addrBits) (incoming : Option Chunk) (outgoing : Bool) :
    (q.tick incoming outgoing).count.val ≤ queueDepth addrBits := by
  exact Nat.le_of_lt_succ (q.tick incoming outgoing).count.isLt

theorem Queue.tick_rejected_push (q : Queue addrBits) (incoming : Option Chunk)
    (outgoing : Bool) (rejected : q.willPush incoming = false) :
    (q.tick incoming outgoing).memory = q.memory := by
  simp [tick, rejected]

theorem Queue.tick_empty_pop (q : Queue addrBits) (incoming : Option Chunk)
    (empty : q.count.val = 0) :
    (q.tick incoming true).head = q.head := by
  simp [tick, willPop, readable, empty]

theorem Queue.tick_full_push (q : Queue addrBits) (incoming : Option Chunk)
    (outgoing : Bool) (full : q.count.val = queueDepth addrBits) :
    (q.tick incoming outgoing).tail = q.tail := by
  simp [tick, willPush, writable, full]

/-- A ring has at most one wrap when both offsets are within its depth. -/
theorem ring_mod (head offset depth : Nat) (headBound : head < depth)
    (offsetBound : offset < depth) :
    (head + offset) % depth =
      if head + offset < depth then head + offset else head + offset - depth := by
  by_cases within : head + offset < depth
  · simp [within, Nat.mod_eq_of_lt within]
  · rw [if_neg within, Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]

theorem ring_injective (head left right depth : Nat) (headBound : head < depth)
    (leftBound : left < depth) (rightBound : right < depth)
    (same : (head + left) % depth = (head + right) % depth) : left = right := by
  rw [ring_mod head left depth headBound leftBound,
    ring_mod head right depth headBound rightBound] at same
  split at same <;> split at same <;> omega

/-- The list is a proof ghost, not operational storage. -/
structure Queue.Contents (q : Queue addrBits) (chunks : List Chunk) : Prop where
  length : chunks.length = q.count.val
  tail : q.tail.val = (q.head.val + q.count.val) % queueDepth addrBits
  lookup : ∀ k (within : k < chunks.length),
    q.memory[(q.head.val + k) % queueDepth addrBits]'(Nat.mod_lt _ (queueDepth_positive _)) =
      chunks[k]

theorem Queue.empty_contents (addrBits : Nat) : (Queue.empty addrBits).Contents [] := by
  constructor
  · rfl
  · simp [empty]
  · simp

theorem Queue.Contents.push (q : Queue addrBits) (chunks : List Chunk) (chunk : Chunk)
    (contents : q.Contents chunks) (room : q.count.val < queueDepth addrBits) :
    (q.tick (some chunk) false).Contents (chunks ++ [chunk]) := by
  constructor
  case length => simp [tick, willPush, writable, room, willPop, contents.length]
  case tail => simp [tick, willPush, writable, room, willPop, nextIndex, contents.tail, Nat.add_assoc]
  case lookup =>
    intro k within
    simp only [tick, willPush, Option.isSome_some, writable, room, decide_true,
      Bool.and_self, ↓reduceIte, willPop, Bool.false_and, Bool.false_eq_true,
      Option.getD_some]
    by_cases old : k < chunks.length
    · have distinct : q.tail.val ≠ (q.head.val + k) % queueDepth addrBits := by
        intro same
        have equal := ring_injective q.head.val q.count.val k (queueDepth addrBits)
          q.head.isLt room (by have := contents.length; omega) (contents.tail.symm.trans same)
        exact (Nat.ne_of_lt (contents.length ▸ old)) equal.symm
      simpa [Vector.getElem_set, distinct, List.getElem_append_left, old] using contents.lookup k old
    · have last : k = chunks.length := by simpa using Nat.eq_of_lt_succ_of_not_lt (by simpa using within) old
      simp [last, contents.length, ← contents.tail]

theorem Queue.Contents.pop (q : Queue addrBits) (chunks : List Chunk)
    (contents : q.Contents chunks) (nonempty : 0 < q.count.val) :
    (q.tick none true).Contents (chunks.drop 1) := by
  constructor
  case length => simp [tick, willPush, willPop, readable, Nat.ne_of_gt nonempty, contents.length]
  case tail =>
    simp [tick, willPush, willPop, readable, Nat.ne_of_gt nonempty, nextIndex, contents.tail]
    congr 1 <;> omega
  case lookup =>
    intro k within
    simpa [tick, willPush, willPop, readable, Nat.ne_of_gt nonempty, nextIndex,
      Nat.add_assoc, Nat.add_comm 1 k] using
      contents.lookup (k + 1) (by simp only [List.length_drop] at within; omega)

theorem Queue.tick_both (q : Queue addrBits) (chunk : Chunk)
    (room : q.count.val < queueDepth addrBits) (nonempty : 0 < q.count.val) :
    q.tick (some chunk) true = (q.tick none true).tick (some chunk) false := by
  have afterRoom : q.count.val - 1 < queueDepth addrBits :=
    Nat.lt_of_le_of_lt (Nat.sub_le _ _) room
  simp [tick, willPush, willPop, writable, readable, room, afterRoom, Nat.ne_of_gt nonempty,
    Nat.sub_add_cancel nonempty]

theorem Queue.Contents.exchange (q : Queue addrBits) (chunks : List Chunk) (chunk : Chunk)
    (contents : q.Contents chunks) (room : q.count.val < queueDepth addrBits)
    (nonempty : 0 < q.count.val) :
    (q.tick (some chunk) true).Contents (chunks.drop 1 ++ [chunk]) := by
  rw [tick_both q chunk room nonempty]
  apply Queue.Contents.push _ _ _ (contents.pop q chunks nonempty)
  simpa [tick_count, willPush, willPop, readable, Nat.ne_of_gt nonempty] using
    Nat.lt_of_le_of_lt (Nat.sub_le q.count.val 1) room

theorem Queue.Contents.peek (q : Queue addrBits) (chunks : List Chunk)
    (contents : q.Contents chunks) (nonempty : 0 < chunks.length) :
    q.peek = chunks[0] := by
  simpa [Queue.peek, Nat.mod_eq_of_lt q.head.isLt] using contents.lookup 0 nonempty

end Pinwheel.Program.Streaming
