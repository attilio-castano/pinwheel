import Pinwheel.Program.StreamingQueueProofs
import Pinwheel.Program.StreamingPacking

/-! FIFO order and bit accounting use ghost lists; hardware storage stays fixed. -/
namespace Pinwheel.Program.Streaming

def Queue.traceTick (q : Queue addrBits) (chunks : List Chunk)
    (incoming : Option Chunk) (outgoing : Bool) : List Chunk :=
  let kept := if q.willPop outgoing then chunks.drop 1 else chunks
  if q.willPush incoming then kept ++ [incoming.getD {}] else kept

theorem Queue.tick_no_effect (q : Queue addrBits) (incoming : Option Chunk) (outgoing : Bool)
    (noPush : q.willPush incoming = false) (noPop : q.willPop outgoing = false) :
    q.tick incoming outgoing = q := by
  simp [tick, noPush, noPop]

theorem Queue.tick_push_only (q : Queue addrBits) (incoming : Option Chunk) (outgoing : Bool)
    (push : q.willPush incoming = true) (noPop : q.willPop outgoing = false) :
    q.tick incoming outgoing = q.tick (some (incoming.getD {})) false := by
  have room : q.writable = true := by
    simp only [willPush, Bool.and_eq_true] at push
    exact push.2
  simp only [tick, push, noPop]
  simp only [willPush, Option.isSome_some, Bool.true_and, room,
    willPop, Bool.false_and, Bool.false_eq_true, ↓reduceIte, Option.getD_some]

theorem Queue.tick_pop_only (q : Queue addrBits) (incoming : Option Chunk) (outgoing : Bool)
    (noPush : q.willPush incoming = false) (pop : q.willPop outgoing = true) :
    q.tick incoming outgoing = q.tick none true := by
  have ready : q.readable = true := by
    simp only [willPop, Bool.and_eq_true] at pop
    exact pop.2
  simp only [tick, noPush, pop]
  simp [willPush, willPop, ready]

theorem Queue.tick_exchange (q : Queue addrBits) (incoming : Option Chunk) (outgoing : Bool)
    (push : q.willPush incoming = true) (pop : q.willPop outgoing = true) :
    q.tick incoming outgoing = q.tick (some (incoming.getD {})) true := by
  have room : q.writable = true := by
    simp only [willPush, Bool.and_eq_true] at push
    exact push.2
  have ready : q.readable = true := by
    simp only [willPop, Bool.and_eq_true] at pop
    exact pop.2
  simp only [tick, push, pop]
  simp [willPush, willPop, room, ready]

theorem Queue.Contents.tick (q : Queue addrBits) (chunks : List Chunk)
    (incoming : Option Chunk) (outgoing : Bool) (contents : q.Contents chunks) :
    (q.tick incoming outgoing).Contents (q.traceTick chunks incoming outgoing) := by
  by_cases push : q.willPush incoming = true <;> by_cases pop : q.willPop outgoing = true
  all_goals simp only [traceTick, push, pop, Bool.false_eq_true, ↓reduceIte]
  · rw [q.tick_exchange incoming outgoing push pop]
    apply contents.exchange
    · simp only [willPush, Bool.and_eq_true, writable, decide_eq_true_eq] at push
      exact push.2
    · simp only [willPop, Bool.and_eq_true, readable, bne_iff_ne] at pop
      omega
  · rw [q.tick_push_only incoming outgoing push (Bool.eq_false_iff.mpr pop)]
    apply contents.push
    simp only [willPush, Bool.and_eq_true, writable, decide_eq_true_eq] at push
    exact push.2
  · rw [q.tick_pop_only incoming outgoing (Bool.eq_false_iff.mpr push) pop]
    apply contents.pop
    simp only [willPop, Bool.and_eq_true, readable, bne_iff_ne] at pop
    omega
  · rw [q.tick_no_effect incoming outgoing (Bool.eq_false_iff.mpr push) (Bool.eq_false_iff.mpr pop)]
    exact contents

theorem Queue.Contents.flow (q : Queue addrBits) (chunks : List Chunk)
    (incoming : Option Chunk) (outgoing : Bool) (contents : q.Contents chunks)
    (meaning : Chunk → List α) :
    chunks.flatMap meaning ++
        (if q.willPush incoming then meaning (incoming.getD {}) else []) =
      (if q.willPop outgoing then meaning q.peek else []) ++
        (q.traceTick chunks incoming outgoing).flatMap meaning := by
  by_cases pop : q.willPop outgoing = true
  · have nonempty : 0 < chunks.length := by
      simp only [willPop, Bool.and_eq_true, readable, bne_iff_ne] at pop
      have := contents.length
      omega
    cases chunks with
    | nil => simp at nonempty
    | cons first rest =>
      have peek : q.peek = first := contents.peek q (first :: rest) nonempty
      by_cases push : q.willPush incoming = true <;>
        simp [traceTick, pop, push, peek, List.append_assoc]
  · by_cases push : q.willPush incoming = true <;> simp [traceTick, pop, push]

end Pinwheel.Program.Streaming
