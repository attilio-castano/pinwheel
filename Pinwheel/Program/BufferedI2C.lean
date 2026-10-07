import Pinwheel.Program.Buffered

/-! A data-independent four-byte register-read frontend for the reference
buffered reactive engine. This is a compact stored syntax, not an upload image
or a universal electrical/protocol-success theorem. The three TX control bytes
are supplied in wire order by the caller; the result appends thirty-two bits.
ACK decisions occupy scratch zero, independently of the data RX prefix. -/
namespace Pinwheel.Program.BufferedI2C
open Pinwheel.Program.Buffered
open Pinwheel.Engine.Reactive (Pins Action Capture)
open Pinwheel.Engine.Reactive.Counted (Schedule)

def chain : List (Schedule Instruction) → Schedule Instruction
  | [] => .emit {operation := .halt}
  | [last] => last
  | first :: rest => .seq first (chain rest)

def leaf (operation : Operation) (append : Option (Fin 2) := none)
    (preserveEnabled : BitVec 3 := 0) : Schedule Instruction :=
  .emit {operation, append, preserveEnabled}

def action (duration : Fin 256) (enabled : BitVec 3) : Action 15 := ⟨⟨0, enabled⟩, duration, none⟩

def wait (budget : Fin 256) (enabled : BitVec 3) (preserve : BitVec 3 := 0) : Schedule Instruction :=
  leaf (.wait ⟨⟨0, enabled⟩, ⟨0, true⟩, budget⟩) none preserve

def high (duration : Fin 256) (enabled : BitVec 3) (preserve : BitVec 3 := 0)
    (append : Option (Fin 2) := none) (capture : Option (Capture 15) := none) : Schedule Instruction :=
  leaf (.checked (action duration enabled) ⟨1, 1⟩ capture .sequential) append preserve

def txByte (duration budget : Fin 256) : Schedule Instruction :=
  let bit := chain [leaf (.shift 1 true true (action duration 1)), wait budget 0 2,
    high duration 0 2, leaf (.checked (action duration 1) ⟨0, 0⟩ none) none 2]
  let ack := chain [leaf (.drive (action duration 1)), wait budget 0,
    high duration 0 0 none (some ⟨1, 0⟩),
    leaf (.checked (action duration 1) ⟨0, 0⟩ none (.branch 0 (.absolute 265) .next))]
  .seq (.repeat 7 bit) ack

def rxByte (duration budget : Fin 256) (nack : Bool) : Schedule Instruction :=
  let bit := chain [leaf (.drive (action duration 1)), wait budget 0,
    high duration 0 0 (some 1), leaf (.checked (action duration 1) ⟨0, 0⟩ none)]
  let low := if nack then 1 else 3
  let release := if nack then 0 else 2
  let ack := chain [leaf (.drive (action duration low)), wait budget release,
    high duration release, leaf (.checked (action duration low) ⟨0, 0⟩ none)]
  .seq (.repeat 7 bit) ack

def stop (duration budget : Fin 256) (terminal : Operation) : Schedule Instruction :=
  chain [leaf (.drive (action duration 3)), wait budget 2, high duration 2,
    leaf (.qualify ⟨⟨0, 0⟩, ⟨3, 3⟩, duration, budget⟩), leaf terminal]

def code (duration budget : Fin 256) : Schedule Instruction :=
  let initialBlock := chain [leaf (.qualify ⟨⟨0, 0⟩, ⟨3, 3⟩, duration, budget⟩),
    high duration 2, leaf (.drive (action duration 3))]
  let restart := chain [leaf (.drive (action duration 1)), wait budget 0,
    leaf (.checked (action duration 0) ⟨3, 3⟩ none), high duration 2,
    leaf (.drive (action duration 3))]
  chain [initialBlock, .repeat 1 (txByte duration budget), restart, txByte duration budget,
    .repeat 2 (rxByte duration budget false), rxByte duration budget true,
    stop duration budget .halt, stop duration budget (.fault .fault)]

def program (duration budget : Fin 256) : Program :=
  ⟨code duration budget, ⟨0, 0⟩, by
      simp [code, chain, txByte, rxByte, stop, high, wait, leaf, Schedule.span]
      decide,
    by simp [code, chain, txByte, rxByte, stop, high, wait, leaf, Schedule.nodes],
    by simp [code, chain, txByte, rxByte, stop, high, wait, leaf, Schedule.nesting]⟩

set_option maxRecDepth 5000 in
theorem virtual_span (duration budget : Fin 256) : (code duration budget).span = 270 := by
  rfl
  done

set_option maxRecDepth 5000 in
theorem stored_words (duration budget : Fin 256) : (code duration budget).words = 50 := by
  rfl
  done

set_option maxRecDepth 5000 in
theorem stored_nodes (duration budget : Fin 256) : (code duration budget).nodes = 105 := by
  rfl
  done

end Pinwheel.Program.BufferedI2C
