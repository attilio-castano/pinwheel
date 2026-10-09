import Pinwheel.Program.BufferedI2C
import Pinwheel.Hardware.Buffered.DecodedExecution
import Pinwheel.Hardware.Buffered.SramExecution

/-! The bounded four-byte register-read source decoded from its actual binary
instruction, loop and shared-branch fields. The decoder consumes only resident
bytes and metadata. Its source-execution theorem quantifies over all raw-input
histories, capacities, transfer states and edge counts. Packed-circuit/source
refinement and a universal Python compiler theorem remain separate gates. -/
namespace Pinwheel.Hardware.Buffered.I2cSource
open Pinwheel.Program Pinwheel.Engine.Reactive
open Pinwheel.Engine.Reactive.Counted

def source : Program.Buffered.Program := BufferedI2C.program 3 31

def flatten : Schedule Program.Buffered.Instruction → List Program.Buffered.Instruction
  | .emit i => [i]
  | .seq a b => flatten a ++ flatten b
  | .repeat _ body => flatten body

def captureBits : Option (Capture 15) → Nat
  | none => 0
  | some c => 1 + 2 * c.input.val + 4 * c.destination.val

def appendBits : Option (Fin 2) → Nat
  | none => 0
  | some input => input.val + 1

def encodeInstruction (i : Program.Buffered.Instruction) : BitVec 64 :=
  let fields (kind : Nat) (pins : Pins) (duration : Fin 256)
      (capture : Option (Capture 15)) (terminal : Option (Capture 15))
      (guard : Check) (waitInput : Fin 2) (waitLevel : Bool) (budget : Fin 256)
      (preserveLevels preserveEnabled : BitVec 3) (output : Fin 3) (enable invert : Bool) :=
    BitVec.ofNat 64 (kind + 8 * pins.levels.toNat + 64 * pins.enabled.toNat +
      2^9 * duration.val + 2^17 * preserveLevels.toNat + 2^20 * output.val +
      2^22 * appendBits i.append + 2^24 * (if enable then 1 else 0) +
      2^25 * (if invert then 1 else 0) + 2^26 * preserveEnabled.toNat +
      2^29 * captureBits capture + 2^35 * captureBits terminal +
      2^41 * guard.mask.toNat + 2^43 * guard.value.toNat + 2^45 * waitInput.val +
      2^46 * (if waitLevel then 1 else 0) + 2^47 * budget.val)
  match i.operation with
  | .drive a => fields 0 a.pins a.durationMinusOne a.capture none ⟨0, 0⟩ 0 false 0 0 0 0 false false
  | .shift output enable invert a => fields 1 a.pins a.durationMinusOne a.capture none
      ⟨0, 0⟩ 0 false 0 0 0 output enable invert
  | .keep levels enabled a => fields 2 a.pins a.durationMinusOne a.capture none
      ⟨0, 0⟩ 0 false 0 levels enabled 0 false false
  | .halt => 3
  | .fault reason => BitVec.ofNat 64 (4 + if reason = .timeout then 2^55 else 0)
  | .wait w => fields 5 w.pins 0 none none ⟨0, 0⟩ w.condition.input w.condition.level
      w.budgetMinusOne i.preserveLevels i.preserveEnabled 0 false false
  | .checked a guard terminal _ => fields 6 a.pins a.durationMinusOne a.capture terminal
      guard 0 false 0 i.preserveLevels i.preserveEnabled 0 false false
  | .qualify q => fields 7 q.pins q.durationMinusOne none none q.condition 0 false
      q.budgetMinusOne i.preserveLevels i.preserveEnabled 0 false false

/-- The only absolute successor in this bounded source is its fault STOP.
Its three coordinate fields are retained in the byte descriptor and checked
by the independent decoder, rather than replacing it with a typed target. -/
def encodeTarget : Program.Buffered.Target → Nat
  | .next => 1
  | .absolute pc => 2 * pc.val + 2^11 * (if pc.val = 265 then 45 else 64)

def encodeFinish : Program.Buffered.Finish → BitVec 56
  | .sequential => 0
  | .jump pc => BitVec.ofNat 56 (1 + 2^6 * encodeTarget (.absolute pc))
  | .branch slot yes no => BitVec.ofNat 56
      (2 + 4 * slot.val + 2^6 * encodeTarget yes + 2^30 * encodeTarget no)

def controls : List Nat := [0, 0, 0, 923918, 923918, 923918, 3021070,
  269, 269, 269, 1048845, 0, 0, 0, 0, 0, 1857, 1857, 1857, 1050433,
  0, 0, 0, 0, 967266, 967266, 967266, 3064418, 609, 609, 609, 1049185,
  1921, 1921, 1921, 1050497, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def word (k : BitVec 6) : BitVec 64 :=
  ((flatten source.code)[k.toNat]?).map encodeInstruction |>.getD 0

def control (k : BitVec 6) : BitVec 24 := BitVec.ofNat 24 (controls[k.toNat]?.getD 0)

def branchIndex (k : BitVec 6) : BitVec 4 := if k = 10 ∨ k = 23 then 1 else 0

def dictionary (k : BitVec 4) : BitVec 56 :=
  if k = 1 then encodeFinish (.branch 0 (.absolute 265) .next) else 0

structure Image where
  words : Memory.Contents 6 64
  controls : Memory.Contents 6 24
  indices : Memory.Contents 6 4
  dictionary : Memory.Contents 4 56

def image : Image := ⟨word, control, branchIndex, dictionary⟩

def rows : Memory.Contents 6 92 := fun k => branchIndex k ++ (control k ++ word k)

def decodeCapture (v : BitVec 6) : Option (Option (Capture 15)) :=
  if v = 0 then some none
  else if v[0] then some (some ⟨(v.extractLsb' 1 1).toFin, (v.extractLsb' 2 4).toFin⟩)
  else none

def decodeAppend (v : BitVec 2) : Option (Option (Fin 2)) :=
  match v.toNat with | 0 => some none | 1 => some (some 0) | 2 => some (some 1) | _ => none

def decodeTarget (v : BitVec 24) : Option Program.Buffered.Target :=
  if v = 1 then some .next
  else if v[0] then none
  else if v.extractLsb' 11 7 = 45 ∧ v.extractLsb' 18 6 = 0 ∧ v.extractLsb' 1 10 = 265 then
    some (.absolute (v.extractLsb' 1 10).toFin)
  else none

def decodeFinish (v : BitVec 56) : Option Program.Buffered.Finish := do
  let finish ← match (v.extractLsb' 0 2).toNat with
    | 0 => some .sequential
    | 1 => match ← decodeTarget (v.extractLsb' 6 24) with
      | .absolute pc => some (.jump pc)
      | .next => none
    | 2 => some (.branch (v.extractLsb' 2 4).toFin
        (← decodeTarget (v.extractLsb' 6 24)) (← decodeTarget (v.extractLsb' 30 24)))
    | _ => none
  if encodeFinish finish = v then some finish else none

def decodeInstruction (w : BitVec 64) (branch : BitVec 56) : Option Program.Buffered.Instruction := do
  let append ← decodeAppend (w.extractLsb' 22 2)
  let entry ← decodeCapture (w.extractLsb' 29 6)
  let terminal ← decodeCapture (w.extractLsb' 35 6)
  let pins : Pins := ⟨w.extractLsb' 3 3, w.extractLsb' 6 3⟩
  let duration := (w.extractLsb' 9 8).toFin
  let budget := (w.extractLsb' 47 8).toFin
  let a : Action 15 := ⟨pins, duration, entry⟩
  let guard : Check := ⟨w.extractLsb' 41 2, w.extractLsb' 43 2⟩
  let levels := w.extractLsb' 17 3
  let enabled := w.extractLsb' 26 3
  let operation : Program.Buffered.Operation ← match (w.extractLsb' 0 3).toNat with
    | 0 => some (.drive a)
    | 1 => if h : (w.extractLsb' 20 2).toNat < 3 then
      some (.shift ⟨(w.extractLsb' 20 2).toNat, h⟩ w[24] w[25] a) else none
    | 2 => some (.keep levels enabled a)
    | 3 => some .halt
    | 4 => some (.fault (if w[55] then .timeout else .fault))
    | 5 => some (.wait ⟨pins, ⟨(w.extractLsb' 45 1).toFin, w[46]⟩, budget⟩)
    | 6 => some (.checked a guard terminal (← decodeFinish branch))
    | _ => some (.qualify ⟨pins, guard, duration, budget⟩)
  let i : Program.Buffered.Instruction := ⟨operation, append,
    (if (w.extractLsb' 0 3).toNat ≥ 5 then levels else 0),
    (if (w.extractLsb' 0 3).toNat ≥ 5 then enabled else 0)⟩
  let expectedBranch := match i.operation with | .checked _ _ _ f => encodeFinish f | _ => 0
  if encodeInstruction i = w ∧ expectedBranch = branch then some i else none

def decodeLeaf (i : Image) (pc : Nat) : Option Program.Buffered.Instruction :=
  let address := BitVec.ofNat 6 pc
  decodeInstruction (i.words address) (i.dictionary (i.indices address))

def depthAt (i : Image) (pc : Nat) : Nat :=
  ((i.controls (BitVec.ofNat 6 pc)).extractLsb' 0 2).toNat

/-- Parse compact loop intervals from depth, start, bound and end fields.
The parse traverses each stored leaf once per syntax visit. It never expands
the eight-bit or byte repeats into virtual instructions. It neither receives
the source schedule nor chooses paths from observed wire data. -/
def decodeRegion (i : Image) : Nat → Nat → Nat → Nat → Option (Schedule Program.Buffered.Instruction)
  | 0, _, _, _ => none
  | fuel + 1, first, stop, depth => do
    if first ≥ stop ∨ stop > 64 ∨ depth > 2 then none else do
      let c := i.controls (BitVec.ofNat 6 first)
      if depthAt i first < depth then none else do
        let (head, next) ← if depthAt i first = depth then do
          pure (.emit (← decodeLeaf i first), first + 1)
        else do
          if depth ≥ 2 then none else do
            let start := (c.extractLsb' (if depth = 0 then 2 else 11) 6).toNat
            if start ≠ first then none else do
              let ending ← (List.range (stop - first)).find? fun offset =>
                (i.controls (BitVec.ofNat 6 (first + offset))).getLsbD (20 + depth)
              let next := first + ending + 1
              let body ← decodeRegion i fuel first next (depth + 1)
              let bound := (c.extractLsb' (if depth = 0 then 8 else 17) 3).toFin
              pure (.repeat bound body, next)
        if next = stop then some head else do
          let rest ← decodeRegion i fuel next stop depth
          pure (.seq head rest)

def decodedCode : Schedule Program.Buffered.Instruction :=
  (decodeRegion image 64 0 50 0).getD (.emit {operation := .fault})

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
theorem parse_succeeds : decodeRegion image 64 0 50 0 = some decodedCode := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
theorem decoded_geometry : decodedCode.span = 270 ∧ decodedCode.words = 50 ∧
    decodedCode.nodes = 105 ∧ decodedCode.nesting = 2 := by
  decide +kernel

def decoded : Program.Buffered.Program :=
  ⟨decodedCode, ⟨0, 0⟩, by have := decoded_geometry.1; omega,
    by have := decoded_geometry.2.2.1; omega, by have := decoded_geometry.2.2.2; omega⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 12000000 in
/-- A finite address-decoder certificate covers every legal source PC, not an
execution trace. It makes no assumptions on later samples or control paths. -/
theorem decoded_fetch : ∀ pc : Program.Buffered.PC, decoded.fetch pc = source.fetch pc := by
  decide +kernel

theorem execution_equivalent : DecodedExecution.Equivalent source decoded := by
  refine ⟨funext (fun pc => (decoded_fetch pc).symm), rfl, ?_⟩
  apply Fin.ext
  simp only [Program.Buffered.Program.last, source, decoded, BufferedI2C.program,
    BufferedI2C.virtual_span, decoded_geometry.1]

/-- Equality begins at START, including its pre-edge sampled qualification,
and holds for any supplied transfer state; admission is not assumed here. -/
theorem source_start (capacity : Transfer.Capacity) (s : Program.Buffered.State) :
    Program.Buffered.start source capacity s = Program.Buffered.start decoded capacity s :=
  DecodedExecution.start_eq source decoded execution_equivalent capacity s

theorem source_advance (capacity : Transfer.Capacity) (s : Program.Buffered.State)
    (incoming : Inputs) :
    Program.Buffered.advance source capacity s incoming = Program.Buffered.advance decoded capacity s incoming :=
  DecodedExecution.advance_eq source decoded execution_equivalent capacity s incoming

/-- Arbitrary prefixes include clock stretching, ACK/NACK branches, lost-clock
faults, wait/qualification timeouts and partially retained TX/RX results. No
particular successful target trace is a premise of this execution theorem. -/
theorem source_run (capacity : Transfer.Capacity) (s : Program.Buffered.State)
    (incoming : Nat → Inputs) (edges : Nat) :
    Program.Buffered.run source capacity s incoming edges = Program.Buffered.run decoded capacity s incoming edges :=
  DecodedExecution.run_eq source decoded execution_equivalent capacity s incoming edges

theorem source_started_run (capacity : Transfer.Capacity) (s : Program.Buffered.State)
    (incoming : Nat → Inputs) (edges : Nat) :
    Program.Buffered.run source capacity (Program.Buffered.start source capacity s) incoming edges =
      Program.Buffered.run decoded capacity (Program.Buffered.start decoded capacity s) incoming edges := by
  rw [source_run, source_start]

def coordinates : Schedule α → Nat → Option (Nat × List Nat)
  | .emit _, pc => if pc = 0 then some (0, []) else none
  | .seq a b, pc => if pc < a.span then coordinates a pc
      else (coordinates b (pc - a.span)).map fun (row, env) => (a.words + row, env)
  | .repeat count body, pc => if pc < (count.val + 1) * body.span then
      (coordinates body (pc % body.span)).map fun (row, env) => (row, pc / body.span :: env)
      else none

/-- The encoded fault STOP's physical coordinate is derived from source
layout: row45, outside both counted loops, at virtual265. -/
theorem fault_stop_coordinates : coordinates source.code 265 = some (45, []) := by
  rfl

theorem branch_descriptor :
    (dictionary 1).extractLsb' 0 2 = 2 ∧
    (dictionary 1).extractLsb' 2 4 = 0 ∧
    (dictionary 1).extractLsb' 7 10 = 265 ∧
    (dictionary 1).extractLsb' 17 7 = 45 ∧
    (dictionary 1).extractLsb' 24 6 = 0 ∧
    (dictionary 1).extractLsb' 30 24 = 1 := by
  decide +kernel

def fullWords : Memory.Contents 6 144 := fun k => dictionary (branchIndex k) ++ (control k ++ word k)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem resident_at : ∀ k : BitVec 6,
    SramExecution.residentWords 50 rows dictionary k = fullWords k := by
  decide +kernel

theorem resident_words : SramExecution.residentWords 50 rows dictionary = fullWords := by
  funext k
  exact resident_at k

theorem rejects_reserved_word :
    decodeInstruction (word 0 ||| BitVec.ofNat 64 (2^56)) (dictionary 0) = none := by
  decide +kernel

theorem rejects_wrong_branch_coordinate :
    decodeFinish (BitVec.ofNat 56 (2 + 2^6 * (2 * 265 + 2^11 * 44) + 2^30)) = none := by
  decide +kernel

end Pinwheel.Hardware.Buffered.I2cSource
