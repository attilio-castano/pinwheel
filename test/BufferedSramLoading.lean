import Pinwheel.Hardware.Buffered.SramModel
import Pinwheel.Hardware.Buffered.SramState
import Pinwheel.Hardware.Buffered.SramLoading
import Pinwheel.Hardware.Buffered.SramExecution
import Lean

/-! Initialized loader/execution witnesses start both physical SRAM copies,
Q, controller registers, and the independent compact reference at unrelated
values. Equality is checked only where accepted commands establish it. The
optional fixtures come from canonical source lowering; their source admission
is checked by the narrow Python gate, rather than asserted by this test. -/
open Pinwheel.Hardware Pinwheel.Hardware.Buffered

private structure Command where
  coldInit : Bool := false
  command : Nat := 0
  address : Nat := 0
  word : Nat := 0
  control : Nat := 0
  branch : Nat := 0
  count : Nat := 0
  virtualSpan : Nat := 0
  idleLevels : Nat := 0
  idleEnabled : Nat := 0
  txData : Nat := 0
  txLength : Nat := 0
  rxCapacity : Nat := 0
  expectedGeneration : Nat := 0
  expectedTransfer : Nat := 0
  rawInputs : Nat := 3

private def Command.values (c : Command) : Values Reactive.Input
  | _, .initialize => BitVec.ofBool c.coldInit
  | _, .command => BitVec.ofNat 3 c.command
  | _, .address => BitVec.ofNat 6 c.address
  | _, .word => BitVec.ofNat 64 c.word
  | _, .control => BitVec.ofNat 24 c.control
  | _, .branch => BitVec.ofNat 56 c.branch
  | _, .count => BitVec.ofNat 7 c.count
  | _, .virtualSpan => BitVec.ofNat 11 c.virtualSpan
  | _, .idleLevels => BitVec.ofNat 3 c.idleLevels
  | _, .idleEnabled => BitVec.ofNat 3 c.idleEnabled
  | _, .txData => BitVec.ofNat 32 c.txData
  | _, .txLength => BitVec.ofNat 6 c.txLength
  | _, .rxCapacity => BitVec.ofNat 6 c.rxCapacity
  | _, .expectedGeneration => BitVec.ofNat 16 c.expectedGeneration
  | _, .expectedTransfer => BitVec.ofNat 16 c.expectedTransfer
  | _, .rawInputs => BitVec.ofNat 2 c.rawInputs
  | _, .readIndex => 0

private structure Reference where
  bank : Array Nat

private def Reference.values (s : Reference) : Values SharedBranches.Register := fun {w} r =>
  BitVec.ofNat w (s.bank[SharedBranches.registerIndex r]?.getD 0)

private def sourceExpressions : Array (Sigma (Expr Reactive.Input SharedBranches.Register)) :=
  SharedBranches.registers.map fun ⟨w,r⟩ => ⟨w,SharedBranches.circuit.next r⟩

private def Reference.step (s : Reference) (c : Command) : Reference :=
  ⟨MemoEval.evalMany c.values s.values sourceExpressions⟩

private structure Image where
  name : String
  words : Array Nat
  controls : Array Nat
  indices : Array Nat
  table : Array Nat
  span : Nat
  idleLevels : Nat := 0
  idleEnabled : Nat := 7
  txBits : Nat := 0
  rxBits : Nat := 0
  maxEdges : Nat := 300
  txData : Nat := 0x96a53cc3
  rawInputs : Array Nat := #[]
  expectedPhase : Nat := 0
  expectedRx : Nat := 0
  expectedRxLength : Nat := 0
  expectedConsumed : Nat := 0

private structure Stats where
  cases : Nat := 0
  edges : Nat := 0
  coreChecks : Nat := 0
  outputChecks : Nat := 0
  knownRowChecks : Nat := 0
  dictionaryChecks : Nat := 0
  entryChecks : Nat := 0
  candidateChecks : Nat := 0
  residentPremiseChecks : Nat := 0
  sourceResultChecks : Nat := 0
  negativeWitnesses : Nat := 0
  negativePremiseWitnesses : Nat := 0
  ordinaryBoundaries : Nat := 0
  deriving Lean.ToJson

private structure Pair where
  physical : SramModel.State
  source : Reference
  rows : Array Nat := Array.replicate 64 0
  table : Array Nat := Array.replicate 16 0
  rowKnown : Array Bool := Array.replicate 64 false
  tableKnown : Array Bool := Array.replicate 16 false
  stats : Stats := {}

private def check (ok : Bool) (label : String) : IO Unit :=
  unless ok do throw (IO.userError ("Initialized SRAM loading: " ++ label))

private def forgedRegisters (completeMasks : Bool) : Values Sram.Register
  | _, .core .valid => 1
  | _, .core .count => 1
  | _, .core .written => if completeMasks then 1 else 0
  | _, .branchWritten => if completeMasks then 65535 else 0
  | _, _ => 0

private def forgedState (completeMasks : Bool) : SramState.State :=
  ⟨forgedRegisters completeMasks, fun _ => ⟨fun _ => 1, 0⟩⟩

private theorem forged_count (completeMasks : Bool) :
    SramCoverage.ValidCount (forgedState completeMasks).registers := by
  intro _
  change 0 < (1 : BitVec 7).toNat ∧ (1 : BitVec 7).toNat ≤ 64
  decide +kernel

private theorem forged_initial_agrees (completeMasks : Bool) :
    SramLoading.Agrees (forgedState completeMasks) SramLoading.Ledger.initial :=
  SramLoading.agrees_initial _

private theorem forged_initial_coherent : SramLoading.Coherent SramLoading.Ledger.initial :=
  SramLoading.coherent_initial

private theorem forged_complete_masks :
    SramCoverage.ValidCoverage (forgedState true).registers := by
  intro _
  constructor
  · intro k hk
    change k.toNat < 1 at hk
    have hz : k = 0 := BitVec.eq_of_toNat_eq (by change k.toNat = 0; omega)
    subst k
    decide +kernel
  · rfl
  done

private theorem forged_complete_not_covered :
    ¬ SramLoading.Covered (forgedState true) SramLoading.Ledger.initial := by
  intro h
  have hk := h.rows 0 (by decide +kernel)
  simp only [SramLoading.Ledger.initial, Memory.Sram.Model.Defined,
    Memory.Sram.Model.initial, reduceCtorEq, exists_false] at hk
  done

private theorem forged_empty_covered :
    SramLoading.Covered (forgedState false) SramLoading.Ledger.initial := by
  constructor <;> simp [forgedState, forgedRegisters]
  done

private theorem forged_empty_not_admitted :
    ¬ SramCoverage.ValidCoverage (forgedState false).registers := by
  intro h
  have hm := (h rfl).2
  exact (by decide +kernel : (0 : BitVec 16) ≠ 65535) hm
  done

private theorem forged_not_resident (completeMasks : Bool) :
    ¬ SramExecution.Resident (forgedState completeMasks)
      SramLoading.Ledger.initial.rows SramLoading.Ledger.initial.dictionaryWords := by
  intro h
  have hl : SramExecution.live ((forgedState completeMasks).registers (.core .count)) 0 = true := by
    change SramExecution.live 1 0 = true
    decide +kernel
  have hm := h.2.2.1 0 0 hl
  change (1 : BitVec 64) = 0 at hm
  exact (by decide +kernel : (1 : BitVec 64) ≠ 0) hm
  done

private def dispatchRows : Memory.Contents 6 92 := fun k =>
  if k == 0 then BitVec.ofNat 92 448 else if k == 1 then 3 else 0

private def dispatchRegisters : Values Sram.Register
  | _, .core .valid => 1
  | _, .core .count => 2
  | _, .core .virtualSpan => 2
  | _, .core .phase => 1
  | _, .core .written => 3
  | _, .branchWritten => 65535
  | _, .startWord => 448
  | _, _ => 0

private def staleDispatch : SramState.State :=
  ⟨dispatchRegisters, fun _ => ⟨fun k => (dispatchRows k).extractLsb' 0 64, 0⟩⟩

private theorem stale_dispatch_resident :
    SramExecution.Resident staleDispatch dispatchRows (fun _ => 0) := by
  unfold SramExecution.Resident
  decide +kernel

private theorem stale_dispatch_not_ready :
    ¬ SramExecution.Ready staleDispatch dispatchRows := by
  unfold SramExecution.Ready SramCandidates.Ready
  decide +kernel

private theorem stale_dispatch_changes_entry :
    (staleDispatch.step (Command.values {})).registers (.core .phase) ≠
      Reactive.circuit.step (Command.values {})
        (SramExecution.reference staleDispatch dispatchRows (fun _ => 0)) .phase := by
  decide +kernel

private def negativePremises : IO Nat := do
  -- These theorem declarations are checked by the kernel during compilation.
  -- The runtime checks independently witness the decisive small fields.
  check ((forgedState true).registers (.core .valid) == 1 &&
    (forgedState true).registers (.core .written) == 1 &&
    (forgedState true).registers .branchWritten == 65535)
    "forged startup has syntactically complete masks without initialized ledger provenance"
  check ((forgedState false).registers (.core .valid) == 1 &&
    (forgedState false).registers (.core .written) == 0 &&
    (forgedState false).registers .branchWritten == 0)
    "vacuous Covered alone cannot establish resident admission"
  let i : Values Reactive.Input := Command.values {}
  check ((staleDispatch.step i).registers (.core .phase) !=
    Reactive.circuit.step i (SramExecution.reference staleDispatch dispatchRows (fun _ => 0)) .phase)
    "a resident non-START dispatch with stale Q diverges without derived Ready"
  return 3

private def output (s : Pair) (o : Reactive.Output w) : Nat :=
  (s.physical.observe (Command.values {}) o).toNat

private def physicalState (s : SramModel.State) : SramState.State :=
  ⟨s.registers.values, fun p => ⟨s.contents p, BitVec.ofNat 64 s.q[p.val]!⟩⟩

private def seeded (seed : Nat) : Pair :=
  ⟨SramModel.State.initial (seed+1),
    ⟨SharedBranches.registers.mapIdx fun k ⟨w,_⟩ =>
      (seed*15485863 + k*32452843 + 49979687) % 2^w⟩,
    Array.replicate 64 0, Array.replicate 16 0,
    Array.replicate 64 false, Array.replicate 16 false, {}⟩

private def knownRowsAgree (s : Pair) : Bool := (List.range 64).all fun k =>
  !s.rowKnown[k]! || (s.source.values (.row (BitVec.ofNat 6 k))).toNat == s.rows[k]! &&
    ([0,1] : List (Fin 2)).all fun p =>
      (s.physical.contents p (BitVec.ofNat 6 k)).toNat == s.rows[k]! % 2^64 &&
      (s.physical.registers.values (.metadata (BitVec.ofNat 6 k))).toNat == s.rows[k]! / 2^64

private def tick (s : Pair) (c : Command := {}) (ordinary : Bool := false) : IO Pair := do
  let i : Values Reactive.Input := c.values
  let rowWrite := SharedBranches.rowWriting.eval i s.source.values == 1
  let tableWrite := SharedBranches.tableWriting.eval i s.source.values == 1
  let commit := SharedBranches.committing.eval i s.source.values == 1
  let first := (rowWrite || tableWrite) && s.source.values (.core .pending) == 0
  let entering := (SharedBranches.adapt Reactive.entering).eval i s.source.values == 1
  let pc := (SharedBranches.adapt Reactive.entryPC).eval i s.source.values
  let after := s.physical.step i
  let source := s.source.step c
  let mut stats := {s.stats with edges := s.stats.edges+1}
  if ordinary then
    let actual := (physicalState s.physical).step i
    check (after.registers.bank == (SramModel.snapshot actual.registers).bank)
      "memoized controller agrees with ordinary actual SramState.step"
    for p in ([0,1] : List (Fin 2)) do
      check (BitVec.ofNat 64 after.q[p.val]! == (actual.arrays p).q)
        "ordinary actual macro Q schedule"
      for k in [:64] do
        check (after.contents p (BitVec.ofNat 6 k) ==
          (actual.arrays p).contents (BitVec.ofNat 6 k))
          "ordinary actual macro contents"
    stats := {stats with ordinaryBoundaries := stats.ordinaryBoundaries+1}
  for ⟨_,r⟩ in SharedBranches.registers do
    match r with
    | .core r =>
      check (after.registers.values (.core r) == source.values (.core r))
        s!"all actual/reference core fields after edge {stats.edges}: {Reactive.registerLabel r}"
      stats := {stats with coreChecks := stats.coreChecks+1}
    | _ => pure ()
  for ⟨_,o⟩ in Reactive.outputs do
    let observed := if Reactive.outputLabel o == "rejected" then s.physical.observe i o else after.observe i o
    let expected := SharedBranches.circuit.observe i
      (if Reactive.outputLabel o == "rejected" then s.source.values else source.values) o
    check (observed == expected) s!"public {Reactive.outputLabel o} at edge {stats.edges}"
    stats := {stats with outputChecks := stats.outputChecks+1}
  check (Sram.rowWriting.eval (s.physical.inputs i) s.physical.registers.values ==
    BitVec.ofBool rowWrite) "actual row acceptance equals independent compact reference"
  check (Sram.tableWriting.eval (s.physical.inputs i) s.physical.registers.values ==
    BitVec.ofBool tableWrite) "actual dictionary acceptance equals independent compact reference"
  if entering && pc.toNat < (s.source.values (.core .count)).toNat then
    let actual := (Sram.rowExpr (pc.extractLsb' 0 6)).eval (s.physical.inputs i) s.physical.registers.values
    let expected := s.source.values (.row (pc.extractLsb' 0 6))
    check (actual == expected) "complete compact fetched row including control and dictionary index"
    check (s.physical.registers.values (.branch (actual.extractLsb' 88 4)) ==
      s.source.values (.branch (expected.extractLsb' 88 4))) "fetched dictionary descriptor"
    check ((Sram.adapt (SharedBranches.adapt Reactive.entryRecord)).eval
      (s.physical.inputs i) s.physical.registers.values ==
      (SharedBranches.adapt Reactive.entryRecord).eval i s.source.values)
      "complete decoded 144-bit entry record"
    stats := {stats with entryChecks := stats.entryChecks+1}
  let mut rowKnown := if c.coldInit || c.command == 7 || first then Array.replicate 64 false else s.rowKnown
  let mut tableKnown := if c.coldInit || c.command == 7 || first then Array.replicate 16 false else s.tableKnown
  let mut rows := s.rows
  let mut table := s.table
  if rowWrite then
    rowKnown := rowKnown.set! c.address true
    rows := rows.set! c.address (c.word + c.control*2^64 + c.branch*2^88)
    for p in ([0,1] : List (Fin 2)) do
      check (after.q[p.val]! == s.physical.q[p.val]!) "accepted writes hold unrelated Q"
  if tableWrite then
    tableKnown := tableKnown.set! c.address true
    table := table.set! c.address c.branch
  if commit then
    check ((List.range c.count).all fun k => rowKnown[k]!) "COMMIT derives every resident row from current upload"
    check (tableKnown.all id) "COMMIT derives all sixteen dictionary slots"
    for k in [c.count:64] do
      rows := rows.set! k 0
      check (source.values (.row (BitVec.ofNat 6 k)) == 0) "reference clears complete short replacement tail"
      check ((Sram.rowExpr (BitVec.ofNat 6 k)).eval (after.inputs i) after.registers.values == 0)
        "actual tail projection hides stale physical word and dictionary index"
      check (after.registers.values (.metadata (BitVec.ofNat 6 k)) == 0) "COMMIT clears tail metadata"
      rowKnown := rowKnown.set! k false
  for k in [:64] do
    check ((after.core .written).getLsbD k == rowKnown[k]!) "hardware row coverage tracks current selective upload"
  for k in [:16] do
    check ((after.registers.values .branchWritten).getLsbD k == tableKnown[k]!)
      "hardware dictionary coverage tracks every current upload slot"
  let pair : Pair := ⟨after,source,rows,table,rowKnown,tableKnown,stats⟩
  check (knownRowsAgree pair) "accepted commands establish both bank copies independently"
  stats := {stats with knownRowChecks := stats.knownRowChecks + 4*rowKnown.count true}
  for k in [:16] do
    if tableKnown[k]! then
      check (after.registers.values (.branch (BitVec.ofNat 4 k)) == BitVec.ofNat 56 table[k]! &&
        source.values (.branch (BitVec.ofNat 4 k)) == BitVec.ofNat 56 table[k]!)
        "accepted dictionary writes establish source and actual value independently"
      stats := {stats with dictionaryChecks := stats.dictionaryChecks+2}
  if output pair .valid == 1 then
    let count := (after.core .count).toNat
    check ((List.range count).all fun k => rowKnown[k]! &&
      (after.registers.values (.metadata (BitVec.ofNat 6 k))).toNat == rows[k]! / 2^64)
      "Resident premise: complete live metadata is derived from current accepted upload"
    check (tableKnown.all id) "Resident premise: complete current dictionary is derived from upload"
    check (after.registers.values .startWord == (source.values (.row 0)).extractLsb' 0 64)
      "Resident premise: live row-zero mirror follows current source row"
    stats := {stats with residentPremiseChecks := stats.residentPremiseChecks+1}
    for b in [false,true] do
      let port : Fin 2 := if b then 1 else 0
      let address := ((SramCandidates.candidate b).eval i after.core).extractLsb' 0 6
      if address.toNat < (after.core .count).toNat then
        check (BitVec.ofNat 64 after.q[port.val]! == (source.values (.row address)).extractLsb' 0 64)
          "live prospective candidate Q follows uploaded source row"
        stats := {stats with candidateChecks := stats.candidateChecks+1}
  return {pair with stats := stats}

private def rowCommand (image : Image) (k : Nat) : Command :=
  {command:=1,address:=k,word:=image.words[k]!,control:=image.controls[k]!,branch:=image.indices[k]!}

private def load (s : Pair) (image : Image) : IO Pair := do
  let mut s := s
  -- Interleave an out-of-order row with dictionary writes. Wrong duplicates
  -- must be replaced by the last accepted value, rather than ignored as seen.
  let last := image.words.size-1
  s ← tick s {command:=1,address:=last,word:=0xfeedface,control:=7,branch:=15}
  s ← tick s (rowCommand image last)
  s ← tick s {command:=6,address:=0,branch:=0xfeedface}
  for k in (List.range 16).reverse do
    s ← tick s {command:=6,address:=k,branch:=image.table[k]!}
  s ← tick s {command:=2,count:=image.words.size,virtualSpan:=image.span}
  if image.words.size > 1 then check (output s .valid == 0) "partial row coverage rejects COMMIT"
  for k in (List.range image.words.size).reverse do s ← tick s (rowCommand image k)
  s ← tick s {command:=2,count:=image.words.size,virtualSpan:=image.span, idleLevels:=image.idleLevels,idleEnabled:=image.idleEnabled} true
  check (output s .valid == 1 && output s .pending == 0) "complete upload accepted COMMIT"
  check (knownRowsAgree s) "resident bank equality is established, not an initial premise"
  return s

private def runImage (s : Pair) (image : Image) : IO Pair := do
  let mut s ← load s image
  let generation := output s .generation
  -- Deliberately corrupt Q. The immediate START must use accepted row zero's
  -- mirror, including its separately stored metadata and branch descriptor.
  s := {s with physical := {s.physical with q := #[0xffffffffffffffff,0x123456789abcdef0]}}
  s ← tick s {command:=3,expectedGeneration:=generation,txData:=image.txData, txLength:=image.txBits,rxCapacity:=image.rxBits} true
  check (output s .busy == 1 || output s .retained == 1) "immediate START owns accepted image"
  let mut runEdges := 0
  if output s .busy == 1 then
    for command in [1,2,3,6] do
      let before := s.physical.arrays
      let raw := image.rawInputs[runEdges]?.getD (s.stats.edges%4)
      let c : Command := {command:=command,count:=image.words.size,virtualSpan:=image.span, expectedGeneration:=generation,rawInputs:=raw}
      check (s.physical.observe c.values .rejected == 1) "busy owner rejects mutation"
      s ← tick s c
      runEdges := runEdges+1
      check (s.physical.arrays == before) "busy rejected mutation preserves both physical banks"
  for _ in [:image.maxEdges] do
    if output s .retained == 0 then
      s ← tick s {rawInputs:=image.rawInputs[runEdges]?.getD 3}
      runEdges := runEdges+1
  check (output s .retained == 1 && output s .busy == 0) s!"{image.name}: finite execution retains complete/fault/timeout result"
  if image.expectedPhase > 0 then
    check (runEdges == image.rawInputs.size) s!"{image.name}: actual execution edge count agrees with source/peer witness"
    check (output s .phase == image.expectedPhase && output s .rxData == image.expectedRx &&
      output s .rxLength == image.expectedRxLength && output s .txConsumed == image.expectedConsumed)
      s!"{image.name}: immutable result equals independently checked source/peer capture"
    s := {s with stats := {s.stats with sourceResultChecks:=s.stats.sourceResultChecks+1}}
  for command in [1,2,3,6] do
    let c : Command := {command:=command,count:=image.words.size,virtualSpan:=image.span, expectedGeneration:=generation}
    check (s.physical.observe c.values .rejected == 1) "retained owner rejects mutation"
    s ← tick s c
  s ← tick s {command:=4,expectedGeneration:=generation,expectedTransfer:=output s .transfer}
  check (output s .retained == 0 && output s .valid == 1) "matching RELEASE retains resident image"
  return {s with stats := {s.stats with cases:=s.stats.cases+1}}

private def directedImage (count : Nat) : Image :=
  {name:=s!"directed-{count}",words:=Array.ofFn fun k : Fin count =>
      if k.val+1 == count then 3 else 448+(k.val%8)*8,
    controls:=Array.replicate count 0,indices:=Array.replicate count 0,
    table:=Array.replicate 16 0,span:=count,maxEdges:=count+20}

private def directed (seed : Nat) : IO Pair := do
  let mut s := seeded seed
  check (s.physical.arrays[0]! != s.physical.arrays[1]!) "power-up macro replicas are independent"
  check (s.physical.q[0]! != s.physical.q[1]!) "power-up registered responses are unrelated"
  check ((s.source.values (.row 0)).extractLsb' 0 64 != s.physical.contents 0 0)
    "reference program words do not assume physical bank equality"
  let initialArrays := s.physical.arrays
  s ← tick s {coldInit:=true} true
  check (s.physical.arrays == initialArrays) "initialization preserves arbitrary physical contents"
  check (s.rowKnown.all (!·) && s.tableKnown.all (!·)) "initialization starts with no known uploaded cells"
  s ← tick s {command:=2,count:=1,virtualSpan:=1}
  check (output s .valid == 0) "COMMIT without upload rejected"
  s ← tick s {command:=3,expectedGeneration:=0}
  check (output s .busy == 0 && output s .retained == 0) "START without resident image rejected"
  s ← tick s {command:=1,address:=0,word:=3}
  for k in [:15] do s ← tick s {command:=6,address:=k,branch:=0}
  s ← tick s {command:=2,count:=1,virtualSpan:=1}
  check (output s .valid == 0 && output s .pending == 1) "unused sixteenth dictionary slot still mandatory"
  s ← tick s {command:=7}
  s ← tick s {command:=6,address:=15,branch:=0}
  s ← tick s {command:=2,count:=1,virtualSpan:=1}
  check (output s .valid == 0) "reset invalidates preceding row and dictionary coverage"
  s ← tick s {coldInit:=true}
  s ← runImage s (directedImage 64)
  s ← runImage s (directedImage 3)
  check (s.physical.contents 0 63 != 0) "short replacement deliberately leaves stale physical tail"
  let poisoned := {s with physical := {s.physical with arrays := s.physical.arrays.set! 1 ((s.physical.arrays[1]!).set! 0 0xbad)}}
  check (!knownRowsAgree poisoned) "single physical replica mutation breaks derived bank relation"
  let poisoned := {s with source := ⟨s.source.bank.set! (SharedBranches.registerIndex (.row 0)) 0⟩}
  check (!knownRowsAgree poisoned) "independent reference word mutation breaks derived bank relation"
  let poisoned := {s with physical := {s.physical with registers :=
      ⟨s.physical.registers.bank.set! (Sram.registerIndex (.metadata 0)) 1⟩}}
  check (!knownRowsAgree poisoned) "metadata mutation breaks complete derived row relation"
  let mutated := s.physical.registers.bank.set! (Sram.registerIndex (.branch 0)) 1
  check ((SramModel.Snapshot.values ⟨mutated⟩ (.branch 0)).toNat != s.table[0]!)
    "dictionary mutation breaks derived descriptor relation"
  let start : Command := {command:=3,expectedGeneration:=output s .generation}
  let mutated := s.physical.registers.bank.set! (Sram.registerIndex .startWord) 0
  check (Sram.starting.eval (s.physical.inputs start.values) s.physical.registers.values == 1)
    "mirror negative witness is an admitted START"
  check (Sram.instruction.eval (s.physical.inputs start.values) (SramModel.Snapshot.values ⟨mutated⟩) !=
    (s.source.values (.row 0)).extractLsb' 0 64) "START mirror mutation breaks fetched instruction identity"
  s := {s with stats := {s.stats with negativeWitnesses:=s.stats.negativeWitnesses+5}}
  s ← tick s {command:=7}
  check (output s .valid == 0 && s.rowKnown.all (!·) && s.tableKnown.all (!·))
    "warm reset invalidates resident correspondence knowledge"
  s ← tick s {command:=3,expectedGeneration:=output s .generation}
  check (output s .busy == 0) "invalidated image cannot restart"
  s ← load s (directedImage 3)
  s ← tick s {command:=3,expectedGeneration:=output s .generation}
  check (output s .busy == 1) "warm reset witness owns a running transfer"
  let arrays := s.physical.arrays
  let generation := output s .generation
  let transfer := output s .transfer
  s ← tick s {command:=7}
  check (output s .valid == 0 && output s .busy == 0 && output s .retained == 0 &&
    output s .generation == generation+1 && output s .transfer == transfer)
    "owned warm reset cancels runtime/image, advances generation and preserves transfer"
  check (s.physical.arrays == arrays) "owned warm reset keeps physical contents unrelated to reset"
  s ← load s (directedImage 3)
  s ← tick s {command:=3,expectedGeneration:=output s .generation}
  check (output s .busy == 1) "cold initialization witness owns a running transfer"
  let arrays := s.physical.arrays
  s ← tick s {coldInit:=true}
  check (output s .valid == 0 && output s .busy == 0 && output s .retained == 0 &&
    output s .generation == 0 && output s .transfer == 0)
    "owned cold initialization cancels runtime/image and clears identities"
  check (s.physical.arrays == arrays) "owned cold initialization preserves physical contents"
  return s

private def field (j : Lean.Json) (name : String) : IO Lean.Json := IO.ofExcept (j.getObjVal? name)
private def natField (j : Lean.Json) (name : String) : IO Nat := IO.ofExcept ((j.getObjVal? name).bind Lean.Json.getNat?)
private def arrayField (j : Lean.Json) (name : String) : IO (Array Nat) := do
  let a ← IO.ofExcept ((j.getObjVal? name).bind Lean.Json.getArr?)
  a.mapM fun v => IO.ofExcept v.getNat?

private def imageJson (j : Lean.Json) : IO Image := do
  let name ← IO.ofExcept ((j.getObjVal? "name").bind Lean.Json.getStr?)
  return ⟨name, ← arrayField j "words", ← arrayField j "controls", ← arrayField j "branch_indices",
    ← arrayField j "branch_table", ← natField j "virtual_span", ← natField j "idle_levels",
    ← natField j "idle_enabled", ← natField j "tx_bits", ← natField j "rx_reservation_bits",
    ← natField j "max_edges", ← natField j "tx_data", ← arrayField j "raw_inputs",
    ← natField j "expected_phase", ← natField j "expected_rx_data",
    ← natField j "expected_rx_length", ← natField j "expected_tx_consumed"⟩

private def Stats.add (a b : Stats) : Stats :=
  ⟨a.cases+b.cases,a.edges+b.edges,a.coreChecks+b.coreChecks,a.outputChecks+b.outputChecks,
    a.knownRowChecks+b.knownRowChecks,a.dictionaryChecks+b.dictionaryChecks,a.entryChecks+b.entryChecks,
    a.candidateChecks+b.candidateChecks,a.residentPremiseChecks+b.residentPremiseChecks,
    a.sourceResultChecks+b.sourceResultChecks,a.negativeWitnesses+b.negativeWitnesses,
    a.negativePremiseWitnesses+b.negativePremiseWitnesses,a.ordinaryBoundaries+b.ordinaryBoundaries⟩

def main (args : List String) : IO Unit := do
  let mut stats : Stats := {}
  for seed in [0,7,12345] do
    -- Three distinct kernel counterexamples are replayed alongside each
    -- independently seeded lifecycle, for nine recorded premise checks.
    let negativeCount ← negativePremises
    let s ← directed seed
    stats := stats.add {s.stats with negativePremiseWitnesses:=negativeCount}
  if let some path := args.head? then
    let j ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile path))
    let fixtures ← IO.ofExcept ((← field j "fixtures").getArr?)
    for seed in [0,7,12345] do
      for fixture in fixtures do
        let image ← imageJson fixture
        check (image.words.size > 0 && image.words.size ≤ 64 && image.controls.size == image.words.size &&
          image.indices.size == image.words.size && image.table.size == 16) "fixture admitted shape"
        let s ← tick (seeded seed) {coldInit:=true}
        let s ← runImage s image
        stats := stats.add s.stats
  IO.println ("BUFFERED_SRAM_LOADING_REPORT=" ++ (Lean.toJson stats).compress)
  IO.println s!"Initialized SRAM loading: {stats.cases} cases, {stats.edges} edges, unrelated startup banks/Q/reference, selective upload knowledge, complete entry records, immediate mirror START, retained ownership, reset and mutation witnesses passed."
