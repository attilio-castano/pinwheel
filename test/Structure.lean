import Pinwheel.Hardware.Storage.SampledBackend
import Pinwheel.Hardware.Storage.EnabledBackend
import Pinwheel.Hardware.Storage.PrefetchEmit

/-! Executable structural report for the composed backends: arrival levels per
launch family and endpoint class, the cached-word enable cone, and the source
depths that earlier studies measured on emitted MLIR. -/

open Pinwheel.Hardware Pinwheel.Hardware.Loader Pinwheel.Hardware.Storage
open Backend

inductive Family where
  | pins | command | data | reset | cursor | registers
  deriving BEq, Repr

def Family.all : Array Family := #[.pins, .command, .data, .reset, .cursor, .registers]

def Family.label : Family → String
  | .pins => "incoming" | .command => "command" | .data => "data" | .reset => "init/reset"
  | .cursor => "loader cursor" | .registers => "registers"

def Family.input (f : Family) : Launch Machine.Input
  | _, .incoming => if f == .pins then some 0 else none
  | _, .command => if f == .command then some 0 else none
  | _, .data => if f == .data then some 0 else none
  | _, .init => if f == .reset then some 0 else none
  | _, .reset => if f == .reset then some 0 else none

def Family.register (f : Family) : Launch Backend.Register
  | _, .control .cursor => if f == .cursor || f == .registers then some 0 else none
  | _, _ => if f == .registers then some 0 else none

def Family.sampledRegister (f : Family) : Launch Sampled.Register
  | _, .inner r => f.register r
  | _, .extra _ => if f == .registers then some 0 else none

def registerClass : {w : Nat} → Backend.Register w → String
  | _, .control _ => "loader control" | _, .core _ => "core state"
  | _, .word _ _ => "dictionary words" | _, .index _ _ => "index maps"
  | _, .idle _ => "idle and last" | _, .last _ => "idle and last" | _, .current => "cached word"

def sampledClass : {w : Nat} → Sampled.Register w → String
  | _, .inner r => registerClass r
  | _, .extra _ => "pin stages"

def classes : Array String := #["loader control", "core state", "dictionary words", "index maps",
  "idle and last", "cached word", "fetched words", "pin stages"]

def prefetchClass : {w : Nat} → Backend.Prefetch.Register w → String
  | _, .inner r => registerClass r
  | _, .fetched _ => "fetched words"
  | _, .startWord => "fetched words"

def prefetchSampledClass : {w : Nat} → Extended Backend.Prefetch.Register PinSampler.Stage w → String
  | _, .inner r => prefetchClass r
  | _, .extra _ => "pin stages"

def Family.prefetchRegister (f : Family) : Launch Backend.Prefetch.Register
  | _, .inner r => f.register r
  | _, .fetched _ => if f == .registers then some 0 else none
  | _, .startWord => if f == .registers then some 0 else none

def Family.prefetchSampled (f : Family) : Launch (Extended Backend.Prefetch.Register PinSampler.Stage)
  | _, .inner r => f.prefetchRegister r
  | _, .extra _ => if f == .registers then some 0 else none

def show? : Option Nat → String
  | none => "null" | some n => toString n

/-- The condition of a recirculating register `mux enable new old`. -/
def enableOf : Expr I R w → Option (Expr I R 1)
  | .mux c _ _ => some c
  | _ => none

structure Row where
  family : String
  endpoint : String
  latest : Option Nat
  earliest : Option Nat

def combine (pick : Pick) (a b : Option Nat) : Option Nat := merge pick a b

/-- One pass per family and pick: shared wires are evaluated once. -/
def familyRows (cost : Cost) (n : Netlist R Machine.Output Machine.Input)
    (registers : Array (Sigma R)) (classOf : {w : Nat} → R w → String)
    (launch : Family → Launch R) (current : R 64) : Array Row := Id.run do
  let mut rows := #[]
  for f in Family.all do
    let perPick (pick : Pick) : Array (String × Option Nat) × Option Nat × Option Nat :=
      n.withArrivals pick cost f.input (launch f) fun c leaves =>
        (registers.map fun ⟨_, r⟩ => (classOf r, (c.next r).arrival pick cost leaves (launch f)),
         (enableOf (c.next current)).bind fun e => e.arrival pick cost leaves (launch f),
         Machine.outputs.foldl (fun acc ⟨_, o⟩ =>
           combine pick acc ((c.output o).arrival pick cost leaves (launch f))) none)
    let (late, lateEnable, lateOut) := perPick max
    let (early, earlyEnable, earlyOut) := perPick min
    for name in classes do
      let worst := late.foldl (fun acc (k, v) => if k == name then combine max acc v else acc) none
      let best := early.foldl (fun acc (k, v) => if k == name then combine min acc v else acc) none
      if late.any (·.1 == name) then
        rows := rows.push ⟨f.label, name, worst, best⟩
    rows := rows.push ⟨f.label, "cached word enable", lateEnable, earlyEnable⟩
    rows := rows.push ⟨f.label, "outputs", lateOut, earlyOut⟩
  return rows

/-- Latest arrival of the certified enable and data cones, per storing class. -/
def updateRows (cost : Cost) (n : Netlist Backend.Register Machine.Output Machine.Input) : Array Row := Id.run do
  let mut rows := #[]
  for f in Family.all do
    let cones : Array (String × Option Nat × Option Nat) :=
      n.withArrivals max cost f.input f.register fun c leaves =>
        Backend.registers.filterMap fun ⟨_, r⟩ =>
          if Enabled.stores r then
            (c.next r).updateShape.map fun u =>
              (registerClass r, u.enable.arrival max cost leaves f.register,
                u.data.arrival max cost leaves f.register)
          else none
    for name in classes do
      if cones.any (·.1 == name) then
        let enable := cones.foldl (fun acc (k, e, _) => if k == name then combine max acc e else acc) none
        let data := cones.foldl (fun acc (k, _, d) => if k == name then combine max acc d else acc) none
        rows := rows.push ⟨f.label, name, enable, data⟩
  return rows

def updateJson (rows : Array Row) : String :=
  "[" ++ String.intercalate ",\n    " (rows.toList.map fun r =>
    s!"\{\"family\":\"{r.family}\",\"endpoint\":\"{r.endpoint}\",\"enable\":{show? r.latest},\"data\":{show? r.earliest}}") ++ "]"

def policies : List (String × Enabled.Policy) :=
  [("none", .none), ("dictionary", .dictionary), ("storage", .storage)]

/-- Bits that recirculate through a multiplexer under each gating policy. -/
def policyJson : String :=
  let storing := Backend.registers.foldl (fun n ⟨w, r⟩ => if Enabled.stores r then n + w else n) 0
  "{" ++ String.intercalate ", " (policies.map fun (name, p) =>
    let gated := Backend.registers.filter fun ⟨_, r⟩ => p.gates r
    let bits := gated.foldl (fun n q => n + q.1) 0
    s!"\"{name}\": \{\"clock_gates\": {gated.size}, \"gated_bits\": {bits}, \"recirculating_bits\": {storing - bits}}") ++ "}"

def planText (p : Enabled.Policy) : String :=
  String.intercalate "\n" ((Backend.registers.filter fun ⟨_, r⟩ => p.gates r).toList.map fun ⟨w, r⟩ =>
    s!"r_{Backend.registerLabel r}\t{w}") ++ "\n"

def rowsJson (rows : Array Row) : String :=
  "[" ++ String.intercalate ",\n    " (rows.toList.map fun r =>
    s!"\{\"family\":\"{r.family}\",\"endpoint\":\"{r.endpoint}\",\"latest\":{show? r.latest},\"earliest\":{show? r.earliest}}") ++ "]"

/-- Depth from the loader cursor on the emitted operation graph, as the
bank-selection and cache-enable studies measured it from MLIR. -/
def sourceDepths (lateBank : Bool) (body : Circuit FinalInput Backend.Register Machine.Output) :
    List (String × Option Nat) :=
  let input : Launch Machine.Input := Family.cursor.input
  let register : Launch Backend.Register := Family.cursor.register
  let depth {w : Nat} (e : Backend.E w) := e.arrival max Cost.unit input register
  let successor := depth (BankSelect.successor lateBank)
  let successorLeaves (wire : Option Nat) : Launch SuccessorInput := WithWire.arrivals input wire
  let pc (wire : Option Nat) := BankSelect.nextPC.arrival max Cost.unit (successorLeaves wire) register
  let finalLeaves (wire : Option Nat) : Launch FinalInput :=
    WithWire.arrivals (successorLeaves wire) (pc wire)
  let enable (wire : Option Nat) := (enableOf (body.next .current)).bind fun e =>
    e.arrival max Cost.unit (finalLeaves wire) register
  let index := Backend.Readback.indexRead.bind
    (fun p => match p with | .selected => BankSelect.selected | .target => BankSelect.target)
    (fun r => .reg r)
  [("address", depth BankSelect.target), ("selection", depth BankSelect.selected),
   ("indexValue", if lateBank then none else depth index), ("successorValue", successor),
   ("pcValue", pc successor), ("enable_complete", enable successor),
   ("enable_successor_abstracted", enable none)]

/-- Arrival at each stage of the successor loop, for one launch family. -/
def stageArrivals (cost : Cost) (f : Family) (lateBank : Bool)
    (body : Circuit FinalInput Backend.Register Machine.Output) : List (String × Option Nat) :=
  let input : Launch Machine.Input := f.input
  let register : Launch Backend.Register := f.register
  let depth {w : Nat} (e : Backend.E w) := e.arrival max cost input register
  let successor := depth (BankSelect.successor lateBank)
  let successorLeaves : Launch SuccessorInput := WithWire.arrivals input successor
  let pc := BankSelect.nextPC.arrival max cost successorLeaves register
  let finalLeaves : Launch FinalInput := WithWire.arrivals successorLeaves pc
  [("read address", depth BankSelect.target), ("bank selection", depth BankSelect.selected),
   ("successor word", successor), ("next address", pc),
   ("cached word enable", (enableOf (body.next .current)).bind fun e => e.arrival max cost finalLeaves register),
   ("cached word", (body.next .current).arrival max cost finalLeaves register)]

def controlId : {w : Nat} → Loader.Register w → Nat
  | _, .active => 0 | _, .valid => 1 | _, .pending => 2 | _, .cursor => 3

def coreId : {w : Nat} → Reactive.Register w → Nat
  | _, .mode => 0 | _, .pc => 1 | _, .remaining => 2 | _, .waitLeft => 3
  | _, .levels => 4 | _, .enabled => 5 | _, .sample k => 6 + k.val

def registerId : {w : Nat} → Backend.Register w → Nat
  | _, .control r => controlId r
  | _, .core r => 10 + coreId r
  | _, .word b k => 100 + (if b then 32 else 0) + k.toNat
  | _, .index b k => 200 + (if b then 256 else 0) + k.toNat
  | _, .idle b => 800 + (if b then 1 else 0)
  | _, .last b => 810 + (if b then 1 else 0)
  | _, .current => 820

/-- Shortest path from each register's own output back to its data input. A
recirculating `mux enable new old` gives one multiplexer; such bits are the
ones a flow must protect against hold violations. -/
def selfLoops (cost : Cost) (lateBank : Bool)
    (body : Circuit FinalInput Backend.Register Machine.Output) : Array (String × Nat × Option Nat) :=
  let quiet : Launch Machine.Input := fun _ => none
  Backend.registers.map fun ⟨w, r⟩ =>
    let self : Launch Backend.Register := fun q => if registerId q == registerId r then some 0 else none
    let wires : Launch FinalInput := WithWire.arrivals (WithWire.arrivals quiet (some 0)) (some 0)
    let usesWires := ((body.next r).arrival min cost wires (fun _ => none)).isSome
    -- Compute wire arrivals as values first: a `Launch` is a function, and work
    -- placed inside it would be repeated at every leaf.
    let wireArrivals : Option Nat × Option Nat :=
      if usesWires then
        let successor := (BankSelect.successor lateBank).arrival min cost quiet self
        let successorLeaves : Launch SuccessorInput := WithWire.arrivals quiet successor
        (successor, BankSelect.nextPC.arrival min cost successorLeaves self)
      else (none, none)
    let leaves : Launch FinalInput :=
      WithWire.arrivals (WithWire.arrivals quiet wireArrivals.1) wireArrivals.2
    (registerClass r, w, (body.next r).arrival min cost leaves self)

def selfLoopJson (loops : Array (String × Nat × Option Nat)) : String :=
  let names := classes.filter fun name => loops.any (·.1 == name)
  "{" ++ String.intercalate ", " (names.toList.map fun name =>
    let mine := loops.filter (·.1 == name)
    let bits := mine.foldl (fun n (_, w, _) => n + w) 0
    let short := mine.foldl (fun n (_, w, a) => if a.any (· ≤ cost2) then n + w else n) 0
    let shortest := mine.foldl (fun acc (_, _, a) => merge min acc a) none
    s!"\"{name}\": \{\"bits\": {bits}, \"bits_within_one_multiplexer\": {short}, \"shortest\": {show? shortest}}") ++ "}"
where cost2 := Cost.gates.mux

def depthsJson (depths : List (String × Option Nat)) : String :=
  "{" ++ String.intercalate ", " (depths.map fun (k, v) => s!"\"{k}\":{show? v}") ++ "}"

def report (variant : String) (n : Netlist Backend.Register Machine.Output Machine.Input)
    (lateBank : Bool) (body : Circuit FinalInput Backend.Register Machine.Output) : String :=
  let plain (cost : Cost) := familyRows cost n Backend.registers registerClass Family.register .current
  let sampled (cost : Cost) := familyRows cost (PinSampler.netlist n) Sampled.registers sampledClass
    Family.sampledRegister (.inner .current)
  "{\n  \"variant\": \"" ++ variant ++ "\",\n  \"source_depth_from_cursor\": " ++
    depthsJson (sourceDepths lateBank body) ++
    ",\n  \"loop_stages_gates\": {" ++ String.intercalate ", " ([Family.registers, .pins, .command, .cursor].map fun f =>
      s!"\"{f.label}\": {depthsJson (stageArrivals Cost.gates f lateBank body)}") ++ "}" ++
    ",\n  \"self_loops_gates\": " ++ selfLoopJson (selfLoops Cost.gates lateBank body) ++
    ",\n  \"update_cones_gates\": " ++ updateJson (updateRows Cost.gates n) ++
    ",\n  \"policies\": " ++ policyJson ++
    ",\n  \"unit\": " ++ rowsJson (plain Cost.unit) ++
    ",\n  \"gates\": " ++ rowsJson (plain Cost.gates) ++
    ",\n  \"sampled_gates\": " ++ rowsJson (sampled Cost.gates) ++ "\n}\n"

/-- Arrival at each stage of the decoupled prefetch machine's loop, for one launch
family: the fed successor, the dispatch decision and target, the cached word,
both candidate addresses, the fetched registers and the start word. -/
def prefetchStages (cost : Cost) (f : Family) : List (String × Option Nat) :=
  let input : Launch Machine.Input := f.input
  let register : Launch Backend.Prefetch.Register := f.prefetchRegister
  let successor := Backend.Prefetch.successor.arrival max cost input register
  let l1 : Launch Backend.Prefetch.W1 := WithWire.arrivals input successor
  let dispatch := (Backend.Prefetch.sched Decoupled.dispatchingExpr).arrival max cost l1 register
  let target := (Backend.Prefetch.sched Reactive.target).arrival max cost l1 register
  let taken := (Backend.Prefetch.sched (Decoupled.candidateExpr true)).arrival max cost l1 register
  let untaken := (Backend.Prefetch.sched (Decoupled.candidateExpr false)).arrival max cost l1 register
  let l2 : Launch Backend.Prefetch.W2 := WithWire.arrivals l1 taken
  let l3 : Launch Backend.Prefetch.W3 := WithWire.arrivals l2 untaken
  let at3 {w : Nat} (r : Backend.Prefetch.Register w) :=
    (Backend.Prefetch.body.next r).arrival max cost l3 register
  let core := Reactive.registers.foldl (fun acc ⟨_, r⟩ => combine max acc (at3 (.inner (.core r)))) none
  [("fed successor", successor), ("dispatch decision", dispatch), ("target", target),
   ("cached word enable", Backend.Prefetch.enable3.arrival max cost l3 register),
   ("cached word", at3 (.inner .current)), ("candidate taken", taken), ("candidate untaken", untaken),
   ("fetched taken", at3 (.fetched true)), ("fetched untaken", at3 (.fetched false)),
   ("start word", at3 .startWord), ("core state", core)]

def prefetchReport : String :=
  let plain (cost : Cost) := familyRows cost Backend.Prefetch.netlist Backend.Prefetch.registers prefetchClass
    Family.prefetchRegister (.inner .current)
  let sampled (cost : Cost) := familyRows cost (PinSampler.netlist Backend.Prefetch.netlist)
    Backend.Prefetch.sampledRegisters prefetchSampledClass Family.prefetchSampled (.inner (.inner .current))
  "{\n  \"variant\": \"prefetch\"" ++
    ",\n  \"loop_stages_gates\": {" ++ String.intercalate ", " ([Family.registers, .pins, .command, .cursor].map fun f =>
      s!"\"{f.label}\": {depthsJson (prefetchStages Cost.gates f)}") ++ "}" ++
    ",\n  \"loop_stages_unit\": {" ++ String.intercalate ", " ([Family.registers, .pins].map fun f =>
      s!"\"{f.label}\": {depthsJson (prefetchStages Cost.unit f)}") ++ "}" ++
    ",\n  \"unit\": " ++ rowsJson (plain Cost.unit) ++
    ",\n  \"gates\": " ++ rowsJson (plain Cost.gates) ++
    ",\n  \"sampled_gates\": " ++ rowsJson (sampled Cost.gates) ++ "\n}\n"

def main (args : List String) : IO Unit := do
  let out := args.headD "build/structure"
  IO.FS.createDirAll out
  for (variant, text) in [
      ("command-split", report "command-split" (BankSelect.netlist false) false BankSelect.body),
      ("late-bank", report "late-bank" (BankSelect.netlist true) true BankSelect.body),
      ("enable-split", report "enable-split" CacheEnable.netlist false CacheEnable.body),
      ("prefetch", prefetchReport)] do
    IO.FS.writeFile (out ++ "/" ++ variant ++ ".json") text
    IO.println s!"Wrote structural report for {variant}."
  for (name, p) in policies do
    IO.FS.writeFile (out ++ "/plan-" ++ name ++ ".tsv") (planText p)
