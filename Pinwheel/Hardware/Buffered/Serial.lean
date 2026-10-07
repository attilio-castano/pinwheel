import Pinwheel.Hardware.Buffered.Reactive

/-! Version-one sampled-pin serial frontend for the buffered SRAM controller.
Requests are atomic 160-bit MSB-first frames, delivered only after CS closes.
A separate 192-bit read transaction returns an immutable response snapshot.
The core continues stepping while serial traffic is in flight. -/
namespace Pinwheel.Hardware.Buffered.Serial
open Pinwheel.Hardware

inductive Input : Nat → Type where
  | initialize : Input 1 | sck : Input 1 | mosi : Input 1 | csn : Input 1
  | rawInputs : Input 2
  | status : Reactive.Output w → Input w

inductive Register : Nat → Type where
  | sckPrev : Register 1 | csnPrev : Register 1
  | active : Register 1 | reading : Register 1 | count : Register 9
  | request : Register 160 | dispatch : Register 1 | capture : Register 1
  | code : Register 4 | sequence : Register 16 | rejected : Register 1
  | response : Register 192 | ready : Register 1

inductive Output : Nat → Type where
  | core : Reactive.Input w → Output w
  | miso : Output 1 | ready : Output 1

abbrev E := Expr Input Register
def both (a b : E 1) : E 1 := .band a b
def either (a b : E w) : E w := .inv (.band (.inv a) (.inv b))
def opcode : E 4 := .slice 144 4 (by decide) (.reg .request)
def op (n : Nat) : E 1 := .equal opcode (.lit (BitVec.ofNat 4 n))
def payload (start width : Nat) (h : start + width ≤ 128) : E width :=
  .slice start width (by omega) (.reg .request)
def reserved (used : Nat) (h : used ≤ 128) : E 1 :=
  .zero (payload used (128-used) (by omega))

/-- The decoder rejects every reserved payload bit, including unknown opcodes. -/
def reservedValid : E 1 :=
  .mux (op 0) (reserved 5 (by decide))
  (.mux (op 1) (reserved 98 (by decide))
  (.mux (op 2) (reserved 24 (by decide))
  (.mux (op 3) (reserved 60 (by decide))
  (.mux (op 4) (reserved 32 (by decide))
  (.mux (op 6) (reserved 60 (by decide))
  (.mux (either (op 7) (op 8)) (reserved 0 (by decide)) (.lit 0)))))))
def headerValid : E 1 :=
  .equal (.slice 148 12 (by decide) (.reg .request)) (.lit 0xA71)
def closingCode : E 4 :=
  .mux (.equal (.reg .count) (.lit 160))
    (.mux headerValid (.mux reservedValid (.lit 0) (.lit 3)) (.lit 2)) (.lit 1)

def starting : E 1 := both (.inv (.input .initialize))
  (both (.reg .csnPrev) (both (.inv (.input .csn)) (both (.inv (.input .sck))
    (both (.inv (.reg .active)) (both (.inv (.reg .dispatch)) (.inv (.reg .capture)))))))
def closing : E 1 := both (.reg .active) (.input .csn)
def closingRequest : E 1 := both closing (.inv (.reg .reading))
def closingReadExact : E 1 := both closing
  (both (.reg .reading) (.equal (.reg .count) (.lit 192)))
def taking : E 1 := both (.reg .active)
  (both (.inv (.input .csn)) (both (.input .sck) (.inv (.reg .sckPrev))))
def receiving : E 1 := both taking (.inv (.reg .reading))
def delivering : E 1 := both (.inv (.input .initialize))
  (both (.reg .dispatch) (.zero (.reg .code)))

/-- Status fields use the public Reactive.outputs order, least significant first.
Rejection is the dispatch-edge diagnostic, not the later quiet command value. -/
def packedStatus : E 155 :=
  (Expr.concat (a := 16) (b := 139) (.input (.status .scratch))
    (Expr.concat (a := 8) (b := 131) (.input (.status .waitLeft))
    (Expr.concat (a := 3) (b := 128) (.input (.status .phase))
    (Expr.concat (a := 3) (b := 125) (.input (.status .env1))
    (Expr.concat (a := 3) (b := 122) (.input (.status .env0))
    (Expr.concat (a := 10) (b := 112) (.input (.status .virtualPC))
    (Expr.concat (a := 2) (b := 110) (.input (.status .stage2))
    (Expr.concat (a := 2) (b := 108) (.input (.status .stage1))
    (Expr.concat (a := 1) (b := 107) (.input (.status .exhausted))
    (Expr.concat (a := 16) (b := 91) (.input (.status .transfer))
    (Expr.concat (a := 16) (b := 75) (.input (.status .generation))
    (Expr.concat (a := 1) (b := 74) (.input (.status .readBit))
    (Expr.concat (a := 1) (b := 73) (.input (.status .readValid))
    (Expr.concat (a := 32) (b := 41) (.input (.status .rxData))
    (Expr.concat (a := 6) (b := 35) (.input (.status .rxLength))
    (Expr.concat (a := 6) (b := 29) (.input (.status .txConsumed))
    (Expr.concat (a := 3) (b := 26) (.input (.status .enabled))
    (Expr.concat (a := 3) (b := 23) (.input (.status .levels))
    (Expr.concat (a := 8) (b := 15) (.input (.status .remaining))
    (Expr.concat (a := 8) (b := 7) (.input (.status .pc))
    (Expr.concat (a := 2) (b := 5) (.input (.status .mode))
    (Expr.concat (a := 1) (b := 4) (.reg .rejected)
    (Expr.concat (a := 1) (b := 3) (.input (.status .pending))
    (Expr.concat (a := 1) (b := 2) (.input (.status .retained))
    (Expr.concat (a := 1) (b := 1) (.input (.status .busy))
    (.input (.status .valid)))))))))))))))))))))))))))
def responseCode : E 4 :=
  .mux (both (.zero (.reg .code)) (.reg .rejected)) (.lit 4) (.reg .code)
def capturedResponse : E 192 :=
  .concat (Expr.concat (a := 12) (b := 4) (.lit 0x5A1) responseCode)
    (.concat (.reg .sequence) (Expr.concat (a := 5) (b := 155) (.lit 0) packedStatus))

def nextUninitialized : {w : Nat} → Register w → E w
  | _, .sckPrev => .input .sck
  | _, .csnPrev => .input .csn
  | _, .active => .mux starting (.lit 1) (.mux closing (.lit 0) (.reg .active))
  | _, .reading => .mux starting (.reg .ready) (.reg .reading)
  | _, .count => .mux starting (.lit 0)
      (.mux taking (.mux (.ult (.reg .count) (.lit 193))
        (.sub (.reg .count) (.lit 511)) (.reg .count)) (.reg .count))
  | _, .request => .mux (both starting (.inv (.reg .ready))) (.lit 0)
      (.mux receiving (Expr.concat (a := 159) (b := 1)
        (.slice 0 159 (by decide) (.reg .request : E 160))
        (.input .mosi : E 1)) (.reg .request))
  | _, .dispatch => closingRequest
  | _, .capture => .reg .dispatch
  | _, .code => .mux closingRequest closingCode (.reg .code)
  | _, .sequence => .mux closingRequest
      (.mux (.equal (.reg .count) (.lit 160))
        (.slice 128 16 (by decide) (.reg .request)) (.lit 0)) (.reg .sequence)
  | _, .rejected => .mux (.reg .dispatch)
      (.mux delivering (.input (.status .rejected)) (.lit 0)) (.reg .rejected)
  | _, .response => .mux (.reg .capture) capturedResponse (.reg .response)
  | _, .ready => .mux (.reg .capture) (.lit 1)
      (.mux closingReadExact (.lit 0) (.reg .ready))

/-- Physical POR clears the frontend, including the pending command pipelines.
Previous pin levels track POR samples, so POR cannot invent a rising SCK/CS edge. -/
def next : {w : Nat} → Register w → E w
  | _, .sckPrev => .input .sck
  | _, .csnPrev => .input .csn
  | _, r => .mux (.input .initialize) (.lit 0) (nextUninitialized r)

def coreInput : {w : Nat} → Reactive.Input w → E w
  | _, .initialize => either (.input .initialize) (both delivering (op 8))
  | _, .command => .mux (both delivering (.inv (op 8)))
      (.slice 0 3 (by decide) opcode) (.lit 0)
  | _, .address => .mux (op 6)
      (Expr.concat (a := 2) (b := 4) (.lit 0) (payload 56 4 (by decide)))
      (payload 92 6 (by decide))
  | _, .word => payload 0 64 (by decide)
  | _, .control => payload 64 24 (by decide)
  | _, .branch => .mux (op 6) (payload 0 56 (by decide))
      (Expr.concat (a := 52) (b := 4) (.lit 0) (payload 88 4 (by decide)))
  | _, .count => payload 0 7 (by decide)
  | _, .virtualSpan => payload 7 11 (by decide)
  | _, .idleLevels => payload 18 3 (by decide)
  | _, .idleEnabled => payload 21 3 (by decide)
  | _, .txData => payload 0 32 (by decide)
  | _, .txLength => payload 32 6 (by decide)
  | _, .rxCapacity => payload 38 6 (by decide)
  | _, .expectedGeneration => .mux (op 4) (payload 0 16 (by decide))
      (payload 44 16 (by decide))
  | _, .expectedTransfer => payload 16 16 (by decide)
  | _, .readIndex => .mux (both headerValid (both (op 0) (reserved 5 (by decide))))
      (payload 0 5 (by decide)) (.lit 0)
  | _, .rawInputs => .input .rawInputs

def miso : E 1 := .mux
  (both (.inv (.input .initialize)) (both (.reg .active) (.reg .reading)))
  ((List.finRange 192).foldl (fun acc k =>
    .mux (.equal (.reg .count) (.lit (BitVec.ofNat 9 k.val)))
      (.slice (191-k.val) 1 (by omega) (.reg .response)) acc) (.lit 0)) (.lit 0)
def output : {w : Nat} → Output w → E w
  | _, .core p => coreInput p
  | _, .miso => miso
  | _, .ready => .mux (.input .initialize) (.lit 0) (.reg .ready)
def circuit : Circuit Input Register Output := ⟨next,output⟩

def inputs : Array (Sigma Input) :=
  #[⟨1,.initialize⟩,⟨1,.sck⟩,⟨1,.mosi⟩,⟨1,.csn⟩,⟨2,.rawInputs⟩] ++
    Reactive.outputs.map (fun ⟨w,o⟩ => ⟨w,.status o⟩)
def outputs : Array (Sigma Output) :=
  Reactive.inputs.map (fun ⟨w,p⟩ => ⟨w,.core p⟩) ++ #[⟨1,.miso⟩,⟨1,.ready⟩]
def registers : Array (Sigma Register) :=
  #[⟨1,.sckPrev⟩,⟨1,.csnPrev⟩,⟨1,.active⟩,⟨1,.reading⟩,⟨9,.count⟩,
    ⟨160,.request⟩,⟨1,.dispatch⟩,⟨1,.capture⟩,⟨4,.code⟩,⟨16,.sequence⟩,
    ⟨1,.rejected⟩,⟨192,.response⟩,⟨1,.ready⟩]
def registerIndex : {w : Nat} → Register w → Nat
  | _, .sckPrev => 0 | _, .csnPrev => 1 | _, .active => 2 | _, .reading => 3
  | _, .count => 4 | _, .request => 5 | _, .dispatch => 6 | _, .capture => 7
  | _, .code => 8 | _, .sequence => 9 | _, .rejected => 10
  | _, .response => 11 | _, .ready => 12
def inputLabel : {w : Nat} → Input w → String
  | _, .initialize => "initialize" | _, .sck => "sck" | _, .mosi => "mosi"
  | _, .csn => "csn" | _, .rawInputs => "raw_inputs"
  | _, .status o => "status_" ++ Reactive.outputLabel o
def outputLabel : {w : Nat} → Output w → String
  | _, .core p => "core_" ++ Reactive.inputLabel p
  | _, .miso => "miso" | _, .ready => "ready"
def registerLabel : {w : Nat} → Register w → String
  | _, .sckPrev => "sck_prev" | _, .csnPrev => "csn_prev" | _, .active => "active"
  | _, .reading => "reading" | _, .count => "count" | _, .request => "request"
  | _, .dispatch => "dispatch" | _, .capture => "capture" | _, .code => "code"
  | _, .sequence => "sequence" | _, .rejected => "rejected"
  | _, .response => "response" | _, .ready => "ready"
def moduleText : Except String String := MemoEmit.moduleText
  "pinwheel_buffered_sram_serial_frontend" circuit inputs registers outputs
  inputLabel registerLabel outputLabel

end Pinwheel.Hardware.Buffered.Serial
