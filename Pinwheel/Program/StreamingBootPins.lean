import Pinwheel.Program.StreamingCompile
import Pinwheel.Program.StreamingSession
import Pinwheel.Program.StreamingBootControl

/-! Concrete physical upload waveforms for the streaming host link. The wire
CRC and all request bits are constructed here, independently of the frontend. -/
namespace Pinwheel.Program.Streaming.BootPins

def idlePin (raw : BitVec 2 := 0) : Session.Pins := { rawInputs := raw }
def lowPin (nibble : BitVec 4) (raw : BitVec 2 := 0) : Session.Pins :=
  { csn := false, mosi := nibble, rawInputs := raw }
def highPin (nibble : BitVec 4) (raw : BitVec 2 := 0) : Session.Pins :=
  { csn := false, sck := true, mosi := nibble, rawInputs := raw }

def requestCRC (logical : BitVec 160) : BitVec 16 :=
  (List.range 40).foldl (fun crc k => Host.crcNibble crc (logical.extractLsb' ((39-k)*4) 4)) 65535

def request (opcode : BitVec 4) (sequence : BitVec 16) (payload : BitVec 128) : BitVec 176 :=
  let logical : BitVec 160 := (0xA72#12 ++ opcode) ++ (sequence ++ payload)
  logical ++ requestCRC logical

def writeRequest (sequence : BitVec 16) (address : BitVec 6) (word : BitVec 64) : BitVec 176 :=
  request 1 sequence (address ++ (word ++ 0#58))

def commitRequest (sequence : BitVec 16) (count : BitVec 7) (idle : Engine.Reactive.Pins) : BitVec 176 :=
  request 2 sequence (count ++ (idle.levels ++ (idle.enabled ++ 0#115)))

def requestPins (word : BitVec 176) (raw : BitVec 2 := 0) : List Session.Pins :=
  [idlePin raw] ++
  (List.range 44).flatMap (fun k =>
    let nibble := word.extractLsb' ((43-k)*4) 4
    [lowPin nibble raw, highPin nibble raw]) ++ [idlePin raw]

def readPins (raw : BitVec 2 := 0) : List Session.Pins :=
  (List.range 52).flatMap (fun _ => [lowPin 0 raw, highPin 0 raw]) ++ [idlePin raw]

/-- Fifty deselected clocks complete dispatch and all response CRC work. The
exact response read then makes the frontend available for the next request. -/
def transaction (word : BitVec 176) (raw : BitVec 2 := 0) : List Session.Pins :=
  requestPins word raw ++ List.replicate 50 (idlePin raw) ++ readPins raw

def upload (words : List (BitVec 64)) (idle : Engine.Reactive.Pins) (raw : BitVec 2 := 0) : List Session.Pins :=
  (words.zipIdx.flatMap (fun (word,k) =>
    transaction (writeRequest (BitVec.ofNat 16 k) (BitVec.ofNat 6 k) word) raw)) ++
  transaction (commitRequest (BitVec.ofNat 16 words.length) (BitVec.ofNat 7 words.length) idle) raw

def compiled (image : Compiled source idle) (raw : BitVec 2 := 0) : List Session.Pins :=
  upload image.words idle raw

def spi : List Session.Pins := compiled (spiImage 3)
def jtag : List Session.Pins := compiled (jtagImage 3)

theorem transaction_length (word : BitVec 176) (raw : BitVec 2) : (transaction word raw).length = 245 := by
  rfl

abbrev Control := Host.BootControl.State

def initialControl : Control := { csnPrev := true }

def coldPin : Session.Pins := { «initialize» := true }

theorem spi_length : spi.length = 1225 := by decide +kernel
theorem jtag_length : jtag.length = 3430 := by decide +kernel

def nextDelivery (words : List (BitVec 64)) (idle : Engine.Reactive.Pins)
    (n : Nat) (installed : Bool) (c : Host.Command) : Option (Nat × Bool) :=
  if c.runtime.initialize || c.runtime.txPush || c.runtime.rxPop then none
  else if c.runtime.command == 0 then some (n,installed)
  else if c.runtime.command == 1 && !installed && n < words.length &&
      c.address == BitVec.ofNat 6 n && c.word == words[n]?.getD 0 then some (n+1,false)
  else if c.runtime.command == 2 && !installed && n == words.length &&
      c.count == BitVec.ofNat 7 words.length && c.idle == idle then some (n,true)
  else none

def controlSafe (s : Control) : Bool :=
  s.phase != 2 && (s.phase != 1 || !(Host.BootControl.restore s).bulk)

def check (words : List (BitVec 64)) (idle : Engine.Reactive.Pins) :
    Control → Nat → Bool → List Session.Pins → Bool
  | control,n,installed,[] =>
      installed && n == words.length && control.phase == 0 && !control.ready && !control.active
  | control,n,installed,pin::rest =>
      controlSafe control &&
      match nextDelivery words idle n installed (Host.BootControl.command (pin.host {}) control) with
      | none => false
      | some (n,installed) => check words idle (Host.BootControl.step false (pin.host {}) control) n installed rest

theorem spi_check : check (spiImage 3).words ⟨4,7⟩ initialControl 0 false spi = true := by
  decide +kernel

theorem jtag_check : check (jtagImage 3).words ⟨0,7⟩ initialControl 0 false jtag = true := by
  decide +kernel

structure CommandSafe (c : Host.Command) : Prop where
  cold : c.runtime.initialize = false
  tx : c.runtime.txPush = false
  rx : c.runtime.rxPop = false

inductive Delivery (words : List (BitVec 64)) (idle : Engine.Reactive.Pins)
    (n : Nat) (installed : Bool) (c : Host.Command) : Nat → Bool → Prop
  | quiet (safe : CommandSafe c) (command : c.runtime.command = 0#4) :
      Delivery words idle n installed c n installed
  | write (safe : CommandSafe c) (before : installed = false) (within : n < words.length)
      (command : c.runtime.command = 1#4) (address : c.address = BitVec.ofNat 6 n)
      (word : c.word = words[n]?.getD 0) : Delivery words idle n installed c (n+1) false
  | commit (safe : CommandSafe c) (before : installed = false) (complete : n = words.length)
      (command : c.runtime.command = 2#4) (count : c.count = BitVec.ofNat 7 words.length)
      (pins : c.idle = idle) : Delivery words idle n installed c n true

theorem nextDelivery_sound (words : List (BitVec 64)) (idle : Engine.Reactive.Pins)
    (n : Nat) (installed : Bool) (c : Host.Command) (next : Nat × Bool)
    (checked : nextDelivery words idle n installed c = some next) :
    Delivery words idle n installed c next.1 next.2 := by
  unfold nextDelivery at checked
  split at checked
  · contradiction
  · rename_i ordinary
    have safe : CommandSafe c := by
      constructor
      all_goals cases cold : c.runtime.initialize <;> cases tx : c.runtime.txPush <;>
        cases rx : c.runtime.rxPop <;> simp_all
    split at checked
    · rename_i command
      have cmd : c.runtime.command = 0#4 := by simpa using command
      cases checked
      exact .quiet safe cmd
    · split at checked
      · rename_i fields
        simp only [Bool.and_eq_true,Bool.not_eq_true',beq_iff_eq,decide_eq_true_eq] at fields
        cases checked
        exact .write safe fields.1.1.1.2 fields.1.1.2 fields.1.1.1.1 fields.1.2 fields.2
      · split at checked
        · rename_i fields
          simp only [Bool.and_eq_true,Bool.not_eq_true',beq_iff_eq] at fields
          cases checked
          exact .commit safe fields.1.1.1.2 fields.1.1.2 fields.1.1.1.1 fields.1.2 fields.2
        · contradiction

theorem controlSafe_sound (s : Control) (checked : controlSafe s = true) : Host.BootControl.Safe s := by
  simp only [controlSafe,Bool.and_eq_true,Bool.or_eq_true,Bool.not_eq_true',bne_iff_ne,
    BitVec.ofNat_eq_ofNat] at checked
  exact ⟨checked.1,fun phase => checked.2.resolve_left (fun ne => ne phase)⟩

inductive Certified (words : List (BitVec 64)) (idle : Engine.Reactive.Pins) :
    Control → Nat → Bool → List Session.Pins → Prop
  | nil (control : Control) (n : Nat) (installed : Bool)
      (complete : n = words.length) (done : installed = true)
      (phase : control.phase = 0#3) (ready : control.ready = false) (active : control.active = false) :
      Certified words idle control n installed []
  | cons {control n installed pin rest nextN nextInstalled}
      (safe : Host.BootControl.Safe control)
      (delivery : Delivery words idle n installed (Host.BootControl.command (pin.host {}) control) nextN nextInstalled)
      (after : Certified words idle (Host.BootControl.step false (pin.host {}) control) nextN nextInstalled rest) :
      Certified words idle control n installed (pin::rest)

theorem check_sound (words : List (BitVec 64)) (idle : Engine.Reactive.Pins)
    (control : Control) (n : Nat) (installed : Bool) (pins : List Session.Pins)
    (checked : check words idle control n installed pins = true) :
    Certified words idle control n installed pins := by
  induction pins generalizing control n installed with
  | nil =>
    simp only [check,Bool.and_eq_true,Bool.not_eq_true',beq_iff_eq,BitVec.ofNat_eq_ofNat] at checked
    exact .nil control n installed checked.1.1.1.2 checked.1.1.1.1 checked.1.1.2 checked.1.2 checked.2
  | cons pin rest ih =>
    simp only [check,Bool.and_eq_true] at checked
    cases found : nextDelivery words idle n installed (Host.BootControl.command (pin.host {}) control) with
    | none =>
      simp only [found,Bool.false_eq_true] at checked
      exact False.elim checked.2
    | some next =>
      apply Certified.cons (controlSafe_sound control checked.1) (nextDelivery_sound _ _ _ _ _ next found)
      exact ih _ _ _ (by simpa only [found] using checked.2)

theorem spi_certified : Certified (spiImage 3).words ⟨4,7⟩ initialControl 0 false spi :=
  check_sound _ _ _ _ _ _ spi_check

theorem jtag_certified : Certified (jtagImage 3).words ⟨0,7⟩ initialControl 0 false jtag :=
  check_sound _ _ _ _ _ _ jtag_check

end Pinwheel.Program.Streaming.BootPins
