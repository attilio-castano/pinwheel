import Pinwheel.Hardware.Streaming.Frontend

namespace Pinwheel.Hardware.Streaming.Frontend
open Pinwheel.Hardware

def inputs : Array (Sigma Input) :=
  #[⟨1,.initialize⟩,⟨1,.sck⟩,⟨1,.csn⟩,⟨4,.mosi⟩,⟨2,.rawInputs⟩] ++
    Core.outputs.map (fun ⟨w,o⟩ => ⟨w,.status o⟩)
def outputs : Array (Sigma Output) :=
  Core.inputs.map (fun ⟨w,p⟩ => ⟨w,.core p⟩) ++ #[⟨4,.miso⟩,⟨1,.ready⟩]
def registers : Array (Sigma Register) :=
  #[⟨1, .sckPrev⟩, ⟨1, .csnPrev⟩, ⟨1, .active⟩, ⟨1, .reading⟩, ⟨7, .count⟩, ⟨176, .request⟩, ⟨16, .requestCRC⟩, ⟨3, .phase⟩, ⟨4, .code⟩, ⟨16, .sequence⟩, ⟨1, .cacheReply⟩, ⟨208, .response⟩, ⟨1, .ready⟩, ⟨1, .lastValid⟩, ⟨176, .lastRequest⟩, ⟨208, .lastReply⟩, ⟨7, .txLeft⟩, ⟨64, .txStaging⟩, ⟨1, .rxPending⟩, ⟨1, .workBulk⟩, ⟨64, .exportData⟩, ⟨16, .exportStart⟩, ⟨7, .exportBits⟩, ⟨16, .ackOffset⟩, ⟨192, .replyLogical⟩, ⟨192, .crcWork⟩, ⟨16, .crc⟩, ⟨6, .crcCount⟩]
def inputLabel : {w : Nat} → Input w → String
  | _, .initialize => "initialize" | _, .sck => "sck" | _, .csn => "csn"
  | _, .mosi => "mosi" | _, .rawInputs => "raw_inputs"
  | _, .status o => "status_" ++ Core.outputLabel o
def outputLabel : {w : Nat} → Output w → String
  | _, .core p => "core_" ++ Core.inputLabel p
  | _, .miso => "miso" | _, .ready => "ready"
def registerLabel : {w : Nat} → Register w → String
  | _, .sckPrev => "sck_prev"
  | _, .csnPrev => "csn_prev"
  | _, .active => "active"
  | _, .reading => "reading"
  | _, .count => "count"
  | _, .request => "request"
  | _, .requestCRC => "request_crc"
  | _, .phase => "phase"
  | _, .code => "code"
  | _, .sequence => "sequence"
  | _, .cacheReply => "cache_reply"
  | _, .response => "response"
  | _, .ready => "ready"
  | _, .lastValid => "last_valid"
  | _, .lastRequest => "last_request"
  | _, .lastReply => "last_reply"
  | _, .txLeft => "tx_left"
  | _, .txStaging => "tx_staging"
  | _, .rxPending => "rx_pending"
  | _, .workBulk => "work_bulk"
  | _, .exportData => "export_data"
  | _, .exportStart => "export_start"
  | _, .exportBits => "export_bits"
  | _, .ackOffset => "ack_offset"
  | _, .replyLogical => "reply_logical"
  | _, .crcWork => "crc_work"
  | _, .crc => "crc"
  | _, .crcCount => "crc_count"
def registerIndex : {w : Nat} → Register w → Nat
  | _, .sckPrev => 0
  | _, .csnPrev => 1
  | _, .active => 2
  | _, .reading => 3
  | _, .count => 4
  | _, .request => 5
  | _, .requestCRC => 6
  | _, .phase => 7
  | _, .code => 8
  | _, .sequence => 9
  | _, .cacheReply => 10
  | _, .response => 11
  | _, .ready => 12
  | _, .lastValid => 13
  | _, .lastRequest => 14
  | _, .lastReply => 15
  | _, .txLeft => 16
  | _, .txStaging => 17
  | _, .rxPending => 18
  | _, .workBulk => 19
  | _, .exportData => 20
  | _, .exportStart => 21
  | _, .exportBits => 22
  | _, .ackOffset => 23
  | _, .replyLogical => 24
  | _, .crcWork => 25
  | _, .crc => 26
  | _, .crcCount => 27
def moduleText : Except String String := Buffered.MemoEmit.moduleText
  "pinwheel_streaming_quad_frontend" circuit inputs registers outputs
  inputLabel registerLabel outputLabel

end Pinwheel.Hardware.Streaming.Frontend

