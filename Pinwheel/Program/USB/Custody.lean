import Pinwheel.Program.USB.LowSpeed
import Pinwheel.Program.StreamingReadyCustodySession

/-! Publication uses the existing two-word ownership and drain invariant. -/
namespace Pinwheel.USBHostFeasibility
open Pinwheel.USBPacketFeasibility
open Pinwheel.Program.Streaming
abbrev ReadyState := Pinwheel.Program.StreamingReady.State

structure QuietHost (h : Host.State) : Prop where
  control : h.ControlSafe
  noStaging : h.phase ≠ 2#3
  ackZero : h.ackOffset = 0#16
  exportZero : h.exportBits = 0#7
  startZero : h.exportStart = 0#16

def publishedCore (generation transfer : BitVec 16) (payload : List Bool) : ReadyState 1 :=
  { phase := .completed, generation := generation, transfer := transfer
    total := 64, rxProduced := 64, rx := commitDecoded (.data payload) }

def publishedSession (h : Host.State) (g t : BitVec 16) (payload : List Bool) :
    Pinwheel.Program.StreamingReady.Session.State 1 :=
  ⟨h, publishedCore g t payload⟩

def packetTrace (payload : List Bool) : BitTrace :=
  { captured := payload,
    rxQueued := [fullChunk (payload.take 32), fullChunk (payload.drop 32)] }

theorem packet_queue_bits (payload : List Bool) (size : payload.length = 64) :
    (packetTrace payload).rxQueued.flatMap Chunk.rxBits = payload := by
  have first : (payload.take 32).length = 32 := by simp [size]
  have second : (payload.drop 32).length = 32 := by simp [size]
  change (fullChunk (payload.take 32)).rxBits ++
    ((fullChunk (payload.drop 32)).rxBits ++ []) = payload
  rw [List.append_nil, chunk_roundtrip _ first, chunk_roundtrip _ second]
  exact List.take_append_drop 32 payload
  done

theorem terminal_publication_custody (h : Host.State) (clean : QuietHost h)
    (g t : BitVec 16) (payload : List Bool) (size : payload.length = 64) :
    (publishedSession h g t payload).Custody (packetTrace payload) := by
  constructor
  · exact clean.control
  · intro stage
    exact False.elim (clean.noStaging stage)
  · constructor <;> simp [publishedSession, publishedCore, clean.ackZero, clean.exportZero, clean.startZero]
  · refine ⟨[], ?_, ?_⟩ <;>
      simp [publishedSession, packetTrace, Host.State.exportedBits, clean.ackZero, clean.exportZero]
  · constructor
    · exact Queue.empty_contents 1
    · exact accepted_two_word_contents payload
    · simp [packetTrace, publishedSession, publishedCore, Pinwheel.Program.StreamingReady.State.pendingTx]
    · simp [packetTrace, publishedSession, publishedCore, Pinwheel.Program.StreamingReady.State.pendingRx]
      simpa [packetTrace] using (packet_queue_bits payload size).symm
  · constructor <;> simp [packetTrace, publishedSession, publishedCore, size]
  · constructor <;>
      simp [publishedSession, publishedCore, Pinwheel.Program.StreamingReady.State.ReservationCredit, Pinwheel.Program.StreamingReady.State.PartialCredit]
  · constructor <;>
      simp [publishedSession, publishedCore, Pinwheel.Program.StreamingReady.State.txFlight, Pinwheel.Program.StreamingReady.State.rxFlight,
        Pinwheel.Program.StreamingReady.Instruction.isStream]
  done

end Pinwheel.USBHostFeasibility
