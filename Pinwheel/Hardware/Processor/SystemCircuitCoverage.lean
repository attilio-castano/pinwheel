import Pinwheel.Hardware.Processor.SystemCircuitProofs

/-! Coverage of all valid connected logical states. RAM contents and Q are
arbitrary. Inactive byte-request metadata and inactive fetch payloads may also
be arbitrary; the witness does not assume cleared hardware payload latches. -/
namespace Pinwheel.Hardware.Processor.SystemCircuit

set_option backward.isDefEq.respectTransparency false

open Memory

/-- An active request stores only its operand metadata; Q remains the memory's
existing snapshot. Inactive metadata comes from the caller, except pending=0. -/
def encodeRam (s : ByteAdapterModel.State aw) (inactive : Values (ByteAdapterCircuit.Metadata aw)) :
    Values (ByteAdapterCircuit.Register aw)
  | _, .left r => CommandFlops.encode s.memory r
  | _, .right r => match s.pending, r with
    | none, .at ⟨6,_⟩ => 0
    | none, r => inactive r
    | some req, .at ⟨0,_⟩ => match req with | .read .. => 0 | .store .. => 1
    | some req, .at ⟨1,_⟩ => match req with | .read signed .. => BitVec.ofBool signed | .store .. => 0
    | some req, .at ⟨2,_⟩ => req.size
    | some req, .at ⟨3,_⟩ => req.address
    | some req, .at ⟨4,_⟩ => req.offset
    | some req, .at ⟨5,_⟩ => match req with | .read .. => 0 | .store _ _ _ data => data
    | some _, .at ⟨6,_⟩ => 1
    | some _, .at ⟨k+7,h⟩ => False.elim (by change k+7 < 7 at h; omega)

theorem view_encodeRam (s : ByteAdapterModel.State aw) (inactive : Values (ByteAdapterCircuit.Metadata aw)) :
    ByteAdapterCircuit.view (encodeRam s inactive) = s := by
  have memory_eq : CommandFlops.view (ByteAdapterCircuit.memoryValues (encodeRam s inactive)) = s.memory := by
    change CommandFlops.view (CommandFlops.encode s.memory) = s.memory
    exact CommandFlops.view_encode s.memory
  unfold ByteAdapterCircuit.view
  rw [memory_eq]
  rcases s with ⟨memory, pending⟩
  cases pending with
  | none => rfl
  | some req =>
    cases req with
    | read signed size address offset =>
      cases signed <;> simp [ByteAdapterCircuit.pending, ByteAdapterCircuit.metaPending,
        ByteAdapterCircuit.storedRequest, ByteAdapterCircuit.metaWrite,
        ByteAdapterCircuit.metaSigned, ByteAdapterCircuit.metaSize,
        ByteAdapterCircuit.metaAddress, ByteAdapterCircuit.metaOffset,
        ByteAdapterInterface.request, encodeRam, ByteAdapterModel.Request.size,
        ByteAdapterModel.Request.address, ByteAdapterModel.Request.offset]
      all_goals rfl
    | store size address offset data =>
      simp [ByteAdapterCircuit.pending, ByteAdapterCircuit.metaPending,
        ByteAdapterCircuit.storedRequest, ByteAdapterCircuit.metaWrite,
        ByteAdapterCircuit.metaSize, ByteAdapterCircuit.metaAddress,
        ByteAdapterCircuit.metaOffset, ByteAdapterCircuit.metaData,
        ByteAdapterInterface.request, encodeRam, ByteAdapterModel.Request.size,
        ByteAdapterModel.Request.address, ByteAdapterModel.Request.offset]
      rfl

def encodeFetch (reply : Option CoreModel.FetchReply) (inactive : Values Fetch) : Values Fetch
  | _, .at ⟨0,_⟩ => BitVec.ofBool reply.isSome
  | _, .at ⟨1,_⟩ => match reply with
    | none => inactive (.at ⟨1,by decide⟩)
    | some .accessFault => 1
    | some (.instruction _) => 0
  | _, .at ⟨2,_⟩ => match reply with
    | none => inactive (.at ⟨2,by decide⟩)
    | some .accessFault => 0
    | some (.instruction value) => value
  | _, .at ⟨k+3,h⟩ => False.elim (by change k+3 < 3 at h; omega)

/-- Canonical active controls, with independently chosen inactive RAM-request
metadata and fetch payload latches. Every logical word and Q are represented. -/
def encode (s : SystemModel.State aw) (ramInactive : Values (ByteAdapterCircuit.Metadata aw))
    (fetchInactive : Values Fetch) : Values (Register aw) :=
  Stream.Joint.values (CoreCircuit.encode s.core)
    (Stream.Joint.values (encodeRam s.ram ramInactive)
      (Stream.Joint.values (MmioCircuit.encode s.mmio) (encodeFetch s.fetch fetchInactive)))

theorem fetchView_encode (s : SystemModel.State aw) (ramInactive : Values (ByteAdapterCircuit.Metadata aw))
    (fetchInactive : Values Fetch) : fetchView (encode s ramInactive fetchInactive) = s.fetch := by
  cases h : s.fetch with
  | none => simp [fetchView, encode, encodeFetch, fetchValid, fetch, h, Stream.Joint.values]
  | some reply => cases reply <;> simp [fetchView, encode, encodeFetch,
      fetchValid, fetchFault, fetchData, fetch, h, Stream.Joint.values]

theorem view_encode (s : SystemModel.State aw) (h : CoreModel.Valid s.core)
    (ramInactive : Values (ByteAdapterCircuit.Metadata aw)) (fetchInactive : Values Fetch) :
    view (encode s ramInactive fetchInactive) = s := by
  change SystemModel.State.mk (CoreCircuit.view (CoreCircuit.encode s.core))
    (ByteAdapterCircuit.view (encodeRam s.ram ramInactive))
    (MmioCircuit.view (MmioCircuit.encode s.mmio)) (fetchView (encode s ramInactive fetchInactive)) = s
  rw [CoreCircuit.view_encode s.core h, view_encodeRam, MmioCircuit.view_encode, fetchView_encode]

theorem valid_encode (layout : AddressMap.Layout rw aw) (rom : SystemModel.Rom rw)
    (s : SystemModel.State aw) (h : SystemModel.Valid layout rom s)
    (ramInactive : Values (ByteAdapterCircuit.Metadata aw)) (fetchInactive : Values Fetch) :
    Valid layout rom (encode s ramInactive fetchInactive) := by
  refine ⟨CoreCircuit.valid_encode s.core h.core, ?_⟩
  rw [view_encode s h.core ramInactive fetchInactive]
  exact h

/-- Logical coverage does not assume a particular ROM program, RAM image, Q,
register contents, or cleared inactive byte/fetch metadata. -/
theorem initial_coverage (layout : AddressMap.Layout rw aw) (rom : SystemModel.Rom rw)
    (s : SystemModel.State aw) (h : SystemModel.Valid layout rom s)
    (ramInactive : Values (ByteAdapterCircuit.Metadata aw)) (fetchInactive : Values Fetch) :
    ∃ raw : Values (Register aw), Valid layout rom raw ∧ view raw = s :=
  ⟨encode s ramInactive fetchInactive, valid_encode layout rom s h ramInactive fetchInactive,
    view_encode s h.core ramInactive fetchInactive⟩

end Pinwheel.Hardware.Processor.SystemCircuit
