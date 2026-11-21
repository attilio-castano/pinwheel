import Pinwheel.Hardware.Memory.ByteAdapterCircuit
import Pinwheel.Hardware.Memory.CommandFlopsProofs
import Pinwheel.Hardware.DecodedImplementation

namespace Pinwheel.Hardware.Memory.ByteAdapterCircuit
open ByteAdapterInterface
set_option backward.isDefEq.respectTransparency false

theorem legal_eval (size offset : Expr I R 2) (i : Values I) (s : Values R) :
    (legal size offset).eval i s = match ByteAccess.access (size.eval i s) (offset.eval i s) with
      | .ok _ => 1 | .error _ => 0 := by
  rcases ByteAccess.raw_cases (size.eval i s) with hs | hs | hs | hs
  all_goals rcases ByteAccess.raw_cases (offset.eval i s) with ho | ho | ho | ho
  all_goals simp [legal, Expr.eval, Expr.bor, hs, ho, ByteAccess.access, ByteAccess.decodeSize,
    ByteAccess.Aligned, ByteAccess.Size.bytes]

theorem storeExpr_eval (size offset : Expr I R 2) (word data : Expr I R 32)
    (i : Values I) (s : Values R) (decoded : ByteAccess.Size)
    (h : ByteAccess.access (size.eval i s) (offset.eval i s) = .ok decoded) :
    (storeExpr size offset word data).eval i s =
      ByteAccess.storeCore decoded (offset.eval i s) (word.eval i s) (data.eval i s) := by
  rcases ByteAccess.raw_cases (size.eval i s) with hs | hs | hs | hs
  all_goals rcases ByteAccess.raw_cases (offset.eval i s) with ho | ho | ho | ho
  all_goals cases decoded <;> simp_all [ByteAccess.access, ByteAccess.decodeSize, ByteAccess.Aligned,
    ByteAccess.Size.bytes, storeExpr, select4, Expr.eval, ByteAccess.storeCore,
    ByteAccess.pack, ByteAccess.Touched, ByteAccess.byte]
  all_goals apply BitVec.eq_of_getLsbD_eq
  all_goals intro k hk
  all_goals grind

theorem loadExpr_eval (size offset : Expr I R 2) (signed : Expr I R 1) (word : Expr I R 32)
    (i : Values I) (s : Values R) (decoded : ByteAccess.Size)
    (h : ByteAccess.access (size.eval i s) (offset.eval i s) = .ok decoded) :
    (loadExpr size offset signed word).eval i s =
      ByteAccess.loadCore decoded (signed.eval i s == 1) (offset.eval i s) (word.eval i s) := by
  rcases ByteAccess.raw_cases (size.eval i s) with hs | hs | hs | hs
  all_goals rcases ByteAccess.raw_cases (offset.eval i s) with ho | ho | ho | ho
  all_goals rcases BitVec.eq_zero_or_eq_one (signed.eval i s) with hb | hb
  all_goals cases decoded <;> simp_all [ByteAccess.access, ByteAccess.decodeSize, ByteAccess.Aligned,
    ByteAccess.Size.bytes, loadExpr, selectedByte, select4, Expr.eval, ByteAccess.loadCore,
    ByteAccess.extend, ByteAccess.byte]
  all_goals bv_normalize
  all_goals simp [BitVec.extractLsb'_extractLsb'_of_le (by decide : 7 + 1 ≤ 8),
    BitVec.extractLsb'_extractLsb'_of_le (by decide : 15 + 1 ≤ 16)] at *

@[simp] theorem request_check (wr sg : BitVec 1) (sz : BitVec 2) (addr : BitVec a)
    (off : BitVec 2) (value : BitVec 32) :
    (request wr sg sz addr off value).check = ByteAccess.access sz off := by
  rcases BitVec.eq_zero_or_eq_one wr with h | h <;> simp [request, h, ByteAdapterModel.Request.check,
    ByteAdapterModel.Request.size, ByteAdapterModel.Request.offset]

@[simp] theorem request_address (wr sg : BitVec 1) (sz : BitVec 2) (addr : BitVec a)
    (off : BitVec 2) (value : BitVec 32) : (request wr sg sz addr off value).address = addr := by
  rcases BitVec.eq_zero_or_eq_one wr with h | h <;> simp [request, h, ByteAdapterModel.Request.address]

theorem request_finish (wr sg : BitVec 1) (sz : BitVec 2) (addr : BitVec a)
    (off : BitVec 2) (value q : BitVec 32) :
    (request wr sg sz addr off value).finishCommand q =
      if wr = 1 then match ByteAccess.access sz off with
        | .ok decoded => .write addr (ByteAccess.storeCore decoded off q value)
        | .error _ => .idle
      else .idle := by
  rcases BitVec.eq_zero_or_eq_one wr with h | h <;> cases hc : ByteAccess.access sz off <;>
    simp [ByteAdapterModel.Request.finishCommand, ByteAdapterModel.Request.write,
      ByteAdapterModel.Request.check, ByteAdapterModel.Request.size, ByteAdapterModel.Request.offset, hc, request, h]

theorem decoded_command (i : Values (Input a)) (s : Values (Register a)) :
    CommandInterface.decode (memoryPins i s) = ByteAdapterModel.command (decode i) (view s) := by
  rcases BitVec.eq_zero_or_eq_one (i reset) with hr | hr
  all_goals rcases BitVec.eq_zero_or_eq_one (s pending) with hp | hp
  all_goals rcases BitVec.eq_zero_or_eq_one (i requestValid) with hv | hv
  all_goals rcases BitVec.eq_zero_or_eq_one (i responseReady) with hd | hd
  all_goals rcases BitVec.eq_zero_or_eq_one (s (.right metaWrite)) with hw | hw
  all_goals simp [CommandInterface.decode, memoryPins, memoryInput, sample, commit, accept,
    requestReadyExpr, responseValidExpr, storedLegal, Expr.eval, Expr.bor, legal_eval,
    ByteAdapterModel.command, ByteAdapterModel.Request.beginCommand, decode, view, storedRequest,
    request_finish, hr, hp, hv, hd, hw, memoryValues, CommandFlops.view, CommandFlops.q]
  all_goals cases hi : ByteAccess.access (i size) (i offset)
  all_goals cases hm : ByteAccess.access (s (.right metaSize)) (s (.right metaOffset))
  all_goals simp_all
  all_goals congr 1
  all_goals exact storeExpr_eval _ _ _ _ i s _ hm

theorem memory_step (i : Values (Input a)) (s : Values (Register a)) (r : CommandFlops.Register a 32 b) :
    (circuit a).step i s (.left r) = (CommandFlops.circuit a 32).step (memoryPins i s) (memoryValues s) r :=
  Expr.eval_bind memoryInput (fun r => .reg (.left r)) ((CommandFlops.circuit a 32).next r) i s

theorem memory_view_step (i : Values (Input a)) (s : Values (Register a)) :
    CommandFlops.view (memoryValues ((circuit a).step i s)) =
      SinglePort.step (view s).memory (ByteAdapterModel.command (decode i) (view s)) := by
  have h : (fun {b} (r : CommandFlops.Register a 32 b) => memoryValues ((circuit a).step i s) r) =
      (fun {b} (r : CommandFlops.Register a 32 b) => (CommandFlops.circuit a 32).step (memoryPins i s) (memoryValues s) r) :=
    funext fun b => funext fun r => memory_step i s (b := b) r
  rw [h, CommandFlops.step_view, decoded_command]
  rfl

theorem storedRequest_step (i : Values (Input a)) (s : Values (Register a)) :
    storedRequest ((circuit a).step i s) = if accept.eval i s = 1 then
      request (i write) (i signed) (i size) (i address) (i offset) (i data) else storedRequest s := by
  rcases BitVec.eq_zero_or_eq_one (accept.eval i s) with h | h
  all_goals simp [storedRequest, Circuit.step, circuit, metaWrite, metaSigned, metaSize,
    metaAddress, metaOffset, metaData, metadataNext, Expr.eval, h]

theorem pending_step (i : Values (Input a)) (s : Values (Register a)) :
    (circuit a).step i s pending =
      if i reset = 1 then 0 else if s pending = 1 then
        if i responseReady = 1 then 0 else 1 else i requestValid := by
  change (~~~i reset &&& (if s pending = 1 then ~~~i responseReady else i requestValid)) = _
  rcases BitVec.eq_zero_or_eq_one (i reset) with hr | hr
  all_goals rcases BitVec.eq_zero_or_eq_one (s pending) with hp | hp
  all_goals rcases BitVec.eq_zero_or_eq_one (i responseReady) with hd | hd
  all_goals simp [hr, hp, hd]
  all_goals exact BitVec.allOnes_and

theorem view_step (i : Values (Input a)) (s : Values (Register a)) :
    view ((circuit a).step i s) = ByteAdapterModel.step (decode i) (view s) := by
  unfold view ByteAdapterModel.step
  congr 1
  · exact memory_view_step i s
  · change (if (circuit a).step i s pending = 1 then some (storedRequest ((circuit a).step i s)) else none) = _
    rw [pending_step, storedRequest_step]
    rcases BitVec.eq_zero_or_eq_one (i reset) with hr | hr
    all_goals rcases BitVec.eq_zero_or_eq_one (s pending) with hp | hp
    all_goals rcases BitVec.eq_zero_or_eq_one (i responseReady) with hd | hd
    all_goals rcases BitVec.eq_zero_or_eq_one (i requestValid) with hv | hv
    all_goals simp [decode, accept, requestReadyExpr,
      Expr.eval, hr, hp, hd, hv]

theorem codeExpr_eval (i : Values (Input a)) (s : Values (Register a)) :
    codeExpr.eval i s = code ((storedRequest s).response (view s).memory.q) := by
  rcases BitVec.eq_zero_or_eq_one (s (.right metaWrite)) with hw | hw
  all_goals rcases ByteAccess.raw_cases (s (.right metaSize)) with hs | hs | hs | hs
  all_goals rcases ByteAccess.raw_cases (s (.right metaOffset)) with ho | ho | ho | ho
  all_goals simp [codeExpr, storedLegal, legal_eval, Expr.eval, storedRequest, request,
    ByteAdapterModel.Request.response, ByteAdapterModel.Request.check, ByteAdapterModel.Request.size,
    ByteAdapterModel.Request.offset, ByteAccess.access, ByteAccess.decodeSize, ByteAccess.Aligned,
    ByteAccess.Size.bytes, code, hw, hs, ho]

theorem responseData_eval (i : Values (Input a)) (s : Values (Register a)) :
    (circuit a).observe i s responseData = if i reset = 1 then 0 else if s pending = 1 then
      payload ((storedRequest s).response (view s).memory.q) else 0 := by
  rcases BitVec.eq_zero_or_eq_one (i reset) with hr | hr
  all_goals rcases BitVec.eq_zero_or_eq_one (s pending) with hp | hp
  all_goals rcases BitVec.eq_zero_or_eq_one (s (.right metaWrite)) with hw | hw
  all_goals cases hc : ByteAccess.access (s (.right metaSize)) (s (.right metaOffset))
  all_goals simp [Circuit.observe, circuit, responseData, responseValidExpr, storedLegal,
    Expr.eval, legal_eval, hr, hp, hw, hc, payload, storedRequest, request, ByteAdapterModel.Request.response,
    ByteAdapterModel.Request.check, ByteAdapterModel.Request.size, ByteAdapterModel.Request.offset,
    view, memoryValues, CommandFlops.view, CommandFlops.q]
  all_goals first | rfl | exact loadExpr_eval _ _ _ _ i s _ hc

theorem output_eq (i : Values (Input a)) (s : Values (Register a)) (o : Output b) :
    (circuit a).observe i s o = (ByteAdapterInterface.spec a).observe i (view s) o := by
  cases o with
  | «at» k =>
    match k with
    | ⟨0, _⟩ | ⟨1, _⟩ | ⟨2, _⟩ =>
      all_goals rcases BitVec.eq_zero_or_eq_one (i reset) with hr | hr
      all_goals rcases BitVec.eq_zero_or_eq_one (s pending) with hp | hp
      all_goals simp [Circuit.observe, circuit, requestReadyExpr, responseValidExpr,
        Expr.eval, codeExpr_eval, ByteAdapterInterface.spec, outputValues, ByteAdapterModel.component,
        ByteAdapterModel.machine, Hardware.Stream.Machine.component, ByteAdapterModel.ready,
        ByteAdapterModel.offer, decode, view, hr, hp]
    | ⟨3, _⟩ =>
      change (circuit a).observe i s responseData = _
      rw [responseData_eval]
      rcases BitVec.eq_zero_or_eq_one (i reset) with hr | hr
      all_goals rcases BitVec.eq_zero_or_eq_one (s pending) with hp | hp
      all_goals simp [ByteAdapterInterface.spec, outputValues, ByteAdapterModel.component,
        ByteAdapterModel.machine, Hardware.Stream.Machine.component, ByteAdapterModel.offer, decode, view, hr, hp]
    | ⟨k+4, h⟩ => exact False.elim (by change k+4 < 4 at h; omega)

def implementation (a : Nat) : DecodedImplementation (circuit a) (ByteAdapterInterface.spec a) where
  Valid := fun _ => True
  view := view
  preserved _ _ _ := trivial
  step_eq i s _ := view_step i s
  output_eq i s _ {_} o := output_eq i s o

theorem trace_correct (s : Values (Register a)) (traffic : List (Values (Input a))) :
    (circuit a).component.trace s traffic = (ByteAdapterInterface.spec a).trace (view s) traffic :=
  (implementation a).trace_eq s trivial traffic

theorem run_correct (s : Values (Register a)) (traffic : List (Values (Input a))) :
    view ((circuit a).component.run s traffic) = (ByteAdapterInterface.spec a).run (view s) traffic :=
  (implementation a).run_eq s trivial traffic

theorem reset_view (i : Values (Input a)) (s : Values (Register a)) (hr : i reset = 1) :
    view ((circuit a).step i s) = ByteAdapterModel.resetState (view s) := by
  rw [view_step]
  exact ByteAdapterModel.reset_state (decode i) (view s) (by simp [decode, hr])

theorem reset_memory (i : Values (Input a)) (s : Values (Register a)) (hr : i reset = 1)
    (r : CommandFlops.Register a 32 b) : (circuit a).step i s (.left r) = s (.left r) := by
  rw [memory_step]
  have hc : CommandInterface.decode (memoryPins i s) = .idle := by
    rw [decoded_command]
    simp [ByteAdapterModel.command, decode, hr]
  have h := CommandFlops.encode_view ((CommandFlops.circuit a 32).step (memoryPins i s) (memoryValues s))
  rw [CommandFlops.step_view, hc, SinglePort.idle_holds, CommandFlops.encode_view] at h
  exact congrFun (congrFun h.symm b) r

theorem metadata_hold (i : Values (Input a)) (s : Values (Register a)) (r : Metadata a b)
    (hk : ((metadataPorts a).interface.position r).val ≠ 6) (ha : accept.eval i s = 0) :
    (circuit a).step i s (.right r) = s (.right r) := by
  cases r with
  | «at» k =>
    match k with
    | ⟨0, _⟩ | ⟨1, _⟩ | ⟨2, _⟩ | ⟨3, _⟩ | ⟨4, _⟩ | ⟨5, _⟩ =>
      all_goals simp [Circuit.step, circuit, metadataNext, Expr.eval, ha,
        metaWrite, metaSigned, metaSize, metaAddress, metaOffset, metaData]
    | ⟨6, _⟩ => exact False.elim (hk rfl)
    | ⟨k+7, h⟩ => exact False.elim (by change k+7 < 7 at h; omega)

theorem reset_metadata (i : Values (Input a)) (s : Values (Register a)) (hr : i reset = 1)
    (r : Metadata a b) (hk : ((metadataPorts a).interface.position r).val ≠ 6) :
    (circuit a).step i s (.right r) = s (.right r) :=
  metadata_hold i s r hk (by simp [accept, requestReadyExpr, Expr.eval, hr])

theorem reset_pending (i : Values (Input a)) (s : Values (Register a)) (hr : i reset = 1) :
    (circuit a).step i s pending = 0 := by rw [pending_step]; simp [hr]

theorem reset_outputs (i : Values (Input a)) (s : Values (Register a)) (hr : i reset = 1)
    (o : Output b) : (circuit a).observe i s o = 0 := by
  rw [output_eq]
  cases o with
  | «at» k =>
    match k with
    | ⟨0, _⟩ | ⟨1, _⟩ | ⟨2, _⟩ | ⟨3, _⟩ =>
      all_goals simp [ByteAdapterInterface.spec, ByteAdapterModel.component, ByteAdapterModel.machine,
        Hardware.Stream.Machine.component, decode, hr, outputValues]
      all_goals rfl
    | ⟨k+4, h⟩ => exact False.elim (by change k+4 < 4 at h; omega)

def resetCertificate (a : Nat) : (implementation a).Reset reset where
  initial s := ByteAdapterModel.resetState (view s)
  reset_valid _ _ _ := trivial
  reset_view i s hr := reset_view i s hr

theorem trace_after_reset (i : Values (Input a)) (s : Values (Register a)) (hr : i reset = 1)
    (traffic : List (Values (Input a))) :
    (circuit a).component.trace ((circuit a).step i s) traffic =
      (ByteAdapterInterface.spec a).trace (ByteAdapterModel.resetState (view s)) traffic :=
  (resetCertificate a).trace_after_reset (implementation a) reset i s hr traffic

theorem run_after_reset (i : Values (Input a)) (s : Values (Register a)) (hr : i reset = 1)
    (traffic : List (Values (Input a))) :
    view ((circuit a).component.run ((circuit a).step i s) traffic) =
      (ByteAdapterInterface.spec a).run (ByteAdapterModel.resetState (view s)) traffic :=
  (resetCertificate a).run_after_reset (implementation a) reset i s hr traffic

theorem snapshot_valid_run (s : Values (Register a)) (h : ByteAdapterModel.Valid (view s))
    (traffic : List (Values (Input a))) : ByteAdapterModel.Valid (view ((circuit a).component.run s traffic)) := by
  induction traffic generalizing s with
  | nil => exact h
  | cons i rest ih =>
    apply ih
    change ByteAdapterModel.Valid (view ((circuit a).step i s))
    rw [view_step]
    exact ByteAdapterModel.valid_preserved (decode i) (view s) h

/-- Reset establishes the stronger owned-word snapshot invariant used for byte
preservation; arbitrary raw functional correspondence does not require it. -/
theorem snapshot_valid_after_reset (i : Values (Input a)) (s : Values (Register a)) (hr : i reset = 1)
    (traffic : List (Values (Input a))) :
    ByteAdapterModel.Valid (view ((circuit a).component.run ((circuit a).step i s) traffic)) := by
  apply snapshot_valid_run
  rw [reset_view i s hr]
  exact ByteAdapterModel.reset_valid _

end Pinwheel.Hardware.Memory.ByteAdapterCircuit
