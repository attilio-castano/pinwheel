import Pinwheel.Hardware.Switch.Circuit

namespace Pinwheel.Hardware.Switch.Structural

open Physical
set_option backward.isDefEq.respectTransparency false

@[simp] theorem fifo_encode (e : DestinationEncoding (m+1))
    (s : Switch.State n (m+1) (BitVec w)) (k : Fin (n+1)) (r : Stream.CellReg (e.width+w) depth b) :
    encode e s (fifoReg k r) = PacketEncoding.cells e (s.queues k) r := rfl
@[simp] theorem slot_encode (e : DestinationEncoding (m+1))
    (s : Switch.State n (m+1) (BitVec w)) (o : Fin (m+1)) (r : Stream.CellReg w 1 b) :
    (encode e s : Values (Register n m e.width w depth)) (slotReg o r) = Stream.cells (slotValue s o).toList r := rfl
@[simp] theorem cursor_encode (e : DestinationEncoding (m+1))
    (s : Switch.State n (m+1) (BitVec w)) (o : Fin (m+1)) (k : Fin (n+1)) :
    (encode e s : Values (Register n m e.width w depth)) (cursorReg o k) = BitVec.ofBool (k == s.cursor o) := rfl

theorem headValid_eval (e : DestinationEncoding (m+1)) (s : Switch.State n (m+1) (BitVec w))
    (hs : Switch.Valid depth s) (i : Values (In n m e.width w)) (k : Fin (n+1)) :
    (headValid e.width w depth k).eval i (encode e s) = BitVec.ofBool (s.queues k).head?.isSome := by
  simp only [headValid, Expr.eval_bind, Expr.eval, fifo_encode]
  exact PacketEncoding.head_valid e (s.queues k) (hs.1 k) i

theorem headData_eval (e : DestinationEncoding (m+1)) (s : Switch.State n (m+1) (BitVec w))
    (hs : Switch.Valid depth s) (i : Values (In n m e.width w)) (k : Fin (n+1)) :
    (headData e.width w depth k).eval i (encode e s) = PacketEncoding.head e (s.queues k) := by
  simp only [headData, Expr.eval_bind, Expr.eval, fifo_encode]
  exact PacketEncoding.cell_head e (s.queues k) (hs.1 k) i

theorem headPayload_eval (e : DestinationEncoding (m+1)) (s : Switch.State n (m+1) (BitVec w))
    (hs : Switch.Valid depth s) (i : Values (In n m e.width w)) (k : Fin (n+1)) :
    (headPayload e.width w depth k).eval i (encode e s) = ((s.queues k).head?.map Packet.payload).getD 0 := by
  simp only [headPayload, Expr.eval, headData_eval e s hs]
  exact PacketEncoding.head_payload e (s.queues k)

theorem request_eval (e : DestinationEncoding (m+1)) (s : Switch.State n (m+1) (BitVec w))
    (hs : Switch.Valid depth s) (i : Values (In n m e.width w)) (o : Fin (m+1)) (k : Fin (n+1)) :
    (request e w depth o k).eval i (encode e s) = BitVec.ofBool (Switch.request s o k) := by
  simp only [request, Expr.eval, headValid_eval e s hs, headData_eval e s hs, BitVec.ofBool_and_ofBool]
  congr 1
  exact PacketEncoding.head_matches e (s.queues k) o

theorem canLoad_eval (e : DestinationEncoding (m+1)) (s : Switch.State n (m+1) (BitVec w))
    (i : Values (In n m e.width w)) (o : Fin (m+1)) :
    (canLoad e.width w depth o).eval i (encode e s) = BitVec.ofBool (Switch.canLoad (decode (readPins i)) s o) := by
  have hv : Stream.cells (slotValue s o).toList (.valid (0 : Fin 1)) = BitVec.ofBool (slotValue s o).isSome := by
    cases slotValue s o <;> rfl
  simp only [canLoad, Stream.eval_bor, Expr.eval, slot_encode, hv]
  rw [← Arbitration.RoundRobinCircuit.bit_roundtrip (i (outReady o)),
    BitVec.not_ofBool, BitVec.ofBool_or_ofBool]
  congr 1
  change (!(slotValue s o).isSome || (i (outReady o) == 1)) = _
  cases h : s.slots o <;> simp only [slotValue, h, Option.map_none, Option.map_some,
    Option.isSome_none, Option.isSome_some, Switch.canLoad, decode, readPins,
    Option.isNone_none, Option.isNone_some, Bool.not_false, Bool.not_true]


theorem selection_eval (e : DestinationEncoding (m+1)) (s : Switch.State n (m+1) (BitVec w))
    (hs : Switch.Valid depth s) (i : Values (In n m e.width w)) (o : Fin (m+1))
    (value : Fin (n+1) → Wire n m e.width w depth b) (fallback : Wire n m e.width w depth b) :
    (selection e w depth o value fallback).eval i (encode e s) =
      match Arbitration.RoundRobin.grant (s.cursor o) (Switch.request s o) with
      | none => fallback.eval i (encode e s)
      | some k => (value k).eval i (encode e s) := by
  exact Arbitration.RoundRobinMasked.selection_eval _ _ _ _ (s.cursor o) (Switch.request s o)
    i (encode e s) (fun _ => rfl) (request_eval e s hs i o)


theorem grantBit_eval (e : DestinationEncoding (m+1)) (s : Switch.State n (m+1) (BitVec w))
    (hs : Switch.Valid depth s) (i : Values (In n m e.width w)) (o : Fin (m+1)) (k : Fin (n+1)) :
    (grantBit e w depth o k).eval i (encode e s) =
      BitVec.ofBool (Switch.grant (decode (readPins i)) s o == some k) := by
  simp only [grantBit, gated, Expr.eval, canLoad_eval, selection_eval e s hs]
  cases hr : (decode (readPins i)).reset <;> cases hc : Switch.canLoad (decode (readPins i)) s o <;>
    cases hg : Arbitration.RoundRobin.grant (s.cursor o) (Switch.request s o) <;>
    simp_all [Switch.grant, decode, readPins]

theorem anyWire_eval (bits : α → Expr I R 1) (xs : List α) (i : Values I) (s : Values R)
    (f : α → Bool) (hf : ∀ x, (bits x).eval i s = BitVec.ofBool (f x)) :
    (anyWire bits xs).eval i s = BitVec.ofBool (xs.any f) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change ((bits x).bor (anyWire bits xs)).eval i s = _
    simp [hf, ih]

theorem pulled_eval (e : DestinationEncoding (m+1)) (s : Switch.State n (m+1) (BitVec w))
    (hs : Switch.Valid depth s) (i : Values (In n m e.width w)) (k : Fin (n+1)) :
    (pulled e w depth k).eval i (encode e s) = BitVec.ofBool (Switch.pulled (decode (readPins i)) s k) :=
  anyWire_eval _ _ _ _ _ (fun o => grantBit_eval e s hs i o k)

theorem legal_eval (e : DestinationEncoding (m+1)) (i : Values (In n m e.width w))
    (s : Values (Register n m e.width w depth)) (k : Fin (n+1)) :
    (legal e w depth k).eval i s = BitVec.ofBool (decide ((i (inDestination k)).toNat < m+1)) := by
  simp only [legal, Expr.eval, encodeDestination_toNat, BitVec.not_ofBool]
  congr 1
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq]
  omega

theorem admitted_eval (e : DestinationEncoding (m+1)) (i : Values (In n m e.width w))
    (s : Values (Register n m e.width w depth)) (k : Fin (n+1)) :
    (admitted e w depth k).eval i s = BitVec.ofBool ((decode (readPins i)).offered k).isSome := by
  simp only [admitted, Expr.eval, legal_eval]
  rw [← Arbitration.RoundRobinCircuit.bit_roundtrip (i (inValid k)), BitVec.ofBool_and_ofBool]
  by_cases hv : i (inValid k) = 1 <;>
    simp only [decode, readPins, hv, if_true, if_false, PacketEncoding.decode_raw_isSome,
      Option.isSome_none, beq_self_eq_true, Bool.true_and, BitVec.ofBool_false]
  · have hb : (i (inValid k) == 1) = false := by exact beq_eq_false_iff_ne.mpr hv
    simp only [hb, Bool.false_and, BitVec.ofBool_false]

theorem admissible_eval (e : DestinationEncoding (m+1)) (i : Values (In n m e.width w))
    (s : Values (Register n m e.width w depth)) (k : Fin (n+1)) :
    (admissible e w depth k).eval i s = BitVec.ofBool (Physical.admissible (readPins i) k) := by
  simp only [admissible, Stream.eval_bor, Expr.eval, legal_eval]
  rw [← Arbitration.RoundRobinCircuit.bit_roundtrip (i (inValid k)),
    BitVec.not_ofBool, BitVec.ofBool_or_ofBool]
  rfl

theorem offered_pack (e : DestinationEncoding (m+1)) (i : Values (In n m e.width w)) (k : Fin (n+1)) :
    ((decode (readPins i)).offered k).map (PacketEncoding.pack e) =
      if i (inValid k) = 1 then
        if (i (inDestination k)).toNat < m+1 then some (i (inDestination k) ++ i (inPayload k)) else none
      else none := by
  simp only [decode, readPins]
  split <;> simp [PacketEncoding.decode_raw_pack]

theorem fifoInput_eval (e : DestinationEncoding (m+1)) (s : Switch.State n (m+1) (BitVec w))
    (hs : Switch.Valid depth s) (i : Values (In n m e.width w)) (k : Fin (n+1)) :
    (fun {b} (p : Stream.In (e.width+w) b) => (fifoInput e w depth k p).eval i (encode e s)) =
      @Stream.inputValues _ (Stream.mapInput (PacketEncoding.pack e) (Switch.queueInput (decode (readPins i)) s k)) := by
  funext b p
  cases p with
  | «at» p => match p with
    | ⟨0, _⟩ => exact (Arbitration.RoundRobinCircuit.bit_roundtrip (i reset)).symm
    | ⟨1, _⟩ => simpa only [fifoInput, Stream.inputExpr, Stream.inputValues, Stream.mapInput, Switch.queueInput, Option.isSome_map]
        using admitted_eval e i (encode e s) k
    | ⟨2, _⟩ => exact pulled_eval e s hs i k
    | ⟨3, _⟩ =>
      change (if (admitted e w depth k).eval i (encode e s) = 1 then
        i (inDestination k) ++ i (inPayload k) else 0) =
        (((decode (readPins i)).offered k).map (PacketEncoding.pack e)).getD 0
      rw [admitted_eval, offered_pack]
      by_cases hv : i (inValid k) = 1 <;> by_cases hd : (i (inDestination k)).toNat < m+1 <;>
        simp only [decode, readPins, hv, hd, if_true, if_false, PacketEncoding.decode_raw_isSome,
          Option.isSome_none, decide_true, decide_false, BitVec.ofBool_false, BitVec.ofBool_true,
          Option.getD_some, Option.getD_none]
      all_goals simp
    | ⟨p+4, h⟩ => exact False.elim (by change p+4<4 at h; omega)

theorem selected_isSome (i : Switch.Input n m α) (s : Switch.State n m α) (o : Fin m) :
    (Switch.selectedDelivery i s o).isSome = (Switch.grant i s o).isSome := by
  cases hg : Switch.grant i s o with
  | none => simp [Switch.selectedDelivery, hg]
  | some k =>
    obtain ⟨p, hp, _⟩ := Switch.requested_head s o k (Switch.grant_requested i s o k hg)
    simp [Switch.selectedDelivery, hg, hp]

theorem gated_selection_eval (e : DestinationEncoding (m+1)) (s : Switch.State n (m+1) (BitVec w))
    (hs : Switch.Valid depth s) (i : Values (In n m e.width w)) (o : Fin (m+1))
    (value : Fin (n+1) → Wire n m e.width w depth b) :
    (gated e.width w depth o (selection e w depth o value (.lit 0))).eval i (encode e s) =
      match Switch.grant (decode (readPins i)) s o with
      | none => 0
      | some k => (value k).eval i (encode e s) := by
  simp only [gated, Expr.eval, canLoad_eval, selection_eval e s hs]
  cases hr : (decode (readPins i)).reset <;> cases hc : Switch.canLoad (decode (readPins i)) s o <;>
    cases hg : Arbitration.RoundRobin.grant (s.cursor o) (Switch.request s o) <;>
    simp_all [Switch.grant, decode, readPins]

theorem grantAny_eval (e : DestinationEncoding (m+1)) (s : Switch.State n (m+1) (BitVec w))
    (hs : Switch.Valid depth s) (i : Values (In n m e.width w)) (o : Fin (m+1)) :
    (grantAny e w depth o).eval i (encode e s) =
      BitVec.ofBool (Switch.selectedDelivery (decode (readPins i)) s o).isSome := by
  rw [grantAny, gated_selection_eval e s hs, selected_isSome]
  cases Switch.grant (decode (readPins i)) s o <;> rfl

theorem selectedPayload_eval (e : DestinationEncoding (m+1)) (s : Switch.State n (m+1) (BitVec w))
    (hs : Switch.Valid depth s) (i : Values (In n m e.width w)) (o : Fin (m+1)) :
    (selectedPayload e w depth o).eval i (encode e s) =
      ((Switch.selectedDelivery (decode (readPins i)) s o).map (fun d => d.packet.payload)).getD 0 := by
  rw [selectedPayload, gated_selection_eval e s hs]
  cases hg : Switch.grant (decode (readPins i)) s o with
  | none => simp [Switch.selectedDelivery, hg]
  | some k =>
    simp only [Switch.selectedDelivery, hg, Option.bind_some, headPayload_eval e s hs, Option.map_map, Function.comp_def]

theorem slotInput_eval (e : DestinationEncoding (m+1)) (s : Switch.State n (m+1) (BitVec w))
    (hs : Switch.Valid depth s) (i : Values (In n m e.width w)) (o : Fin (m+1)) :
    (fun {b} (p : Stream.In w b) => (slotInput e w depth o p).eval i (encode e s)) =
      @Stream.inputValues _ (Stream.mapInput (fun d => d.packet.payload) (Switch.slotInput (decode (readPins i)) s o)) := by
  funext b p
  cases p with
  | «at» p => match p with
    | ⟨0, _⟩ => exact (Arbitration.RoundRobinCircuit.bit_roundtrip (i reset)).symm
    | ⟨1, _⟩ => simpa only [slotInput, Stream.inputExpr, Stream.inputValues, Stream.mapInput, Switch.slotInput, Option.isSome_map]
        using grantAny_eval e s hs i o
    | ⟨2, _⟩ => exact (Arbitration.RoundRobinCircuit.bit_roundtrip (i (outReady o))).symm
    | ⟨3, _⟩ => exact selectedPayload_eval e s hs i o
    | ⟨p+4, h⟩ => exact False.elim (by change p+4<4 at h; omega)

theorem cursorNext_eval (e : DestinationEncoding (m+1)) (s : Switch.State n (m+1) (BitVec w))
    (hs : Switch.Valid depth s) (i : Values (In n m e.width w)) (o : Fin (m+1)) (k : Fin (n+1)) :
    (cursorNext e w depth o k).eval i (encode e s) =
      BitVec.ofBool (k == (Switch.step depth (decode (readPins i)) s).cursor o) := by
  simp only [cursorNext, Expr.eval, canLoad_eval, selection_eval e s hs, cursor_encode]
  cases hr : (decode (readPins i)).reset <;> cases hc : Switch.canLoad (decode (readPins i)) s o <;>
    cases hg : Arbitration.RoundRobin.grant (s.cursor o) (Switch.request s o) <;>
    simp_all [Switch.step, Switch.grant, decode, readPins]

theorem slotValue_step (i : Switch.Input n (m+1) (BitVec w)) (s : Switch.State n (m+1) (BitVec w))
    (o : Fin (m+1)) :
    (Stream.elastic id).step (Stream.mapInput (fun d => d.packet.payload) (Switch.slotInput i s o)) (slotValue s o) =
      slotValue (Switch.step depth i s) o := by
  cases hr : i.reset <;> cases hd : i.ready o <;> cases hs : s.slots o <;>
    simp [Stream.elastic, Stream.mapInput, Switch.slotInput, slotValue, Switch.step, hr, hd, hs]

theorem step_eq (e : DestinationEncoding (m+1)) (s : Switch.State n (m+1) (BitVec w))
    (hs : Switch.Valid depth s) (i : Values (In n m e.width w)) (r : Register n m e.width w depth b) :
    (circuit e n w depth).step i (encode e s) r =
      encode e (Switch.step depth (decode (readPins i)) s) r := by
  cases r with
  | left r => cases r with
    | «at» k r =>
      simp only [Circuit.step, circuit, Expr.eval_bind, fifoInput_eval e s hs, Expr.eval, fifo_encode]
      exact PacketEncoding.fifo_step e (Switch.queueInput (decode (readPins i)) s k) (s.queues k) (hs.1 k) r
  | right r => cases r with
    | left r => cases r with
      | «at» o r =>
        simp only [Circuit.step, circuit, Expr.eval_bind, slotInput_eval e s hs, Expr.eval, slot_encode]
        rw [show ((Stream.Elastic.circuit (Stream.Map.identity w)).next r).eval
            (Stream.inputValues (Stream.mapInput (fun d => d.packet.payload) (Switch.slotInput (decode (readPins i)) s o)))
            (Stream.cells (slotValue s o).toList) = _ from Stream.Elastic.step_eq (Stream.Map.identity w) _ _ r]
        rw [show (Stream.Map.identity w).function = id from rfl, slotValue_step]
        rfl
    | right r => cases r with
      | «at» o r => cases r with
        | «at» k => exact cursorNext_eval e s hs i o k

theorem output_eq (e : DestinationEncoding (m+1)) (s : Switch.State n (m+1) (BitVec w))
    (hs : Switch.Valid depth s) (hd : 0 < depth) (i : Values (In n m e.width w)) (p : Out n m w b) :
    (circuit e n w depth).observe i (encode e s) p = Physical.observe depth (readPins i) s p := by
  cases p with
  | left p => cases p with
    | «at» k =>
      simp only [Circuit.observe, circuit, Expr.eval, admissible_eval, Expr.eval_bind,
        fifoInput_eval e s hs, fifo_encode]
      rw [show ((Stream.Fifo.circuit (e.width+w) depth).output Stream.inReady).eval
          (Stream.inputValues (Stream.mapInput (PacketEncoding.pack e) (Switch.queueInput (decode (readPins i)) s k)))
          (PacketEncoding.cells e (s.queues k)) = _ from
        PacketEncoding.fifo_output e (Switch.queueInput (decode (readPins i)) s k) (s.queues k) (hs.1 k) hd Stream.inReady]
      dsimp only [Stream.outputValues, Stream.inReady, Stream.outputPorts, lanePorts]
      rw [BitVec.ofBool_and_ofBool]
      cases hr : (decode (readPins i)).reset <;>
        simp [Physical.observe, Switch.observe, Stream.Machine.component, Switch.queueInput, hr, Bool.and_comm]
  | right p => cases p with
    | left p => cases p with
      | «at» o =>
        simp only [Circuit.observe, circuit, Expr.eval_bind, slotInput_eval e s hs, Expr.eval, slot_encode]
        rw [show ((Stream.Elastic.circuit (Stream.Map.identity w)).output Stream.outValid).eval
            (Stream.inputValues (Stream.mapInput (fun d => d.packet.payload) (Switch.slotInput (decode (readPins i)) s o)))
            (Stream.cells (slotValue s o).toList) = _ from Stream.Elastic.output_eq (Stream.Map.identity w) _ _ Stream.outValid]
        cases hr : (decode (readPins i)).reset <;> cases hslot : s.slots o <;>
          simp [Stream.outputValues, Stream.outValid, Stream.Machine.component, Stream.elastic, Stream.mapInput,
            Switch.slotInput, slotValue, Physical.observe, Switch.observe, lanePorts, hr, hslot]
    | right p => cases p with
      | «at» o =>
        simp only [Circuit.observe, circuit, Expr.eval_bind, slotInput_eval e s hs, Expr.eval, slot_encode]
        rw [show ((Stream.Elastic.circuit (Stream.Map.identity w)).output Stream.outData).eval
            (Stream.inputValues (Stream.mapInput (fun d => d.packet.payload) (Switch.slotInput (decode (readPins i)) s o)))
            (Stream.cells (slotValue s o).toList) = _ from Stream.Elastic.output_eq (Stream.Map.identity w) _ _ Stream.outData]
        cases hr : (decode (readPins i)).reset <;> cases hslot : s.slots o <;>
          simp [Stream.outputValues, Stream.outData, Stream.Machine.component, Stream.elastic, Stream.mapInput,
            Switch.slotInput, slotValue, Physical.observe, Switch.observe, lanePorts, hr, hslot]

theorem reset_eq (e : DestinationEncoding (m+1)) (i : Values (In n m e.width w))
    (s : Values (Register n m e.width w depth)) (hr : i reset = 1) (r : Register n m e.width w depth b) :
    (circuit e n w depth).step i s r = encode e Switch.initial r := by
  cases r with
  | left r => cases r with
    | «at» k r => cases r <;>
      simp [Circuit.step, circuit, Expr.eval_bind, Stream.Fifo.circuit, Expr.eval, fifoInput,
        Stream.inputExpr, Stream.reset, hr, encode, PacketEncoding.cells, Switch.initial, Stream.cells]
  | right r => cases r with
    | left r => cases r with
      | «at» o r => cases r <;>
        simp [Circuit.step, circuit, Expr.eval_bind, Stream.Elastic.circuit, Expr.eval, slotInput,
          Stream.inputExpr, Stream.reset, hr, encode, slotValue, Switch.initial, Stream.cells]
    | right r => cases r with
      | «at» o r => cases r with
        | «at» k => simp [Circuit.step, circuit, cursorNext, Expr.eval, hr, encode, Switch.initial]

end Pinwheel.Hardware.Switch.Structural
