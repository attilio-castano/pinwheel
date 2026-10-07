import Pinwheel.Hardware.Memory
import Pinwheel.Hardware.Storage.TwoPort
import Pinwheel.Hardware.Buffered.Reactive

/-! A fetch deadline contract, independent of the source protocol and row format.

A latency-one memory response has already been fixed when a terminal-edge
decision arrives. If the controller feeds that one response directly as the
successor row, two distinct successors cannot both be correct. This statement
allows even the current request to depend on the decision: that request is too
late to change the registered response. It does not exclude another cache,
replicated storage, or a combinational bypass.

In particular this is not a universal two-port lower bound. The current
reactive circuit samples decisions from `stage2`, whose next value is the old
`stage1`. Looking through the current transition may therefore determine the
next edge's required row before that edge. The laws below isolate which
deadline decisions are register-only; they do not construct that controller or
qualify its address path timing.

Reading both successors ahead of the deadline permits selection on the deadline
edge, under an explicitly stable bank. The port order follows the existing
`Storage.TwoPort` policy. These are memory/selection laws, not a refinement of
the buffered reactive controller to an SRAM implementation. -/
namespace Pinwheel.Hardware.Buffered.FetchDeadline
open Pinwheel.Hardware

/-- Select the already identified successor address; `true` is the taken arm. -/
def selectedAddress (decision : Bool) (taken untaken : BitVec a) : BitVec a :=
  if decision then taken else untaken

/-- Two distinct successor rows cannot both be supplied by the same registered
single read response on their decision edge. -/
theorem registered_single_cannot_cover_distinct
    (s : Memory.State a w 1 1) (requests : Bool → Memory.Request a w 1)
    (taken untaken : BitVec a)
    (distinct : s.contents taken ≠ s.contents untaken) :
    ¬ ∀ decision, s.observe (requests decision) 0 =
      s.contents (selectedAddress decision taken untaken) := by
  intro covers
  exact distinct ((covers true).symm.trans
    ((congrFun (Memory.observe_registered s (requests true) (requests false)) 0).trans
      (covers false)))
  done

/-- Port zero carries the untaken arm and port one the taken arm. -/
def selectedPort (decision : Bool) : Fin 2 := if decision then 1 else 0

/-- An immutable executing bank is read at both candidate addresses on the
edge before the decision. The upload write port is disabled in this contract. -/
def dualRequest (taken untaken : BitVec a) : Memory.Request a w 2 :=
  ⟨⟨false, 0, 0⟩, fun port => if port = 0 then untaken else taken⟩

/-- Both responses survive the latency-one boundary. The request made on the
decision edge is unrestricted and has no effect on these responses. -/
theorem dual_prefetch_selects_previous_contents
    (s : Memory.State a w 2 1) (taken untaken : BitVec a)
    (decisionRequest : Memory.Request a w 2) (decision : Bool) :
    ((Memory.spec a w 2 1).step (dualRequest taken untaken) s).observe decisionRequest
      (selectedPort decision) = s.contents (selectedAddress decision taken untaken) :=
  match decision with
  | false => rfl
  | true => rfl

/-- The read-ahead edge leaves the executing bank unchanged. -/
theorem dual_request_preserves_bank (s : Memory.State a w 2 1)
    (taken untaken : BitVec a) :
    (s.step (dualRequest taken untaken)).contents = s.contents :=
  Memory.write_disabled s.contents (dualRequest taken untaken).write rfl

/-- Under the immutable-bank request, the selected prefetched row is also the
row currently stored at that candidate address. -/
theorem dual_prefetch_selects_current_contents
    (s : Memory.State a w 2 1) (taken untaken : BitVec a)
    (decisionRequest : Memory.Request a w 2) (decision : Bool) :
    (s.step (dualRequest taken untaken)).observe decisionRequest (selectedPort decision) =
      (s.step (dualRequest taken untaken)).contents (selectedAddress decision taken untaken) := by
  simpa only [Memory.spec_step, dual_request_preserves_bank] using
    dual_prefetch_selects_previous_contents s taken untaken decisionRequest decision

/-- The port selection convention is precisely the existing two-port policy's
fetched-word convention, independently of commit/start-word handling. -/
theorem existing_two_port_selector (i : Reactive.Inputs) (s : Reactive.State)
    (committing : Bool) (st : Storage.Decoupled.Registers)
    (reads : Fin 2 → BitVec 64) (decision : Bool) :
    (Storage.TwoPort.policy.step i s committing st reads).fetched decision =
      reads (selectedPort decision) := rfl

section ReactiveLookahead
open Pinwheel.Hardware.Buffered.Reactive

/-- Dispatch consumes synchronized register values, not the raw input being
sampled on this edge. This includes WAIT, CHECKED and QUALIFY dispatch. -/
theorem reactive_dispatch_register_only (i j : Values Input) (s : Values Register) :
    dispatch.eval i s = dispatch.eval j s := rfl

/-- The terminal capture forwarded into a branch comes from `stage2`; both
the scratch fallback and absolute endpoint are likewise register-only. -/
theorem reactive_endpoint_register_only (i j : Values Input) (s : Values Register) :
    endpoint.eval i s = endpoint.eval j s := rfl

/-- With START excluded, counted row addressing depends only on the register
state, including branch forwarding and restored loop indices. Reset/cancel
arbitration remains an obligation of any proposed fetch controller. -/
theorem reactive_entry_pc_register_only_without_start
    (i j : Values Input) (s : Values Register)
    (hi : starting.eval i s = 0) (hj : starting.eval j s = 0) :
    entryPC.eval i s = entryPC.eval j s := by
  simp only [entryPC, sequentialPC, Expr.eval, hi, hj]
  rfl
  done

end ReactiveLookahead

end Pinwheel.Hardware.Buffered.FetchDeadline
