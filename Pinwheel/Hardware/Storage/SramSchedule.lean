import Pinwheel.Hardware.Storage.SramAssembly
import Pinwheel.Hardware.Storage.SramExecution

/-! Edge/resource obligations for the existing hybrid assembly. The state and
requests are the actual shared controller/array model, not a second scheduler.
These are digital availability claims; macro timing and wrapper read-back remain
separate. Direct SRAM does not inherit this execution certificate. -/
namespace Pinwheel.Hardware.Storage.SramSchedule
open Pinwheel.Hardware Loader SramExecution

abbrev State := SramExecution.State

def ports (i : Machine.Inputs) (s : State) : Values SramController.Port :=
  SramController.portValues false (s.inputs i) s.values

/-- Both branch candidates are already present at the macro Q pins on a running
edge. There is no minimum-duration assumption on the instruction being left. -/
theorem candidates_ready (s : State) (h : Valid s)
    (hv : s.backend.control.valid = true)
    (hb : Reactive.runningValue s.backend.core = true) (b : Bool) :
    s.q b = FetchPolicy.canonical s.backend.reference.machine s.backend.current b := by
  exact (h.choose_spec.2.2.2.2 hv).1 hb b

/-- The candidate availability contract renews on every edge, including
consecutive one-cycle branches. -/
theorem candidates_after_edge (i : Machine.Inputs) (s : State) (h : Valid s)
    (hv : (next i s).backend.control.valid = true)
    (hb : Reactive.runningValue (next i s).backend.core = true) (b : Bool) :
    (next i s).q b = FetchPolicy.canonical (next i s).backend.reference.machine
      (next i s).backend.current b :=
  candidates_ready (next i s) (valid_next i s h) hv hb b

/-- Exactly one access is enabled at each replicated single-port SRAM.
The actual controller also enables reads during idle nonwrite edges. -/
theorem one_access (direct : Bool) (i : Values SramController.Input)
    (s : Values SramController.Register) :
    (SramController.portValues direct i s .write).toNat +
      (SramController.portValues direct i s .read).toNat = 1 := by
  rw [SramController.read_write_exclusive]
  rcases BitVec.eq_zero_or_eq_one (SramController.portValues direct i s .write) with h | h <;> simp [h]
  done

/-- The response after this edge comes from the address on the actual typed
request port before the edge. Writes hold Q instead of consuming a read port. -/
theorem response_edge (i : Machine.Inputs) (s : State) (b : Bool) :
    (next i s).q b = if (request i s).write.enable then s.q b else
      (s.arrays (if b then 1 else 0)).contents
        ((ports i s (SramAssembly.macroAddress b)).extractLsb' 0 6) := by
  simp only [ports, SramAssembly.macroAddress, SramController.hybrid_port_address]
  cases hw : (request i s).write.enable <;>
    simp_all [request, SramExecution.next, SramExecution.State.q, Memory.Sram.step, Memory.Sram.State.step]
  done

/-- The start value, whether retained or bypassed, belongs to word zero of the
valid active image. This is the same start expression used by emission. -/
theorem start_ready (s : State) (h : Valid s) (hv : s.backend.control.valid = true) :
    s.responses.start = Loader.Store.read
      (s.backend.reference.machine.memory s.backend.control.active) 0 :=
  (h.choose_spec.2.2.2.2 hv).2

/-- Commit marks the response produced on this edge for the immediate start. -/
theorem commit_pending (i : Machine.Inputs) (s : State)
    (hc : Machine.committing (Backend.adapt i s.backend) s.backend.reference.machine = true) :
    (next i s).extra .startPending = 1 := by
  simpa [hc] using pending_next i s

/-- On the very next edge the start input bypasses the newly produced Q0. -/
theorem commit_bypass (i : Machine.Inputs) (s : State)
    (hc : Machine.committing (Backend.adapt i s.backend) s.backend.reference.machine = true) :
    (next i s).responses.start = (next i s).q false := by
  simp [SramExecution.State.responses, Sram.Responses.start, commit_pending i s hc]

/-- The following edge saves that same response for later restarts, even if
the follow-up command is unrelated to execution. -/
theorem commit_saved (i j : Machine.Inputs) (s : State)
    (hc : Machine.committing (Backend.adapt i s.backend) s.backend.reference.machine = true) :
    (next j (next i s)).extra .startWord = (next i s).q false :=
  (start_next j (next i s)).trans (commit_bypass i s hc)

/-- Configuration writes cannot alter any active-bank word in either replica. -/
theorem active_bank_untouched (i : Machine.Inputs) (s : State) (port : Fin 2) (k : BitVec 5) :
    ((next i s).arrays port).contents (Memory.Sram.bankAddress s.backend.control.active k) =
      (s.arrays port).contents (Memory.Sram.bankAddress s.backend.control.active k) :=
  SramController.hybrid_preserves_active i s.backend s.q s.extra s.arrays port k

/-- A write delivers the actual data port to every replica on the same edge. -/
theorem broadcast_write (i : Machine.Inputs) (s : State)
    (hw : (request i s).write.enable = true) (port : Fin 2) :
    ((next i s).arrays port).contents (request i s).write.address = ports i s .data :=
  Memory.Sram.broadcast_write (request i s) s.arrays hw port

/-- The named read-address computation is the actual request address on every
read edge. This includes idle/commit reads, not only running execution. -/
theorem request_on_read (direct : Bool) (i : Values SramController.Input)
    (s : Values SramController.Register) (b : Bool)
    (h : SramController.portValues direct i s .write = 0) :
    SramController.portValues direct i s (.address b) =
      (SramAssembly.computationExpr direct (.readAddress b)).eval i s := by
  simp only [SramController.portValues, SramController.core, Netlist.observe,
    Circuit.observe, SramController.body, SramController.request, Expr.eval,
    Backend.fresh, Expr.eval_bind, WithWire.values] at h ⊢
  simp [h, SramAssembly.computationExpr, SramAssembly.resolve, Expr.eval_bind, Expr.eval]
  congr 1
  funext w p
  cases p <;> rfl
  done

/-- Writes use only the named upload address at either replica. -/
theorem request_on_write (direct : Bool) (i : Values SramController.Input)
    (s : Values SramController.Register) (b : Bool)
    (h : SramController.portValues direct i s .write = 1) :
    SramController.portValues direct i s (.address b) =
      (SramAssembly.computationExpr direct .writeAddress).eval i s := by
  simp only [SramController.portValues, SramController.core, Netlist.observe,
    Circuit.observe, SramController.body, SramController.request, Expr.eval,
    Backend.fresh, Expr.eval_bind, WithWire.values] at h ⊢
  simp [h, SramAssembly.computationExpr]
  done

/-- Running execution is contained in the read-edge envelope used by the
diagnostic. The envelope also includes commit, idle and non-macro uploads. -/
theorem running_reads (i : Machine.Inputs) (s : State)
    (hb : Reactive.runningValue s.backend.core = true) : ports i s .write = 0 := by
  change SramController.portValues false (SramController.inputValues i s.q)
    (SramController.registerValues s.backend s.extra) .write = 0
  rw [SramController.hybrid_port_write]
  have hbusy : Reactive.runningValue s.backend.reference.machine.core = true := hb
  simp [Sram.writing, Loader.push, Loader.enabled, Machine.controlInput, hbusy]
  done

end Pinwheel.Hardware.Storage.SramSchedule
