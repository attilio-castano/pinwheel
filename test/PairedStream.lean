import Pinwheel.Hardware.Storage.PairedStream

open Pinwheel.Hardware Pinwheel.Hardware.Storage

/-- An independent command table; it deliberately does not call the supervisor's
arming/rearming/resetting predicates. Nonzero command priority is explicit. -/
private def expected (enabled : Bool) (mode : Nat) (valid pending : Bool)
    (i : Loader.Machine.Inputs) : BitVec 3 × BitVec 64 × Bool :=
  if i.command == 6 && i.data == 0 then (7,i.data,false)
  else if i.init || i.reset || i.command == 7 then (i.command,i.data,false)
  else if i.command == 6 && i.data == 1 && !enabled && valid && !pending &&
      (mode == 0 || mode == 5 || mode == 6 || mode == 7) then (5,0,true)
  else if i.command == 0 && enabled && valid && !pending && mode == 5 then (5,0,true)
  else (if enabled && i.command != 0 then 6 else i.command,
    i.data, enabled && mode != 6 && mode != 7)

private def snapshot (enabled : Bool) (mode : Nat) (valid pending : Bool) :
    Values PairedStream.Register
  | _, .extra .enabled => BitVec.ofBool enabled
  | _, .inner .mode => BitVec.ofNat 3 mode
  | _, .inner .valid => BitVec.ofBool valid
  | _, .inner .pending => BitVec.ofBool pending
  | _, .inner .current => 4
  | _, .inner .samples => 0xa653
  | _, .inner (.parameter b k) => BitVec.ofNat 20 (37 + 19*k.toNat + if b then 1024 else 0)
  | _, .inner (.boot b) => if b then 7 else 4
  | _, .inner (.idle _) => 0x3f
  | _, _ => 0

private def inputs (i : Loader.Machine.Inputs) : Values PairedStream.Input
  | _, .base p => i.values p
  | _, .q b => if b then 0xfedcba9876543210 else 0x0123456789abcdef

private def assert (name : String) (ok : Bool) : IO Unit :=
  unless ok do throw (IO.userError name)

private def policyTable : IO Nat := do
  let mut count := 0
  for mode in [:8] do
    for command in [:8] do
      for data in ([0,1,2,0x100000001,0xffffffffffffffff] : List (BitVec 64)) do
        for enabled in [false,true] do
          for valid in [false,true] do
            for pending in [false,true] do
              for init in [false,true] do
                for reset in [false,true] do
                  let i : Loader.Machine.Inputs :=
                    {init,reset,command := BitVec.ofNat 3 command,data,incoming := 2}
                  let result := PairedStream.step ⟨enabled⟩
                    ⟨BitVec.ofNat 3 mode,valid,pending⟩ i
                  let (ec,ed,ee) := expected enabled mode valid pending i
                  let description := s!"policy mode={mode} command={command} data={data.toNat} " ++
                    s!"enabled={enabled} valid={valid} pending={pending} init={init} reset={reset}"
                  assert description (result.effective.command == ec && result.effective.data == ed &&
                    result.state.enabled == ee && result.effective.init == init &&
                    result.effective.reset == reset && result.effective.incoming == 2)
                  let s : Values PairedStream.Register := snapshot enabled mode valid pending
                  let raw : Values PairedStream.Input := inputs i
                  for ⟨_,p⟩ in PairedController.inputs Loader.Machine.inputs do
                    assert (description ++ "; input expression")
                      ((PairedStream.inputExpr p).eval raw s == PairedStream.effectiveInputs raw s p)
                  assert (description ++ "; next enabled expression")
                    ((PairedStream.nextExpr .enabled).eval raw s == BitVec.ofBool ee)
                  count := count + 1
  return count

private def circuitLifecycle (n : Netlist PairedStream.Register PairedStream.Output PairedStream.Input) :
    IO Unit := do
  let stopped : Values PairedStream.Register := snapshot true 5 true false
  for command in ([1,2,3,4,5,6] : List (BitVec 3)) do
    let input : Values PairedStream.Input := inputs {command,data := 1}
    let next : Values PairedStream.Register := n.step input stopped
    assert "Reserved engine forwarded a loader write" (n.observe input stopped (.port .write) == 0)
    assert "Reserved engine failed to reject a real command"
      (n.observe input stopped (.base (.control .rejected)) == 1)
    for ⟨w,r⟩ in PairedController.registers do
      match w, r with
      | _, .parameter _ _ | _, .boot _ | _, .idle _ | _, .active | _, .valid | _, .pending | _, .cursor =>
          assert "Reservation changed upload state" (next (.inner r) == stopped (.inner r))
      | _, _ => pure ()
    assert "Real command unexpectedly auto-rearmed"
      (n.observe input stopped (.base (.control .start)) == 0)
  let quiet : Values PairedStream.Input := inputs {data := 0xfeed}
  assert "Completion did not auto-rearm" (n.observe quiet stopped (.base (.control .start)) == 1)
  assert "Auto-rearm retained a command payload" (n.step quiet stopped (.inner .payload) == 0)
  assert "Auto-rearm disabled its session" (n.step quiet stopped (.extra .enabled) == 1)
  let disabled : Values PairedStream.Register := snapshot false 0 true false
  let arm : Values PairedStream.Input := inputs {command := 6,data := 1}
  assert "Enable failed to start immediately" (n.observe arm disabled (.base (.control .start)) == 1)
  assert "Enable failed to retain ownership" (n.step arm disabled (.extra .enabled) == 1)
  let oneshot : Values PairedStream.Input := inputs {command := 5,data := 0xab}
  assert "Default one-shot no longer starts" (n.observe oneshot disabled (.base (.control .start)) == 1)
  assert "Default one-shot payload changed" (n.step oneshot disabled (.inner .payload) == 0xab)
  assert "Default one-shot acquired stream ownership" (n.step oneshot disabled (.extra .enabled) == 0)
  for mode in [0,1,2,3,4,5,6,7] do
    let s : Values PairedStream.Register := snapshot true mode true false
    let stop : Values PairedStream.Input := inputs {command := 6,data := 0}
    assert "Stop failed to abort execution" (n.step stop s (.inner .mode) == 0)
    assert "Stop failed to disarm" (n.step stop s (.extra .enabled) == 0)
    assert "Stop cleared committed validity" (n.step stop s (.inner .valid) == 1)
    assert "Stop was rejected" (n.observe stop s (.base (.control .rejected)) == 0)
  for mode in [6,7] do
    let s : Values PairedStream.Register := snapshot true mode true false
    assert "Terminal error retained ownership" (n.step quiet s (.extra .enabled) == 0)
    assert "Terminal error retried" (n.observe quiet s (.base (.control .start)) == 0)

private def overlayPages : IO Unit := do
  let raw : Values (SramController.Out Chip.Output) := fun _ => 0
  for enabled in [false,true] do
    for page in [:4] do
      for byte in [:256] do
        let s : Values PairedStream.FullRegister := fun {w} r => match w, r with
          | _, .extra .pageSecond => BitVec.ofNat 2 page
          | _, .inner (.inner (.inner (.inner (.extra .enabled)))) => BitVec.ofBool enabled
          | _, _ => 0
        let o : Values (SramController.Out Chip.Output) := fun {w} p => match w, p with
          | _, .base .uoOut => BitVec.ofNat 8 byte
          | _, p => raw p
        let shown := PairedStream.overlay s o
        let expectedByte := if enabled && page == 3 then (BitVec.ofNat 8 byte) ||| 8 else
          BitVec.ofNat 8 byte
        assert "Status overlay changed a different bit or page" (shown (.base .uoOut) == expectedByte)
        assert "Status overlay changed protocol outputs" (shown (.base .uioOut) == o (.base .uioOut))
        assert "Status overlay changed protocol ownership" (shown (.base .uioOe) == o (.base .uioOe))

def main : IO Unit := do
  let count ← policyTable
  match PairedStream.core with
  | .error e => throw (IO.userError e)
  | .ok n => circuitLifecycle n
  overlayPages
  assert "Unexpected stream core register count" (PairedStream.registers.size == 82)
  assert "Unexpected stream package register count" (PairedStream.fullRegisters.size == 111)
  IO.println s!"Paired stream: {count} policy cases, typed expressions, reservation, start/rearm/stop/error lifecycle and 2048 page overlays passed"
