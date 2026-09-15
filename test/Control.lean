import Pinwheel

open Pinwheel.Engine.Reactive

private def ensure (b : Bool) (message : String) : IO Unit :=
  unless b do throw (IO.userError message)

def main : IO Unit := do
  for n in [:256] do
    let d : Fin 256 := Fin.ofNat 256 n
    let a : Checked := ⟨⟨.openDrain 2, d, none⟩, ⟨1, 1⟩, some ⟨1, 0⟩, .branch 0 1 2⟩
    let p : Program := ⟨Vector.ofFn (fun pc => if pc.val == 0 then .checked a
      else if pc.val == 1 then .action ⟨.openDrain 1, 3, none⟩
      else .action ⟨.openDrain 3, 7, none⟩), {}, 2⟩
    for sampled in [false, true] do
      let mut s := start p (if sampled then 1 else 3)
      for _ in [:n] do
        ensure (step p s true true 0 == reset p) "checked reset priority"
        ensure ((advance p s 0).control == .stopped .fault) "guard ignored before boundary"
        s := advance p s (if sampled then 1 else 3)
        ensure (s.samples[0] == false) "terminal capture ran early"
      let bad := advance p s (if sampled then 2 else 0)
      ensure (bad.control == .stopped .fault && bad.samples == s.samples && bad.pins == p.idle)
        "guard did not precede terminal capture/branch"
      let next := advance p s (if sampled then 3 else 1)
      ensure (next.samples[0] == sampled) "terminal capture used old input"
      ensure (next.control == if sampled then .active 1 3 else .active 2 7)
        "branch did not use newly captured sample"
    let q : Qualify := ⟨{}, ⟨3, 3⟩, d, d⟩
    let p : Program := ⟨Vector.ofFn (fun pc => if pc.val == 0 then .qualify q else .halt), {}, 1⟩
    let mut s := start p 3
    for _ in [:n] do s := advance p s 3
    ensure (s.control == .qualifying 0 0 d) "qualification countdown"
    let blocked := advance p s 1
    if n == 0 then ensure (blocked.control == .stopped .timeout) "qualification budget one"
    else
      ensure (blocked.control == .qualifying 0 d (Fin.ofNat 256 (n - 1))) "qualification did not restart duration"
      s := blocked
      for _ in [:n] do
        s := advance p s 3
        ensure (busy s) "interrupted qualification completed early"
      s := advance p s 3
      ensure (s.control == .stopped .completed) "qualified interval did not complete"
    s := start p 3
    for _ in [:n] do s := advance p s 2
    ensure ((advance p s 2).control == .stopped .timeout) "qualification persistent timeout"
    ensure (step p s true true 3 == reset p) "qualification reset priority"
    ensure (load ⟨p, s⟩ p == (⟨p, s⟩, false)) "busy qualifier accepted reload"
  let a : Checked := ⟨⟨{}, 0, none⟩, ⟨0, 0⟩, some ⟨1, 0⟩, .branch 0 127 1⟩
  let p : Program := ⟨Vector.ofFn (fun pc => if pc.val == 0 then .checked a else .halt), {}, 1⟩
  let bad := advance p (start p 0) 2
  ensure (bad.control == .stopped .fault && bad.samples[0]) "invalid target or terminal-capture ordering"
  ensure ((advance p (start p 0) 0).control == .stopped .completed) "valid branch target"
  ensure ((dispatch p 0 (.jump 1) (Vector.replicate 8 false) 0).control == .stopped .completed) "direct jump"
  for c in [Control.checked 1 0, .qualifying 1 0 0] do
    ensure ((advance p ⟨c, {}, Vector.replicate 8 false⟩ 3).control == .stopped .fault) "malformed control/instruction pair"
  IO.println "Passed 256 checked durations and qualification budgets, terminal capture/branch order, guard/reset priority, interrupted qualification, invalid targets, and malformed control states."
