import Lean
import Pinwheel.Hardware.Readback.Mux
open Lean Elab Pinwheel.Hardware
namespace HardwareReadbackMuxTests
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
theorem full_priority_selector (x0 : BitVec 1) (x1 : BitVec 1) (x2 : BitVec 1) (x3 : BitVec 1) (x4 : BitVec 1) (x5 : BitVec 5) (x6 : BitVec 1) (x7 : BitVec 1) (x8 : BitVec 1) (x9 : BitVec 1) (x10 : BitVec 1) (x11 : BitVec 1) (x12 : BitVec 1) (x13 : BitVec 1) (x14 : BitVec 1) (x15 : BitVec 1) (x16 : BitVec 1) (x17 : BitVec 1) (x18 : BitVec 1) (x19 : BitVec 1) (x20 : BitVec 1) (x21 : BitVec 1) (x22 : BitVec 1) (x23 : BitVec 1) (x24 : BitVec 1) (x25 : BitVec 1) (x26 : BitVec 1) (x27 : BitVec 1) (x28 : BitVec 1) (x29 : BitVec 1) (x30 : BitVec 1) (x31 : BitVec 1) (x32 : BitVec 1) (x33 : BitVec 1) (x34 : BitVec 1) (x35 : BitVec 1) (x36 : BitVec 32) :
    (if x0 = 1 then (0#5) else (if x1 = 1 then (0#5) else (if x2 = 1 then (0#5) else (if (x3 &&& x4) = 1 then x5 else (if x6 = 1 then x5 else (if x7 = 1 then x5 else (if x8 = 1 then x5 else (if x9 = 1 then x5 else (if x10 = 1 then x5 else (if x11 = 1 then x5 else (if x12 = 1 then x5 else (if (x13 &&& x14) = 1 then x5 else (if x15 = 1 then x5 else (if x16 = 1 then x5 else (if x17 = 1 then x5 else (if (x18 &&& x4) = 1 then x5 else (if x19 = 1 then x5 else (if (x18 &&& x20) = 1 then x5 else (if x21 = 1 then x5 else (if x22 = 1 then x5 else (if (x23 &&& x24) = 1 then x5 else (if x25 = 1 then x5 else (if x26 = 1 then x5 else (if (x23 &&& x27) = 1 then x5 else (if (x23 &&& (x14 &&& x28)) = 1 then x5 else (if (x23 &&& (x29 &&& x28)) = 1 then x5 else (if (x23 &&& x30) = 1 then x5 else (if (x31 &&& (x4 &&& x28)) = 1 then x5 else (if (x31 &&& (x4 &&& x32)) = 1 then x5 else (if (x31 &&& (x14 &&& x28)) = 1 then x5 else (if (x31 &&& (x20 &&& x28)) = 1 then x5 else (if (x31 &&& (x24 &&& x28)) = 1 then x5 else (if (x31 &&& (x33 &&& x28)) = 1 then x5 else (if (x31 &&& (x29 &&& x28)) = 1 then x5 else (if (x31 &&& x30) = 1 then x5 else (if (x31 &&& (x34 &&& x28)) = 1 then x5 else (if (x31 &&& (x27 &&& x28)) = 1 then x5 else (if x35 = 1 then x5 else (if (BitVec.ofBool (decide (x36 = (115#32)))) = 1 then (0#5) else (if (BitVec.ofBool (decide (x36 = (1048691#32)))) = 1 then (0#5) else (0#5))))))))))))))))))))))))))))))))))))))))) = (if (((x0 ||| x1) ||| x2) ||| (~~~(((((((((((((((((((((((((((((((((((x3 &&& x4) ||| x6) ||| x7) ||| x8) ||| x9) ||| x10) ||| x11) ||| x12) ||| (x13 &&& x14)) ||| x15) ||| x16) ||| x17) ||| (x18 &&& x4)) ||| x19) ||| (x18 &&& x20)) ||| x21) ||| x22) ||| (x23 &&& x24)) ||| x25) ||| x26) ||| (x23 &&& x27)) ||| (x23 &&& (x14 &&& x28))) ||| (x23 &&& (x29 &&& x28))) ||| (x23 &&& x30)) ||| ((x31 &&& x4) &&& x28)) ||| ((x31 &&& x4) &&& x32)) ||| (x31 &&& (x14 &&& x28))) ||| ((x31 &&& x20) &&& x28)) ||| ((x31 &&& x24) &&& x28)) ||| ((x31 &&& x33) &&& x28)) ||| (x31 &&& (x29 &&& x28))) ||| (x31 &&& x30)) ||| ((x31 &&& x34) &&& x28)) ||| ((x31 &&& x27) &&& x28)) ||| x35))) = 1 then (0#5) else x5) := by
  simp only [ite_self,Readback.Mux.orSelect,Readback.Mux.notSelect,BitVec.and_assoc]

/-- Replacing OR by AND loses an actual admission; the algebra cannot justify it. -/
theorem wrong_guard_rejected :
    (if ((0#1) ||| (1#1)) = 1 then (173#8) else 0) ≠
      (if ((0#1) &&& (1#1)) = 1 then (173#8) else 0) := by decide +kernel

theorem wrong_inversion_rejected :
    (if ~~~(0#1) = 1 then (173#8) else 0) ≠
      (if (0#1) = 1 then (173#8) else 0) := by decide +kernel

run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (name,_) in env.constants.toList do
    if name.toString.startsWith "Pinwheel.Hardware.Readback.Mux." ||
        name.toString.startsWith "_private.Pinwheel.Hardware.Readback.Mux" ||
        name.toString.startsWith "HardwareReadbackMuxTests." then
      let axioms ← collectAxioms name
      let bad := axioms.filter fun a => a != ``propext && a != ``Classical.choice && a != ``Quot.sound
      unless bad.isEmpty do throwError "Unapproved mux proof axiom {name}: {bad}"
      count := count+1
  unless count ≥ 9 do throwError "Incomplete mux proof audit"
  logInfo m!"Readback mux audit: {count} declarations, standard axioms only."
end HardwareReadbackMuxTests
