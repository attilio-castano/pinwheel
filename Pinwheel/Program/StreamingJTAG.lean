import Pinwheel.Program.StreamingCompile
import Pinwheel.Program.StreamingExecution

/-! JTAG TAP semantics at TCK rising edges and the control sequence of the compiled scan. -/
namespace Pinwheel.Program.StreamingJTAG
open Pinwheel.Program.Streaming

inductive Tap where
  | reset | idle | selectDR | captureDR | shiftDR | exit1DR | pauseDR | exit2DR | updateDR
  | selectIR | captureIR | shiftIR | exit1IR | pauseIR | exit2IR | updateIR
  deriving DecidableEq

def advance (s : Tap) (tms : Bool) : Tap :=
  match s with
  | .reset => if tms then .reset else .idle
  | .idle => if tms then .selectDR else .idle
  | .selectDR => if tms then .selectIR else .captureDR
  | .captureDR => if tms then .exit1DR else .shiftDR
  | .shiftDR => if tms then .exit1DR else .shiftDR
  | .exit1DR => if tms then .updateDR else .pauseDR
  | .pauseDR => if tms then .exit2DR else .pauseDR
  | .exit2DR => if tms then .updateDR else .shiftDR
  | .updateDR => if tms then .selectDR else .idle
  | .selectIR => if tms then .reset else .captureIR
  | .captureIR => if tms then .exit1IR else .shiftIR
  | .shiftIR => if tms then .exit1IR else .shiftIR
  | .exit1IR => if tms then .updateIR else .pauseIR
  | .pauseIR => if tms then .exit2IR else .pauseIR
  | .exit2IR => if tms then .updateIR else .shiftIR
  | .updateIR => if tms then .selectDR else .idle

def walk (s : Tap) : List Bool → Tap × Nat
  | [] => (s, 0)
  | b :: bs =>
    let tail := walk (advance s b) bs
    (tail.1, (if s = .shiftDR then 1 else 0) + tail.2)

theorem walk_append (s : Tap) (a b : List Bool) :
    walk s (a ++ b) =
      let first := walk s a
      let last := walk first.1 b
      (last.1, first.2 + last.2) := by
  induction a generalizing s with
  | nil => simp [walk]
  | cons t a ih => simp [walk, ih, Nat.add_assoc]

def pulseTms (i : Instruction) : Bool := i.cell.highPins.levels.getLsbD 2

def beforeScan (d : Fin 256) : List Bool := ((jtagSource d).take 9).map pulseTms
def afterScan (d : Fin 256) : List Bool := (((jtagSource d).drop 10).take 2).map pulseTms

def scanTms (d : Fin 256) (last bit : Bool) : Bool :=
  ((jtagCell d).dataPins true last bit).levels.getLsbD 2

def dataClocks (d : Fin 256) : List Bool → List Bool
  | [] => []
  | [x] => [scanTms d true x]
  | x :: y :: xs => scanTms d false x :: dataClocks d (y :: xs)

theorem scan_mask (d : Fin 256) (last bit : Bool) : scanTms d last bit = last := by
  change scanTms (0 : Fin 256) last bit = last
  cases last <;> cases bit <;> decide +kernel

theorem data_clock_bits (d : Fin 256) (body : List Bool) (last : Bool) :
    dataClocks d (body ++ [last]) = List.replicate body.length false ++ [true] := by
  induction body with
  | nil => simp [dataClocks,scan_mask]
  | cons x xs ih =>
    cases xs with
    | nil => simp [dataClocks,scan_mask]
    | cons y ys =>
      simp only [List.cons_append,dataClocks,scan_mask,List.length_cons,List.replicate_succ]
      rw [List.cons_append] at ih
      rw [ih]
      rfl

theorem enter_scan (s : Tap) (d : Fin 256) : (walk s (beforeScan d)).1 = .shiftDR := by
  have bits : beforeScan d = [true,true,true,true,true,false,true,false,false] := by
    change beforeScan (0 : Fin 256) = _
    decide +kernel
  rw [bits]
  cases s <;> decide +kernel

theorem scan_exactly (n : Nat) :
    walk .shiftDR (List.replicate n false ++ [true]) = (.exit1DR,n+1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp [List.replicate_succ,walk,advance,ih,Nat.add_comm,Nat.add_left_comm]

theorem compiled_scan_control (s : Tap) (d : Fin 256) (body : List Bool) (last : Bool) :
    let wire := (beforeScan d ++ dataClocks d (body ++ [last])) ++ afterScan d
    (walk s wire).1 = .idle ∧
    (walk s wire).2 = (walk s (beforeScan d)).2 + body.length + 1 := by
  have suffix : afterScan d = [true,false] := by
    change afterScan (0 : Fin 256) = _
    decide +kernel
  dsimp only
  rw [walk_append,walk_append]
  dsimp only
  rw [enter_scan, data_clock_bits,scan_exactly,suffix]
  simp [walk,advance,Nat.add_assoc]

theorem reset_preamble_count (s : Tap) (d : Fin 256) :
    (walk s (beforeScan d)).2 = (if s = .shiftDR then 1 else 0) := by
  have bits : beforeScan d = [true,true,true,true,true,false,true,false,false] := by
    change beforeScan (0 : Fin 256) = _
    decide +kernel
  rw [bits]
  cases s <;> decide +kernel

end Pinwheel.Program.StreamingJTAG
