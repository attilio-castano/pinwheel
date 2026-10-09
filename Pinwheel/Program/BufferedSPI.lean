import Pinwheel.Program.Buffered

/-! The canonical compact mode-0 SPI source: four stored leaves, an inner
eight-bit loop and an outer one-to-four-byte loop. TX and RX are transfer
buffers; no payload is compiled into these instructions. -/
namespace Pinwheel.Program.BufferedSPI
open Buffered Engine.Reactive Engine.Reactive.Counted

structure Config where
  bytesMinusOne : Fin 4
  halfCyclesMinusOne : Fin 256
  sampled : 2 ≤ halfCyclesMinusOne.val
  deriving Repr

def Config.default : Config := ⟨3, 3, by decide⟩

def low (d : Fin 256) : Buffered.Instruction :=
  {operation := .shift 0 false false ⟨⟨0, 7⟩, d, none⟩}

def high (d : Fin 256) : Buffered.Instruction :=
  {operation := .keep 1 0 ⟨⟨2, 7⟩, d, none⟩, append := some 0}

def release (d : Fin 256) : Buffered.Instruction :=
  {operation := .drive ⟨⟨0, 7⟩, d, none⟩}

def halt : Buffered.Instruction := {operation := .halt}

def code (c : Config) : Schedule Buffered.Instruction :=
  .seq (.repeat ⟨c.bytesMinusOne.val, by have := c.bytesMinusOne.isLt; omega⟩
    (.repeat 7 (.seq (.emit (low c.halfCyclesMinusOne))
      (.emit (high c.halfCyclesMinusOne)))))
    (.seq (.emit (release c.halfCyclesMinusOne)) (.emit halt))

theorem geometry (c : Config) :
    (code c).words = 4 ∧ (code c).span = 16 * (c.bytesMinusOne.val + 1) + 2 ∧
    (code c).loops = 2 ∧ (code c).nodes = 9 ∧ (code c).nesting = 2 := by
  simp [code, Schedule.words, Schedule.span, Schedule.loops,
    Schedule.nodes, Schedule.nesting, Nat.mul_comm]
  rfl

def program (c : Config) : Buffered.Program :=
  ⟨code c, ⟨4, 7⟩, by have h := (geometry c).2.1; have := c.bytesMinusOne.isLt; omega,
    by simpa only [(geometry c).2.2.2.1] using (by decide : 9 ≤ 256),
    by simpa only [(geometry c).2.2.2.2] using (by decide : 2 ≤ 2)⟩

/-- Counted virtual fetch repeats the SHIFT/KEEP pair, then executes the final
drive and HALT. This concerns source address decoding, not a physical edge
count or a runtime compiler simulation. -/
theorem fetch_shape (c : Config) (pc : Buffered.PC) :
    (program c).fetch pc =
      if pc.val < 16 * (c.bytesMinusOne.val + 1) then
        some (if pc.val % 2 = 0 then low c.halfCyclesMinusOne else high c.halfCyclesMinusOne)
      else if pc.val = 16 * (c.bytesMinusOne.val + 1) then some (release c.halfCyclesMinusOne)
      else if pc.val = 16 * (c.bytesMinusOne.val + 1) + 1 then some halt
      else none := by
  simp only [Buffered.Program.fetch, program, code, Schedule.locate, Schedule.span]
  simp only [show ((7 : Fin 8).val + 1) * (1 + 1) = 16 from rfl,
    show 1 + 1 = 2 from rfl, Nat.mul_comm,
    Nat.mod_mod_of_dvd pc.val (show 2 ∣ 16 from by decide)]
  have h16 := Nat.mod_lt pc.val (by decide : 0 < 16)
  have h2 := Nat.mod_lt pc.val (by decide : 0 < 2)
  split <;> simp_all
  · refine ⟨#v[Fin.ofNat 8 (pc.val % 16 / 2), Fin.ofNat 8 (pc.val / 16)], ?_⟩
    split <;> simp_all
    done
  · grind
  done

end Pinwheel.Program.BufferedSPI
