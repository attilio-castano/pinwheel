import Pinwheel.Program.Resident

namespace Pinwheel.Program.Resident
open Pinwheel.Engine.Reactive Pinwheel.Hardware

theorem shift_encode_canonical (output : Fin 3) (order : Order)
    (duration : Fin 256) (pins : Pins) :
    Storage.PairedResidentImage.canonical (encode (.shift output order duration pins)) = true := by
  simp [encode, Storage.PairedResidentImage.canonical, Execution.unpack_pack, shiftBits]
  cases order
  all_goals rcases output with ⟨n, h⟩
  all_goals have hn : n = 0 ∨ n = 1 ∨ n = 2 := by omega
  all_goals rcases hn with rfl | rfl | rfl
  all_goals simp [Order.isMsbFirst]
  done

theorem keep_encode_canonical (preserve : BitVec 3) (pins : Pins)
    (capture : Option (Capture 15)) (duration : Fin 256) :
    Storage.PairedResidentImage.canonical (encode (.keep preserve pins capture duration)) = true := by
  simp [encode, Storage.PairedResidentImage.canonical, Execution.unpack_pack]
  cases capture
  all_goals simp [Execution.captureBits]
  all_goals bv_normalize
  all_goals bv_omega
  done

private theorem ordinary_kind_bound (operation : Engine.Reactive.Instruction 255 15) :
    (Execution.unpack (Execution.encode operation)).kind.toNat < 5 := by
  cases operation
  all_goals simp [Execution.encode, Execution.unpack_pack, Execution.fields, Execution.actionFields]
  rename_i checked
  cases finish : checked.finish
  all_goals simp [Execution.finishFields]
  done

theorem ordinary_encode_canonical (operation : Engine.Reactive.Instruction 255 15) :
    Storage.PairedResidentImage.canonical (encode (.ordinary operation)) = true := by
  have bound := ordinary_kind_bound operation
  have kind5 : (Execution.unpack (Execution.encode operation)).kind ≠ 5 := by bv_omega
  have kind6 : (Execution.unpack (Execution.encode operation)).kind ≠ 6 := by bv_omega
  simp only [encode, Storage.PairedResidentImage.canonical, if_neg kind5, if_neg kind6,
    Execution.decode_encode, Option.isSome_some]
  done

theorem encode_canonical (instruction : Instruction) :
    Storage.PairedResidentImage.canonical (encode instruction) = true := by
  cases instruction
  all_goals simp only [ordinary_encode_canonical, shift_encode_canonical, keep_encode_canonical]
  done

theorem source_valid (p : Program) : Storage.PairedResidentImage.Valid (source p) := by
  simp [Storage.PairedResidentImage.Valid, source, imageWords, encode_canonical]
  done

theorem enter_shift (p : Program) (pc : Fin 256) (s : State) (inputs : Inputs)
    (output : Fin 3) (order : Order) (duration : Fin 256) (pins : Pins)
    (instruction : p.fetch pc = .shift output order duration pins) :
    enter p pc s inputs =
      ⟨⟨.active pc duration, shiftPins output order pins s.operand, s.core.samples⟩,
        shifted order s.operand⟩ := by
  change p.memory[pc.val] = .shift output order duration pins at instruction
  simp [enter, Engine.Reactive.enter, lower, Engine.Reactive.Program.fetch, Program.fetch,
    normalize, enteredOperand, instruction, Engine.Reactive.capture]
  done

theorem enter_keep (p : Program) (pc : Fin 256) (s : State) (inputs : Inputs)
    (preserve : BitVec 3) (pins : Pins) (capture : Option (Capture 15)) (duration : Fin 256)
    (instruction : p.fetch pc = .keep preserve pins capture duration) :
    enter p pc s inputs =
      ⟨⟨.active pc duration, keepPins preserve pins s.core.pins,
        Engine.Reactive.capture s.core.samples capture inputs⟩, s.operand⟩ := by
  change p.memory[pc.val] = .keep preserve pins capture duration at instruction
  simp [enter, Engine.Reactive.enter, lower, Engine.Reactive.Program.fetch, Program.fetch,
    normalize, enteredOperand, instruction]
  done

theorem lower_ordinary (p : Engine.Reactive.Program 255 15) (operand : BitVec 8) (old : Pins) :
    lower (ordinaryProgram p) operand old = p := by
  cases p
  simp [lower, ordinaryProgram, normalize, Vector.map_map, Function.comp_def]
  done

theorem enteredOperand_ordinary (p : Engine.Reactive.Program 255 15)
    (core : Engine.Reactive.State 255 15) (operand : BitVec 8) :
    enteredOperand (ordinaryProgram p) core operand = operand := by
  cases control : core.control
  all_goals simp [enteredOperand, ordinaryProgram, Program.fetch, control]
  done

theorem advance_ordinary (p : Engine.Reactive.Program 255 15)
    (core : Engine.Reactive.State 255 15) (operand : BitVec 8) (inputs : Inputs) :
    advance (ordinaryProgram p) ⟨core, operand⟩ inputs =
      ⟨Engine.Reactive.advance p core inputs, operand⟩ := by
  simp [advance, lower_ordinary, enteredOperand_ordinary]
  done

theorem advance_operand_held (p : Program) (s : State) (inputs : Inputs)
    (held : dispatching p s inputs = false) : (advance p s inputs).operand = s.operand := by
  simp [advance, held]
  done

theorem active_held (p : Program) (s : State) (pc : Fin 256) (remaining : Fin 256)
    (inputs : Inputs) (active : s.core.control = .active pc remaining)
    (positive : 0 < remaining.val) :
    advance p s inputs =
      ⟨{s.core with control := .active pc ⟨remaining.val - 1, by omega⟩}, s.operand⟩ := by
  have nonzero : remaining ≠ 0 := by omega
  simp [advance, Engine.Reactive.advance, dispatching, active, positive, nonzero]
  done

theorem busy_start_ignored (p : Program) (s : State) (inputs : Inputs)
    (payload : BitVec 8) (busy : Engine.Reactive.busy s.core = true) :
    step p s false true payload inputs = advance p s inputs := by
  simp [step, busy]
  done

theorem reset_priority (p : Program) (s : State) (startRequested : Bool)
    (payload : BitVec 8) (inputs : Inputs) :
    step p s true startRequested payload inputs = reset p := by
  simp [step]
  done

theorem start_as_enter (p : Program) (s : State) (payload : BitVec 8) (inputs : Inputs) :
    start p s payload inputs =
      enter p 0 ⟨{s.core with samples := Vector.replicate 16 false}, payload⟩ inputs := by
  rfl
  done

end Pinwheel.Program.Resident
