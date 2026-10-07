import Pinwheel.Hardware.Buffered.Serial

/-! Local laws for the actual emitted serial frontend expression trees.
These laws do not claim universal trace correspondence of the serial package,
the SRAM macros or the compiler/emitter. -/
namespace Pinwheel.Hardware.Buffered.Serial
open Pinwheel.Hardware

private theorem zero_ne_one : (0 : BitVec 1) ≠ 1 := by decide +kernel
private theorem band_zero_left : ∀ x : BitVec 1, 0 &&& x = 0 := by decide +kernel
private theorem band_zero_right : ∀ x : BitVec 1, x &&& 0 = 0 := by decide +kernel
private theorem inv_one : ~~~(1 : BitVec 1) = 0 := by decide +kernel
private theorem band_one_one : (1 : BitVec 1) &&& 1 = 1 := by decide +kernel

/-- Protocol raw pins go straight to the existing core sampler. -/
theorem raw_inputs_passthrough (i : Values Input) (s : Values Register) :
    circuit.observe i s (.core .rawInputs) = i .rawInputs := rfl
theorem row_word_decode (i : Values Input) (s : Values Register) :
    circuit.observe i s (.core .word) = (s .request).extractLsb' 0 64 := rfl
theorem row_control_decode (i : Values Input) (s : Values Register) :
    circuit.observe i s (.core .control) = (s .request).extractLsb' 64 24 := rfl
theorem commit_count_decode (i : Values Input) (s : Values Register) :
    circuit.observe i s (.core .count) = (s .request).extractLsb' 0 7 := rfl
theorem commit_span_decode (i : Values Input) (s : Values Register) :
    circuit.observe i s (.core .virtualSpan) = (s .request).extractLsb' 7 11 := rfl
theorem start_tx_length_decode (i : Values Input) (s : Values Register) :
    circuit.observe i s (.core .txLength) = (s .request).extractLsb' 32 6 := rfl
theorem start_rx_capacity_decode (i : Values Input) (s : Values Register) :
    circuit.observe i s (.core .rxCapacity) = (s .request).extractLsb' 38 6 := rfl

/-- Outside the one registered dispatch pulse, the core command is zero. -/
theorem quiet_command (i : Values Input) (s : Values Register)
    (h : s .dispatch = 0) : circuit.observe i s (.core .command) = 0 := by
  simp only [Circuit.observe, circuit, output, coreInput, delivering, both,
    Expr.eval, h, band_zero_left, band_zero_right, zero_ne_one, ↓reduceIte]
  done

/-- A parser rejection suppresses delivery even on a dispatch edge. -/
theorem rejected_frame_no_delivery (i : Values Input) (s : Values Register)
    (h : s .code ≠ 0) :
    circuit.observe i s (.core .command) = 0 := by
  simp only [Circuit.observe, circuit, output, coreInput, delivering, both,
    Expr.eval, h, decide_false, BitVec.ofBool_false, band_zero_left, band_zero_right,
    zero_ne_one, ↓reduceIte]
  done

theorem wrong_header_code (i : Values Input) (s : Values Register)
    (hc : s .count = 160)
    (hh : (s .request).extractLsb' 148 12 ≠ 0xA71) :
    closingCode.eval i s = 2 := by
  simp only [closingCode, headerValid, Expr.eval, hc, hh, decide_true,
    BitVec.ofBool_true, decide_false, BitVec.ofBool_false, zero_ne_one, ↓reduceIte]
  done

/-- A quiet sample after closure removes the dispatch pulse; capture follows
the previous pulse on its separate register. -/
theorem dispatch_one_shot (i : Values Input) (s : Values Register)
    (hc : i .csn = 0) (hi : i .initialize = 0) :
    circuit.step i s .dispatch = 0 := by
  simp only [Circuit.step, circuit, next, nextUninitialized, closingRequest,
    closing, both, Expr.eval, hc, hi, band_zero_left, band_zero_right,
    zero_ne_one, ↓reduceIte]
  done

theorem capture_pipeline (i : Values Input) (s : Values Register)
    (hi : i .initialize = 0) : circuit.step i s .capture = s .dispatch := by
  simp only [Circuit.step, circuit, next, nextUninitialized, Expr.eval,
    hi, zero_ne_one, ↓reduceIte]
  done

/-- Partial and overlong response reads retain READY, even when CS closes. -/
theorem aborted_read_retains_ready (i : Values Input) (s : Values Register)
    (hi : i .initialize = 0) (hcap : s .capture = 0)
    (hlen : s .count ≠ 192) : circuit.step i s .ready = s .ready := by
  simp only [Circuit.step, circuit, next, nextUninitialized, closingReadExact,
    both, Expr.eval, hi, hcap, hlen, decide_false, BitVec.ofBool_false,
    band_zero_right, zero_ne_one, ↓reduceIte]
  done

/-- Neither polling nor changing live core status can change a held snapshot. -/
theorem response_snapshot_stable (i : Values Input) (s : Values Register)
    (hi : i .initialize = 0) (hcap : s .capture = 0) :
    circuit.step i s .response = s .response := by
  simp only [Circuit.step, circuit, next, nextUninitialized, Expr.eval,
    hi, hcap, zero_ne_one, ↓reduceIte]
  done

theorem physical_initialize_clear (i : Values Input) (s : Values Register)
    (hi : i .initialize = 1) (r : Register w) :
    circuit.step i s r = (match r with
      | .sckPrev => i .sck | .csnPrev => i .csn | _ => 0) := by
  cases r <;> simp_all [Circuit.step, circuit, next, Expr.eval]
  done

theorem inactive_no_dispatch (i : Values Input) (s : Values Register)
    (ha : s .active = 0) (hi : i .initialize = 0) :
    circuit.step i s .dispatch = 0 := by
  simp only [Circuit.step, circuit, next, nextUninitialized, closingRequest,
    closing, both, Expr.eval, ha, hi, band_zero_left, zero_ne_one, ↓reduceIte]
  done

theorem close_deactivates (i : Values Input) (s : Values Register)
    (ha : s .active = 1) (hc : i .csn = 1) (hi : i .initialize = 0) :
    circuit.step i s .active = 0 := by
  simp only [Circuit.step, circuit, next, nextUninitialized, starting, closing,
    both, Expr.eval, ha, hc, hi, inv_one, band_zero_left, band_zero_right,
    band_one_one, zero_ne_one, ↓reduceIte]
  done

end Pinwheel.Hardware.Buffered.Serial
