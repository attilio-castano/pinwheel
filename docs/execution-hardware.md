# E64 decoder and store hardware

Implementation and measurement: **2026-09-13**, Apple Silicon, pinned Lean
4.33.1, CIRCT `firtool-1.159.0`, and OSS CAD Suite `2026-09-13`.

The bounded sequence is complete: a realistic combined I²C read established the
capacity requirements, [E64](execution-records.md) defines the execution layout,
and two writable store/decoder circuits now have Lean proofs, generated-RTL
checks, and comparable generic synthesis measurements.

These are hardware frontends for the reactive engine. The earlier
[32×16 UART/SPI core](core-hardware.md) remains the complete structural processor
baseline. The wider reactive scheduler, timer/control registers, capture bank,
and physical loading interface are not included in this measured slice.

## Circuit contract

Both candidates have two independent combinational read addresses, eight bits
each. Each read exposes canonical validity and all twelve E64 fields. Invalid
records still expose their raw fields, so the future scheduler must gate their
use on validity. The standalone decoder uses the same logic as both frontends.

The direct store contains 256 writable 64-bit registers. Its balanced selection
tree has eight mux levels before decoding. The indexed store contains 64 writable
64-bit dictionary registers and 256 writable six-bit indices. Its map read has
eight mux levels followed by six dictionary-selection levels. Both support
current and successor lookup without a registered fetch cycle. Actual path
delay, including branch selection and the destination registers, must be checked
when integrated with the scheduler.

At a rising edge, a raw write is accepted exactly when `write && !busy` and its
bank/address matches. Bank zero writes a record; the indexed dictionary accepts
only addresses 0–63, while direct accepts 0–255. Bank one writes the indexed map
using the low six data bits; direct ignores bank-one writes. Other registers
retain their values. Reads settle to the updated contents after the edge. Busy
blocks writes to either bank.

There is **no assumed power-up memory value, staging bank, atomic commit, reset
port, or completeness check** in this slice. The testbench initializes every
physical register before checking outputs. Raw uploads can expose partial new
contents; a system must not start execution until loading is complete. This is
not yet an implementation of the engine's atomic load operation. Idle pins,
last-address metadata, and commit/start interlocks need their own integration.
Any staging required to preserve an old program must be counted later.

## Proof boundary

All **21 public execution theorems** pass an audit allowing only Lean's standard
axioms (`propext`, `Classical.choice`, `Quot.sound`) or none. The final proofs use
no native decision assumptions. The audit covers:

- Canonical encoding, extraction, accepted-word uniqueness, and decoder
  validity for every 64-bit word.
- Every decoder output wire, generic balanced reads, every register update,
  both read ports, and busy-write retention for arbitrary memory contents.
- Complete-state equality between direct/indexed functional fetch and the typed
  reactive engine for arbitrary starting states and input histories.
- Composition of indexed fetch with the universal I²C register-read compiler
  proof, given a successful indexed-lowering certificate.

The circuit equations prove the frontend behavior. The complete-run theorems
still use the Lean reactive scheduler; they do not claim that a wider reactive
RTL processor has been built. Lowering accepts at most 64 distinct records and
checks all 256 expanded lookups. Actual V0 explicit/counted write files are
tested to lower to identical E64 words. Full V0-to-wide-machine refinement and
physical upload refinement are separate from these lookup certificates.

## Independent executable and RTL evidence

The Python oracle reconstructs the allowed fields for each operation rather
than copying the decoder's validity masks. It checks **100,546 raw words**:
all low-16-bit words, bit mutations of protocol records, canonical operand
extrema/address/capture combinations, reserved-bit variants, and deterministic
random 64-bit words. Lean and generated RTL both match. This is sampled RTL
validation; the universal word claim comes from the Lean proof.

Five loaded images cover UART, SPI, explicit I²C write, combined I²C read, and
counted V0 lowered to E64. Store tests include all addresses, both read ports,
post-write reads, busy and disabled writes, both banks, dictionary address bounds,
map truncation, and malformed records. Direct passes **5,889 edges** and indexed
**5,953 edges**, including respectively 256 and 320 initialization edges. Each
has **5,633 checked read pairs**, with byte-identical Lean/RTL CSV observations.
The five image read sweeps are identical between candidates; raw bank-boundary
tests account for their different memory organizations.

Five RTL mutations are rejected for the expected mismatch: bypass busy gating
in each store, invert a read-address bit in each store, and ignore the decoder's
reserved bit. Native checks also cover 4,096 typed round trips and dictionary
acceptance at 64 unique words/rejection at 65 and 256.

Each packed backend runs the complete independent I²C read matrix:
**4,468 transactions / 1,092,960 observed cycles**, retaining the **502/557-cycle**
quiet/stretched examples. Those are Lean scheduler/packed-fetch wire tests; the
RTL slice tests exercise the actual decoder and stores separately.

## Comparable synthesis result

All three modules use the same unconstrained generic Yosys flow:
`read_verilog -sv`, hierarchy check, `synth`, `check -assert`, `stat`, and
`ltp -noff`. Every memory bit remains writable through input ports. Neither
candidate hardwires a protocol image. Both store totals include their write
logic, two reads, and two decoders; the standalone decoder is a separate result.

| Circuit | Register bits | Combinational cells | Total generic cells | Longest combinational path, cells |
|---|---:|---:|---:|---:|
| Decoder | 0 | 96 | 96 | 12 |
| Direct 256×64 | 16,384 | 69,245 | 85,629 | 26 |
| Indexed 64×64 + 256×6 | 5,632 | 23,312 | 28,944 | 34 |

The indexed store saves **65.6% of register bits** and **66.2% of generic cells**
in this experiment, at the cost of a longer selection path and a 64-distinct-record
limit. This supports carrying it forward as the candidate, with direct retained
as the baseline. These numbers are generic gate counts and topological depth,
not mapped area, nanoseconds, maximum clock frequency, or competition fit.
There is no technology library or clock constraint in this comparison.

## Reproduce and continue

```sh
python3 scripts/check-binary.py
python3 scripts/check-i2c-read.py
python3 scripts/check-execution.py
```

The binary run creates the native input files. The execution runner builds Lean,
audits every public execution theorem, emits MLIR, generates independent
vectors, compares Lean and RTL, rejects mutations, synthesizes both stores, and
runs both packed read matrices. Ignored `build/execution/` contains RTL, netlists,
vectors, CSVs, storage counts, logs, versions, and `report.json` with source and
artifact hashes. The success receipt is removed before a run and written only
after every check passes. The emitter/CIRCT path is tested, not formally proved;
gate equivalence remains open.

The next bounded integration should connect this frontend to structural reactive
control, timers, pin enables, and the 16-slot capture bank, then prove complete
machine refinement and repeat UART/SPI/I²C traces on generated RTL. Terminal
capture must feed the branch decision on the intended edge. Follow with the
staging/commit loader and a technology-constrained area/timing check, counting
metadata and upload storage. Further I²C features can then be chosen against
that working hardware boundary; this batch does not add arbitration, recovery,
analog timing, or arbitrary-length reads.
