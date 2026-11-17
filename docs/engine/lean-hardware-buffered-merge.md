# Buffered many-to-one stream merge

`Stream.BufferedMerge` combines the reusable round-robin arbiter, shared one-hot
selector and elastic output register. It is available through
`Pinwheel.Hardware.Library`. The Lean parameter `n` means **n+1 inputs**, so the
constructor cannot describe an empty source set. Payload width is independent.

The output holds one accepted payload. There are no input queues and no
combinational bypass. An empty output slot can accept an input even when the
consumer is blocked; a full slot can consume and refill on the same edge. Only
the selected input is ready, and selection advances the cursor only when that
input is actually accepted. A valid blocked output remains stable. Asserted
reset suppresses transfers and restores the empty slot and first cursor.

## Public construction and contracts

`Physical.inputInterface n w` enumerates reset, downstream ready, input valids
and input payloads. `Physical.outputInterface n w` enumerates input readies,
output valid and output payload. `Structural.registers n w` contains the slot's
valid/payload registers and n+1 one-hot cursor bits. All expressions are built
through typed substitution into existing components.

`Structural.circuit n w`, `implementation n w` and `resetCertificate n w` use
the common circuit and proof interfaces. State/output correspondence holds for
arbitrary raw inputs and encoded logical states. Reset establishes that encoding
from arbitrary register bits, including malformed cursors. `raw_input_trace`
and `initialized_trace` expose the corresponding finite-history theorems.

The model retains source provenance in a logical `Delivery`; the physical slot
stores only its payload. `encode_eq_of_payload_eq` makes that erasure explicit.
The multiport contract proves per-source conservation and order, single-slot
capacity and unique acceptance. Repeated equal payloads do not merge logical
occurrences. A persistent request is accepted within N eligible refill
opportunities for N inputs. Downstream stalls do not count as opportunities;
delivery requires downstream service. This is not an unconditional cycle bound.

## Reproduction and evidence

```sh
lake build Pinwheel.Hardware.Library
lake env lean -DwarningAsError=true --run test/BufferedMergeModel.lean
lake env lean -DwarningAsError=true --run test/BufferedMergeCircuit.lean
python3 -m unittest discover -s test -p 'test_buffered_merge_oracle.py'
python3 scripts/check-buffered-merge.py --tag merge-local
python3 scripts/check-buffered-merge-artifact.py --tag merge-artifact-local
python3 scripts/check-buffered-merge-artifact-negatives.py --tag merge-negatives-local \
  --positive-report build/buffered-merge-artifact/merge-artifact-local/report.json
```

The model test covers 2,664 exhaustive edges, 10,000 protocol-respecting stress
edges and 103 fairness checks; 123 declarations pass its standard-axiom audit.
The structural test checks 6,064 exhaustive edges, 3,840 trace edges and 64 dirty
reset cases, with a separate 265-declaration audit. Semantic tests include zero
payload width; physical emission requires positive widths.

`build/buffered-merge/merge-matrix-20261116-01/report.json` passes the full matrix
N∈{1,2,3,5,8}, w∈{1,8,17}: 5,286 edges per RTL form, every emitted register and
pre/post output, plus synthesized output replay. The independent occurrence
ledger includes source and serial identity, so repeated payload values remain
distinct. The runner detects 54 actual RTL faults. Twelve portable oracle,
descriptor and trace-parser tests also pass; incomplete, unknown or malformed
traces cannot stand in for semantic mismatch evidence.

`build/buffered-merge-artifact/merge-artifact-02/report.json` certifies all 15
configurations: 1,760 local equalities and 174 typed endpoints. Each certificate
covers arbitrary binary register/input bits and composes with the implementation
and reset certificate to obtain a reset-initialized protocol trace theorem.
The eight-input proof search expands bitwise equations before deeper tactic
search; all original propositions and the standard-axiom audit remain intact.

`build/buffered-merge-artifact-negatives/merge-negatives-20261116-01/report.json`
binds the passed positive artifact set. Four actual RTL corruptions fail local
semantic equalities and have kernel-checked witnesses: blocked payload 90→165,
cursor advancement with no acceptance, two simultaneous input readies, and a
dropped refill during output consumption. Each witness also checks the active
handshake/state condition. Parser failure and timeout do not count as rejection.

Artifact correspondence concerns the imported unsynthesized two-state RTL.
Yosys and restricted JSON interpretation remain trusted boundaries. Protocol
claims require initialization; arbitrary malformed cursor bits are covered by
artifact equality and reset recovery, not an uninitialized fairness promise.
Generic synthesis results in the RTL receipt are separate from physical timing
and do not qualify a fabricated device.
