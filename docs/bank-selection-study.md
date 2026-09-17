# Program-bank selection experiment

Closed on 2026-09-15: both variants have complete Lean circuit and emitted-RTL
proofs, but the candidate does not pass the mapping advance gate. It costs about
2.1% more area, improves the slow ABC estimate only 0.15%, and lengthens the
protocol-input logic path. Retain the candidate as an experiment; no new physical
run or default promotion follows. The [result manifest](../physical/experiments/bank-selection-results.json)
pins the completed receipts.

## Objective and fixed contract

Authorized on 2026-09-15: investigate the measured loader-cursor-to-cache path,
prove one candidate, check its actual emitted RTL, and use a matched mapping
screen to decide whether a bounded physical comparison is useful.

The reference instruction and loader semantics stay fixed. Both variants retain
607 register fields / 6,233 bits, two 32-entry dense dictionaries, two 256-entry
index banks, the 322-word host upload, capacity rejection, and exact execution
edges. All read stages use the same pre-edge register snapshot. Input sampling,
reset priority, capture, faults, and atomic replacement retain their contracts.

The first variant is a composed command-split control. It incorporates the
existing proved command transformation into the typed backend. The second
variant computes each program bank's complete instruction lookup independently
and selects the result at the end. This changes program-bank selection; earlier
late-index/late-record experiments concerned branch-target selection.

## Hypothesis and diagnosis

The retained command-split physical report starts at `loader_cursor[5]`, passes
through `loader_commit` and the selected-bank logic, and ends at a current-word
cache register. Its setup miss is 5.049 ns under the 20 ns target. The prior run's
timing results and incomplete layout checks are owned by the
[successor-fetch study](successor-fetch-study.md#matched-command-split-physical-comparison).
The final combinational arc is `_34879_/S` to `_34879_/X`, followed by
`_45626_/D`: the path reaches the cache input through its update selector.
The experiment therefore measures complete cache data/control cones, including
the next-PC comparison, rather than treating instruction data arrival alone as
the full endpoint. No false-path exception or sensitization claim is introduced.

The candidate moves the cursor-dependent bank choice after both index/dictionary
lookups. Its hypothesis is that shortening the work downstream of this decision
will justify the added combinational area. The address calculation itself is
independent of loader cursor/data. Cache-update control and program metadata
remain part of the complete proof and mapping, including any residual cursor
paths. Graph connectivity does not establish path sensitization or delay.

## Proof and artifact method

`Storage/BankSelect.lean` proves command-split expression equality, bank-read
equality, every register update and output, and initialized reference traces for
both variants. `Storage/BankSelectReadback.lean` gives the read-stage decomposition
used by generated proofs. The generic typed netlist emitter produces both RTL
candidates using the same register and port enumeration.

The existing restricted RTL importer is shared unchanged. Variant-specific
proof hints describe the selected address, program-bank selection, each read
stage, successor and next PC. Lean checks those hints against the circuit and
checks all emitted register updates/outputs. Unsupported shapes still fail.
The proof audit permits only standard Lean axioms; Yosys's Verilog/process
frontend and the JSON interpretation retain their existing trusted boundary.

Fresh receipts are produced with:

```sh
python3 scripts/check-backend-readback.py --variant command-split --tag CONTROL_PROOF
python3 scripts/check-bank-select.py --readback-report build/backend/CONTROL_PROOF/report.json --tag CONTROL_CHECK
python3 scripts/check-backend-readback.py --variant late-bank --tag CANDIDATE_PROOF
python3 scripts/check-bank-select.py --readback-report build/backend/CANDIDATE_PROOF/report.json --tag CANDIDATE_CHECK
```

Each downstream check requires the exact proof source/artifact hashes and
regenerates matching RTL. It also requires the regenerated legacy command-split
RTL to match the frozen physical artifact, then checks sequential equivalence
to it and to generic gates under corresponding states. Independent atomic
regressions and typical/slow technology mappings remain separate evidence.

Focused regressions alternate both banks and exercise consecutive final-upload,
commit and start edges, early commit rejection, reset priority and 128 continuous
input-dependent branches. Wrong-bank, early-commit and stale-cache RTL fixtures
must compile and then fail the independent oracle.

After both downstream checks, reproduce the focused cases and mapped graph screen
using fresh output paths:

```sh
python3 scripts/check-bank-select-cases.py --control build/backend/CONTROL_CHECK/composed.sv --candidate build/backend/CANDIDATE_CHECK/composed.sv --testbench build/backend/CONTROL_CHECK/measured/tb.sv --output build/backend/CASES
python3 scripts/report-bank-select.py --control build/backend/CONTROL_CHECK/measured --candidate build/backend/CANDIDATE_CHECK/measured --output build/backend/CONES.json
python3 -B -m unittest discover -s test -p 'test_bank_select.py'
```

## Advance and stop gates

The local screen compares full-core area, both mapping corners, and maximum
cell/logic depth from loader cursor, loader data, commands, reset and protocol
inputs to cache data/control inputs. Every Liberty-declared flip-flop terminates
the graph traversal. A shorter logical path alone is insufficient: advance only
with a useful slow-corner improvement and viable area cost under the same
floorplan. Retain an unsuccessful screen and stop before routing it.

The new composed control's RTL differs from the previously routed artifact.
Its behavioral equivalence permits functional comparison; prior physical
measurements cannot be assigned to the new bytes. A surviving candidate needs a
fresh composed control and candidate with matched settings.

The authorized physical allocation is one candidate run and, if required, one
separately accounted control run, each with four CPUs, 6 GiB and one hour maximum.
Use the pinned technology/tools, F2 controls, unchanged 20 ns/I/O constraints,
and diagnostic 6x4 floorplan. Record the last completed checkpoint on timeout.
Timing closure additionally requires complete setup/hold, electrical and layout
checks. Default selection and external-interface work are separate decisions.

## Results

### Correctness and artifact validation

Both complete transitions, all outputs and initialized reference traces pass
Lean's checks. Each variant rejects all six compilable RTL corruptions and
accepts unchanged reimport. The declaration counts include generated proofs;
both audits permit only standard Lean axioms.

| Full RTL read-back | Control | Candidate |
| --- | ---: | ---: |
| Checked local equalities | 3,209 | 3,214 |
| Largest local expression (nodes) | 213 | 213 |
| Audited declarations / theorems | 65,222 / 40,122 | 65,491 / 40,306 |
| Elapsed seconds | 1,004.539 | 923.856 |

Each downstream check passes all 6,315 legacy/variant and 6,309 RTL/generic-gate
comparison points, plus 21,409 independent atomic loader edges and 13,151,052
storage-field observations. Cache corruption is rejected. These checks take
92.361 seconds for the control and 96.801 seconds for the candidate.

The final focused regression against these exact checked RTLs passes all 2,090
edges for both variants. It includes four alternations between program banks,
consecutive final-upload/commit/start edges, early commit rejection, reset over
eligible commands and 128 continuous input-dependent branches. All three
compilable wrong-bank, early-commit and stale-cache fixtures fail the oracle.
The first exploratory focused receipt is retained separately; the final receipt
uses the fresh control measurement testbench.

The whole library builds with warnings treated as errors. Two portable tests
check proof-hint roles/widths and sequential graph boundaries, including cycle
rejection; the shared importer/receipt tests also pass. The first cone-report
invocation failed while naming a symlinked cached library, before publishing a
receipt. Keeping its configured repository path fixes that bookkeeping; the
completed report hashes the actual library bytes.

### Matched mapping screen

Both variants retain 6,226 mapped flip-flops. The mappings use the same pinned
libraries and tool settings. ABC delay is a combinational mapping estimate,
without routed parasitics or the full physical timing boundary.

| Metric | Control | Candidate | Change |
| --- | ---: | ---: | ---: |
| Typical cell area (µm²) | 546,109.9056 | 557,432.5932 | +2.073% |
| Slow cell area (µm²) | 546,547.1760 | 557,846.2764 | +2.067% |
| Typical ABC delay (ns) | 7.10618 | 7.57509 | +6.599% |
| Slow ABC delay (ns) | 9.95550 | 9.94025 | −0.153% |

The source graph confirms that both candidate bank-index and bank-word reads
are independent of loader cursor and data. Cursor-to-successor expression depth
falls from 26 to 6; cursor-to-next-PC depth falls from 46 to 26. These counts
include source wiring/logic operations and are not mapped gate depths.

The mapped graph screen includes complete cache data/control cones. Maximum
logic depth excludes buffers; maximum cell depth includes them. Both stop at
every sequential boundary. Each nonempty family reaches all 57 retained cache
input pins; loader data reaches none. Maximum combinational fanout remains 10.

| Launch family | Control typical/slow cell depth | Candidate typical/slow cell depth | Control → candidate logic depth (both corners) |
| --- | ---: | ---: | ---: |
| Loader cursor | 47 / 47 | 30 / 30 | 32 → 25 |
| Protocol inputs | 48 / 49 | 51 / 51 | 35 → 38 |
| Commands | 45 / 45 | 29 / 29 | 32 → 25 |
| Reset/init | 45 / 45 | 29 / 29 | 32 → 25 |

**Decision:** the cursor path is shorter, but protocol paths deepen and the slow
estimate is nearly unchanged. This does not meet the planned useful slow-corner
improvement gate at the added area cost. Stop before routing and retain all
evidence. This screen does not prove that routing could never improve the
candidate. No part of the conditional two-run physical allocation was consumed.

### Artifact identities

The regenerated legacy RTL matches the frozen physical hash
`1a1fd62b6e17bcdf584abaf7b9733c3e28eab1ab7ce565057588139504cc5a42`.
The proved composed control's RTL is
`318930699f99e92eae489eee05c0ad2cdca9f8e34d6aeb2f7a07fe0fc6c6f764`.
The candidate's RTL is
`f1061a2e90f244d3ef40160a205750a83288caae411940f3afac24e053d7b91f`.
Their behavioral equivalence is checked; prior physical measurements remain
attached to the legacy artifact.

| Completed receipt | SHA-256 |
| --- | --- |
| `build/backend/bank-control-initial/report.json` | `ebe957de2b958eac30b237d0d738837e6707e3119452e82a38ea6f2face86c7e` |
| `build/backend/bank-control-check/report.json` | `6fcf621926f1e72284f340b75a2603ef7fa7f1a11ec785c70bd2bc5b2470e735` |
| `build/backend/bank-candidate-initial/report.json` | `6d2297df519f209434c737aaa397f47ce8650f4020622ef91e39c3fe1e44d73a` |
| `build/backend/bank-candidate-check/report.json` | `6c2d72199848b40ccef3fd9c38d62e0435717b74c10785df241e091a6227fb07` |
| `build/backend/bank-cases-initial/report.json` | `9a02425270868c83b7576341797e30014accfd28199515fc20c960a3f3292d41` |
| `build/backend/bank-cases-final/report.json` | `0d65457540724dc727f531c1961e2f7de0ed8a49034d3ec8293e3bab6adc25c7` |
| `build/backend/bank-selection-cones.json` | `f5305bdff37da888e1d87b2f5bcffb7cf5b36e71daef75cf89c3d77a107b4d2c` |

The final identity check verifies all seven receipts and 898 recorded source /
artifact hashes against current bytes, including the final focused cases' RTL
identities. All 156 local links in the touched study/index documents and
`git diff --check` pass.

## Next question

The old physical path enters the cache update selector, and the candidate still
leaves a substantial cursor-dependent control path. The current cache-update
enable is true while idle; the existing `Cache.busy_selection` theorem excludes
bank switching while running. These facts suggest testing whether factoring the
enable by idle/running state removes the residual loader dependency without
duplicating the read. The [cache-enable follow-up](cache-enable-study.md) now
implements and proves a separate variant on the command-split control. It removes
the direct dependency while retaining an indirect path through the shared read,
and improves the matched mapping screen. The follow-up owns its exact results;
no timing exception follows from either hypothesis.
