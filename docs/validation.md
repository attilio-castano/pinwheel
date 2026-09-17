# Validation and review gates

Run the local checks below before pushing a PR. Hardware experiments remain
separately reproducible with the pinned Apple Silicon tools and explicit fixture
prerequisites. Passing the portable gate does not establish emitted-RTL
equivalence, physical fit, or an operating frequency.

## Local pre-push checks

Install the repository's `lean-toolchain` with Elan and use Python 3.12+:

```sh
python3 -B -m unittest discover -s test -p 'test_*.py'
python3 scripts/check-foundation.py --tag first-check
```

The first command checks physical input/checkpoint provenance, backend import
boundaries, receipt binding, and bank-selection helpers using disposable files;
it requires no CAD tools. The second runs the portable Lean/model gate.

The runner requires no prior `.lake/` or `build/` content. Each run writes logs,
commands, source hashes and a success receipt under `build/validation/<tag>/`.
Choose a fresh tag to preserve earlier gate evidence. Other model suites retain
their existing output locations, so use a separate checkout to preserve previous
experiment outputs when rerunning them. A failure produces no success receipt.

The gate:

1. Checks that every library module is reachable from `Pinwheel.lean` and that
   the actual compiler matches the repository pin, then runs `lake build` with
   warnings treated as errors.
2. Audits every Pinwheel declaration in the compiled environment, including
   private and generated declarations and definitions containing proofs. Only
   `propext`, `Classical.choice`, and `Quot.sound` are allowed. An injected custom
   axiom must fail for the expected diagnostic. Counts include generated
   theorems; they are not counts of manually written mathematical results.
3. Runs UART TX/RX, link timing, continuous buffered reception with ideal and
   unequal clocks, SPI, shared engine, reactive I²C, explicit/counted/binary execution,
   register reads, encoding, countdown, timed-interface/fetch, and storage
   certificate checks. Their existing negative cases remain included.
4. Independently decodes and checks generated PWL images and UART RX E64 execution
   with Python oracles. RX includes every supported period/input storage configuration.

The [continuous UART suite](uart-stream.md#validation-and-reproduction) checks
all 65,536 ordered byte pairs, independent wire/queue oracles, consumer stalls,
reset/error recovery, and exact correspondence with the compiled RX supervisor.
The [unequal-clock stream suite](uart-stream-clocks.md#validation-and-reproduction)
adds independent physical-time wire and detection schedules, varying observation
age, relative phases, rearm boundaries, and cases outside the sufficient bounds.
These are Lean/model checks; the supervisor's new buffer has no RTL validation yet.

Validation runs locally; the repository has no automatic GitHub Actions workflow.
Include the check results and source identity in the PR description. Before
pushing, verify that the committed sources match the validated sources. If code,
tests, or validation inputs change, run the affected checks again. Documentation
edits require link and whitespace checks.

## Hardware prerequisite order

These are explicit local gates, not mandatory cloud CI jobs. The checked archives
in `tools/hardware-toolchain.json` target **darwin-arm64**; do not use them in a
Linux workflow. Install the pinned tools and Liberty libraries as described in
[development](development.md). The physical flow has a separate container/PDK pin.

For a new checkout, the relevant dependency chain is:

| Gate | Inputs to generate first | Evidence owner |
| --- | --- | --- |
| Countdown artifact/equivalence | `check-hardware.py` generates its own fixtures; pinned CIRCT/Yosys/Icarus binaries required | [Hardware closure](hardware-closure.md#countdown-artifact-interpretation-rather-than-a-compiler-proof) |
| Full-backend Lean RTL read-back | `check-backend-readback.py --tag NAME` regenerates its own artifact; pinned CIRCT/Yosys/Z3 binaries required | [Full read-back](hardware-closure.md#full-backend-rtl-read-back) |
| Composed dense cached backend | `check-backend.py --tag NAME` builds the native emitter and loader fixtures; pinned hardware tools and technology libraries required | [Composed backend](hardware-closure.md#composed-backend) |
| Program-bank selection variants | `check-backend-readback.py --variant command-split` or `--variant late-bank`, followed by `check-bank-select.py` with the exact proof receipt | [Bank-selection study](bank-selection-study.md) |
| Cache-enable variant | `check-backend-readback.py --variant enable-split`, followed by `check-bank-select.py` and exact-cache regression | [Cache-enable study](cache-enable-study.md) |
| Original UART/SPI core | No prior protocol fixtures; `check-core.py` generates its own | [Original core](core-hardware.md) |
| Reactive core | No prior binary fixtures; `check-reactive-core.py` generates its own | [Reactive core](reactive-core-hardware.md) |
| Atomic loader | No prior binary fixtures; `check-loader.py` generates its own | [Atomic loader](atomic-loader.md) |
| UART RX integration | No prior fixtures; `check-uart-rx-hardware.py --tag <fresh-tag>` regenerates mixed-protocol traces and simulates four backends, including the default dense cached core | [UART receive](uart-receive.md) |
| E64 frontends | Run `check-binary.py`, then `check-execution.py` | [E64 hardware](execution-hardware.md) |
| Dense codec | Execution decoder vectors from the preceding frontend check; create `build/storage` with `test/Storage.lean`, then run `check-dense-codec.py` | [Storage study](storage-study.md) |
| Cached/dense storage | Loader vectors and observation include from `check-loader.py`; emit with `test/Storage.lean`, then run the storage measurement commands below | [Storage study](storage-study.md) |
| Timed contracts | Cached oracle vectors, codec vectors, and general small/dense/cached oracle fixture hashes | [Timed contracts](timed-components.md) |
| Decoder candidate screen | Successful current timed-contract receipt, mapped default receipt, and prepared default physical RTL | [Successor-fetch study](successor-fetch-study.md) |

After loader/frontend/codec preparation, the storage fixtures required by the
current timed-contract runner can be generated with:

```sh
lake env lean --run test/Storage.lean
python3 scripts/measure-storage-variant.py cached --ff 11417
python3 scripts/measure-storage-variant.py small-dense-cached --ff 6226
python3 scripts/check-timed-contracts.py
```

These storage commands include technology mapping. They overwrite their older
run receipts; prefer a new checkout when reproducing them. The timed-contract
runner validates the frozen fixture identities in `test/timed-contracts-baseline.json`
and the unchanged default MLIR/RTL hashes. A mismatch is a failed comparison to
investigate, not a reason to replace the baseline hashes automatically.

Existing retained fixtures may also be used for a focused regression after their
hashes are checked. Label that result as a regression against frozen fixtures,
not as proof that every prerequisite was regenerated from a clean checkout.

The composed-backend gate retains old/new RTL equivalence, RTL/generic-gate
equivalence, independent storage regression, and two mapped corners under a
fresh `build/backend/<tag>/`. Run `check-backend-readback.py --tag NAME` to check
the full emitted transition and initialized traces in Lean. Pass its receipt to
`check-backend.py --readback-report PATH --tag NAME` to require exact source and
artifact identities across both gates. Both countdown and full-backend read-back
retain an explicit trusted parser/frontend boundary. See
[hardware closure](hardware-closure.md) for initial-state relations and mutations.

Candidate staging and timeout/provenance regressions use disposable files and no
CAD execution:

```sh
python3 -B -m unittest discover -s test -p 'test_physical_*.py'
python3 -B -m unittest discover -s test -p 'test_backend_readback.py'
python3 -B -m unittest discover -s test -p 'test_bank_select.py'
```

## Foundation review order

1. **Protocol semantics and compilers:** exact pin edges, capture order, bounded
   protocol scope, and compiler theorem hypotheses.
2. **Machine and storage:** reset/start priorities, atomic image replacement,
   capacity rejection, cache invariants, and exact-edge refinement.
3. **Translation and independent checks:** structural expressions, emitter wiring,
   malformed input coverage, defined-output comparisons, and detected mutations.
4. **Measurements and research records:** baseline identities, fixed constraints,
   default versus experimental backends, and remaining physical limitations.

Preserve historical experiment identities when integrating new work. The hardware
closure and optimization studies record their own artifact-specific evidence;
new physical timing closure or default promotion is not a prerequisite for
merging those functional proofs and experimental variants.
