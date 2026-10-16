# Physical tools and captured replay

The [branch closeout](../docs/history/tt-buffered-branch-closeout.md) records
local commits, final host validation and the completed isolated foundation gate.

The buffered Tiny Tapeout work has three complementary records: source and
selected research manifests in Git; historical source mirrors; and ignored
native evidence under `build/`. Committing the first two does not preserve the
third. The [campaign study](../docs/physical/tt-buffered-overnight-campaign.md)
records the retained C14 routing result and its failed or open qualification
gates. No tool directory here constitutes a tapeout-ready chip.

| Owner | Purpose and execution boundary |
| --- | --- |
| [`scripts/check-tt-buffered*.py`](../scripts/check-tt-buffered.py) | Finite upload-to-pins and mapped-netlist validation of the TT wrapper. These commands need accepted generated inputs, receipts and simulator tools. See the [wrapper study](../docs/protocols/tt-buffered-sram.md). |
| [`scripts/prepare-buffered-tt-physical.py`](../scripts/prepare-buffered-tt-physical.py), [`scripts/run-buffered-tt-physical.py`](../scripts/run-buffered-tt-physical.py), [`physical/buffered_tt/`](../physical/buffered_tt/) | Freeze a physical candidate and explicitly run its bounded offline flow. A prepared directory and passing functional gate are prerequisites. |
| [`openroad-drt-preservation/`](openroad-drt-preservation/README.md) | Pinned native import/export preservation repair and negative fixtures. Matching source, headers, runtime and actual build/fixture receipts are required. Adapter qualification does not establish physical closure. |
| [`pinwheel-physical-campaign/`](pinwheel-physical-campaign/README.md) | Owned execution, routing-ledger parsing and immutable stage admission. The historical stage reads native bootstrap files from the original ignored P2 run. |
| [`pinwheel-postroute-qualification/`](pinwheel-postroute-qualification/README.md) | Separate RC extraction/STA, GDS, public DRC, boundary LVS and antenna measurements. Producer completion and physical pass remain separate. |
| [`pinwheel-drt-logger-observer/`](pinwheel-drt-logger-observer/README.md), [`observer02`](pinwheel-drt-logger-observer-02/README.md), [`observer03`](pinwheel-drt-logger-observer-03/README.md) | Versioned diagnostic observers. Earlier observation-gate failures remain failures. Observer03 measures the actual Python Design context; its retained recovery supplies an observation, not a new routed candidate. |
| [`pinwheel-physical-history/`](pinwheel-physical-history/README.md) | Byte-identical immediate authored source from 122 historical build directories. Includes unsuccessful and superseded versions; the manifest makes no execution or acceptance claim. |
| [`pinwheel-evidence-pack/`](pinwheel-evidence-pack/README.md) | Host-only collection and verification of a declared receipt dependency closure. A sealed pack preserves selected bytes, not every local file or the CAD image. |
| [`openroad-hold/`](openroad-hold/README.md), [`openroad-route-import/`](openroad-route-import/README.md) | Earlier pinned native adapters. Their own studies and receipts determine applicability; they are separate from the overnight detailed-route preservation adapter. |

## Replay identities and missing inputs

The original buffered physical worktree is
`/Users/attiliocastano/.codex/worktrees/8259/pinwheel`. Some captured observer
launchers embed this path. Native adapter/observer builds also refer to matching
headers at
`/Users/attiliocastano/.codex/worktrees/c6eb/pinwheel/build/validation/hold-repair-01/headers`.
These paths identify captured inputs; they are not portable installation paths.
Do not edit them inside historical snapshots or relabel changed bytes as the
original experiment. A future maintained path adapter needs a separate identity
and fresh admission controls.

The campaign stager also reads the ignored original
`build/physical/tt-p2-drt-onepass-route-01` bootstrap and
`build/physical/tt-p2-drt-postroute-tools-03/audit.py`. Qualification preparation
can use the ignored `tt-p2-drt-onepass-tools-04/native_inventory.py` and installed
native-script capture. Source mirrors recover authored code but do not replace
the expected checkpoints, guides, generated RTL, PDK/library views, metadata,
build receipts or compiled adapters at those locations.

Earlier Design A replay documentation refers to tools under the legacy `a2b1`
worktree. On 2026-10-16, both its
`build/tools/oss-cad-suite/bin/iverilog` and `vvp` were absent; this worktree's
equivalent paths were also absent. Therefore the preserved functional receipts
do not imply that a fresh simulator replay is currently available. This is a
separate dependency issue from the overnight Linux physical runtime. The
[Design A replay guide](../docs/research/current-a-replay.md) has its own
relocation and scope rules.

The overnight physical runtime was locally observed as Linux arm64
`ghcr.io/librelane/librelane@sha256:5825633bea1f9cbc705ece2de2bc31de6e4ec83d233739205a0f265ef9d92f92`.
The Docker runtime image was **not exported** into the evidence pack, and its
remote availability was not tested. The pinned physical-toolchain configuration
alone does not identify this actual campaign environment. Use the captured
image-inspection receipt and per-job source/input maps.

## Retention before worktree removal

The original ignored campaign owner is
`build/physical/tt-overnight-campaign-20261015/`. Its `REPRODUCE.md`,
`EVIDENCE_PACK_STATUS.json`, externally recorded seal and final closeout receipts
describe the retained 2.5 GB content-addressed evidence pack and the actual
runtime boundary. Offline pack verification establishes those selected payload
bytes; origin verification additionally compares the original live paths. Git
commits and a local pack in the same worktree are not an independent backup.

Complete build retention is broader than that selected pack. The source archive
was added because several earlier repaired RC/STA/incremental helper bytes were
outside its closure. Preserve the full ignored build evidence and all required
cross-worktree dependencies independently before deleting or archiving their
owners. A full-build copy still does not automatically export Docker images or
resolve dependencies located outside that copied tree. Record a retention
destination and verification result separately; do not infer either from a
manifest or a Git commit.

Historical campaign deadlines have expired. Replay requires a new authorized
execution window, immutable output directory and policy receipts. Extending old
deadlines in place would change historical evidence. No command should be run
merely because its source was archived.

The following check reads source mirrors and originals without launching CAD:

```sh
python3 -B tools/pinwheel-physical-history/verify.py --origins
```

The campaign and three observer host suites run from a fresh checkout using
tracked fixtures and temporary test inputs. The
[host-test runner](../scripts/check-physical-host-tests.py) rejects skipped tests,
process execution and reads from the checkout's ignored `build/` tree; the
[CI workflow](../.github/workflows/physical-host-tests.yml) runs each suite
separately. See [validation](../docs/validation.md) for commands and scope.

Other tool suites deliberately consume retained native artifacts. In particular,
the postroute qualification suite explicitly skips its actual-capture checks
when their retained package is unavailable. These optional replays are separate
from the portable host gate. Source retention, control agreement, functional
behavior and physical qualification remain separate gates.
