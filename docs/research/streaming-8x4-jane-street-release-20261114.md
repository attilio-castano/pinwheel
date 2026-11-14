# Frozen 8×4 Jane Street release rehearsal

Jane Street confirmed 8×4 on November 9 for the planned March 2027
CMOS5L shuttle. The competition asks for a public repository, RTL and
tests, a passing Tiny Tapeout GDS and precheck, the architecture and
instruction set, example programs, and a verification write-up. The
FAQ describes the Tiny Tapeout custom-GDS option for long local builds.
The entry deadline is January 18, 2027.
[Organizer rules and FAQ](https://blog.janestreet.com/protocol-emulator-asic-competition/) ·
[Pinwheel entry draft](../jane-street-8x4-entry.md)

The handoff stages the frozen GDS `d4cd48f0…`, LEF and logical netlist,
preserves the powered view for verification, and adds the exact four
generated SystemVerilog files. The clean source replay matches the
four RTL hashes consumed by the physical parent. It compiled the top
and compared UART receive, SPI duplex, and I²C read and write with the
frozen placed-cell fixture. The upstream 8×4 DEF has the same blob and
SHA-256 as the original candidate's template.

| Release input | Exact revision |
| --- | --- |
| Frozen source | `a305a4b339767e80719c9720a12ced7345b0e814` |
| Current IHP template | `4b1204ab387b5ab94db1d57067051d8d89a2f83c` |
| TTIHP27a action | `e7a50f8f46f9f8df4b2c9935bfeb1cbc6b6ae4f6` |
| Current support tools | `9d13ff3e3e6202090740110438c6a10c1d62ca0f` |
| CMOS5L Ciel PDK | `89d42ee6d2fd9b50b86a1aada6fee6673c3e6008` |

The local converter uses the exact Ubuntu 24.04 amd64 KLayout 0.30.12
package from the custom-GDS action. Independent conversions generated
identical OASIS bytes. The KLayout geometry comparison resolves box,
path and repetition representation at zero coordinate tolerance and
ignores duplicate polygons and format properties. Separately it matches
all 243 label records, including transformations. An independent gdstk
readback matches all 380,716 expanded top-cell instance placements,
all 45 top-cell labels, and the exact top Pin Metal4 and prBoundary
geometry. The GDS sent to precheck is the original frozen GDS.
[Custom-GDS action](https://github.com/TinyTapeout/tt-gds-action/blob/e7a50f8f46f9f8df4b2c9935bfeb1cbc6b6ae4f6/custom_gds/action.yml)

## Local reproduction

The [runner](../../scripts/streaming_8x4_jane_street_release.py)
provides separate stage, convert, precheck, package, and verify commands.
Use a fresh ignored output directory in `build/8x4-jane-street-entry-20261114/`.
The unchanged rehearsal remains in the November 7 trial directory.

The conversion runs the action's `strm2oas` binary offline. The precheck
uses the unmodified official Python and deck entry points, Ciel PDK
revision above, the precheck requirements on Python 3.11, and KLayout
0.30.8 built from the action's pinned Nix package source. The local host
and CAD container use arm64. The hosted action runs on Ubuntu amd64.
The current metadata checker also reopens the staged `info.yaml` and
`docs/info.md`. The precheck selects the complete CMOS5L check inventory
from its own source. It includes the new Yosys Verilog syntax check.
[Precheck action](https://github.com/TinyTapeout/tt-gds-action/blob/e7a50f8f46f9f8df4b2c9935bfeb1cbc6b6ae4f6/precheck/action.yml) ·
[Pinned checker source](https://github.com/TinyTapeout/tt-support-tools/blob/9d13ff3e3e6202090740110438c6a10c1d62ca0f/precheck/precheck.py)

The runner's defaults use the local ignored support and action clones,
PDK and tool virtual environment. Its two offline local Docker images
are `pinwheel-ttihp27a-converter-local:0.30.12` and
`pinwheel-ttihp27a-precheck-local:0.30.8`. The first uses the official
Ubuntu package with SHA-256 `23480767fec91bc9a15e075a9bd6906ba85cd7fdda8b4040dde4ffc95c26a742`.
The second extends the retained CAD image with the `klayout` output from
Nixpkgs `ffa10e26ae11d676b2db836259889f1f571cb14f`. The Ciel installer is
3.2.0. The local native worker lease serializes CAD on this machine.

```sh
ENTRY=build/8x4-jane-street-entry-20261114
RELEASE=$ENTRY/release-replay
SCRIPT=scripts/streaming_8x4_jane_street_release.py
RUNTIME=build/8x4-hold-cap-20261107/verification-precheck-venv/bin/python
python3 -B "$SCRIPT" stage --out "$RELEASE"
"$RUNTIME" -B "$SCRIPT" convert --out "$RELEASE"
python3 -B "$SCRIPT" precheck --out "$RELEASE" \
  --lease "$PINWHEEL_HISTORY/build/streaming-tt-resources/heavy.lock"
python3 -B "$SCRIPT" package --out "$RELEASE" --source "$ENTRY/source-02"
"$RUNTIME" -B "$SCRIPT" verify --out "$RELEASE" --handoff-sha "$RELEASE_SHA256"
```

## Hosted handoff and fabrication

`release-overlay.zip` adds the exact RTL and release views, the reviewed
draft, and `.github/workflows/gds.yml` to a Pinwheel release checkout.
The workflow checks exact files and metadata before calling the official
custom-GDS and precheck actions. Its manual trigger requires the workflow
to be present on the chosen repository's default branch. The local
`tt_submission-local-preview.zip` exercises the documented artifact
structure and uses a clearly marked local provenance record. GitHub
provides a real run URL and commit when the hosted action executes.
[Dispatch workflow requirements](https://docs.github.com/en/actions/how-tos/manage-workflow-runs/manually-run-a-workflow)

The existing main-repository artifact policy rejects raw GDS and large
netlist payloads in a normal PR. A dedicated release repository with
the dispatch workflow on its default branch is one workable publication
path. The current branch carries the workflow template, source scripts,
and receipts' documented identities. Release payload and rehearsal
archives stay in ignored local storage. Publication, hosted execution,
and filing the organizer's entry each require their own decision.
[Artifact policy](../../tools/artifact-policy.json)

| Open fabrication gate | Required input and owner |
| --- | --- |
| CMOS5L timing | IHP or an accepted extraction provider must supply applicable corner SPEFs for `d4cd48f0…` or a released, accepted extraction deck with RC/Liberty pairing. Tiny Tapeout integration must supply the actual host I/O and clock contract, including the earliest arrival on `ui_in[3]` and `ui_in[5]`. |
| Electrical power | Tiny Tapeout integration must supply the actual parent supply contacts, voltage and impedance. IHP and the integration owner must confirm the applicable operating and reliability limits. The project must evaluate the declared activity envelope and transient behavior. |
| Shuttle acceptance | Tiny Tapeout must accept the actual release artifact for the named shuttle and allocation. Jane Street must receive and select the entry for the competition-funded route. |

The [timing intake](streaming-8x4-hold-cap-timing-intake-20261114.md)
verifies the current PDK still exposes a legacy seven-layer OpenRCX model.
The [power intake](streaming-8x4-hold-cap-workload-power-20261114.md)
uses verified workloads on the frozen design and checks parent contact
evidence against exact Metal4 solver nodes. Full physical qualification
and the hosted receipts remain open. Fabrication remains **NO-GO**.
