# Physical validation of the general core

This milestone tests the 32-entry, dense, cached atomic core selected by the
[storage study](storage-study.md). Its pin/capture semantics and atomic loading
contract are unchanged. Physical implementation is separate evidence from the
Lean circuit proofs and independent RTL simulations.

## Target and upstream pins

`tools/physical-toolchain.json` records the inspected upstream identities:

- Tiny Tapeout CMOS5L template: `b86a2a781484bcab7ba522dc5de540086695a430`.
- GDS action: `3412659307918422f3f0727917cf9b499aaca588`.
- CMOS5L support tools: `da63c9927411e3aca350977d653d24bbf5bca972`.
- LibreLane: `3.1.0.dev3`, with the ARM64 container manifest digest pinned.
- IHP Open PDK: `2bbec755dc67ca3db0261c3d6163e15735d66710`, selected by the action.

> **Update 2026-09-18.** The announcement now sets the maximum at 6×4 tiles, so
> the rectangle below is the official die area, and the official 6×4 template
> is in the pinned files ([brief](competition.md#the-outline-and-the-pinned-files)).
> The rest of this section is kept as written, when the announcement said 8×4.
> Still true: these runs do not apply the template's pins.

The [competition](https://blog.janestreet.com/protocol-emulator-asic-competition/)
specifies 8×4 tiles. The pinned
[CMOS5L tile table](https://github.com/TinyTapeout/tt-support-tools/blob/da63c9927411e3aca350977d653d24bbf5bca972/tech/ihp-sg13cmos5l/tile_sizes.yaml)
and DEF inventory have no 8×4 entry. This is an actual support-file gap, beyond
the stale size comment previously recorded in the template. No 8×4 floorplan is
invented or represented as approved here.

The diagnostic uses the supported **6×4 dimensions, 1,289.28 × 710.64 µm**,
as a standalone core rectangle. It does not apply the Tiny Tapeout DEF pin
template: all internal word-loader and diagnostic ports remain exposed and
observable. No functional input is tied off and no output is discarded to shrink
the core. This is a conservative area experiment in a smaller rectangle, not a
Tiny Tapeout submission or a validation of the eventual external pin interface.

The external serial loader, asynchronous input conditioning, pin multiplexing,
and final wrapper still need space and timing budgets. This run does not validate
their behavior or cost. In particular, its synchronous input constraints do not
establish metastability safety or external UART/SPI/I²C electrical timing.

## Experiment constraints

`physical/core.json` starts from the template's 20 ns clock target (50 MHz), uses
the same Metal4 signal-routing ceiling and narrow floorplan margins, and sets a
70% placement-density target to leave room above the previous cell-area estimate.
The density target is not a measured final utilization. Power distribution and
clock-tree synthesis remain enabled. The template's KLayout DRC/XOR exclusions
remain explicit; a flow completion must not be called comprehensive sign-off.

`physical/core.sdc` constrains every nonclock input, including synchronous reset
and initialization, without false-path exceptions:

| Constraint | Experiment assumption |
|---|---|
| Clock period | 20 ns |
| Input delay | 0.2 ns minimum, 4 ns maximum |
| Output delay | 0.2 ns minimum, 4 ns maximum |
| Input driver | `sg13cmos5l_buf_2/X` |
| Output load | 10 fF |
| Clock uncertainty | 0.2 ns |
| Ideal clock transition | 0.15 ns; physical clock propagated after CTS |

These are explicit core integration budgets, not measured board characteristics.
The initial run tests one clock target; it is not a search for maximum frequency.
The configured corners are typical 1.20 V/25 °C, fast 1.32 V/−40 °C, and slow 1.08 V/125 °C. `TIMING_VIOLATION_CORNERS` is explicitly set to all corners; the PDK default checks only typical-corner violations. Unlike the
earlier independent typical/slow mappings, physical STA must analyze the same
implemented netlist across its corners.

## Input provenance

With the pinned Lean toolchain on PATH:

```sh
python3 scripts/prepare-physical.py
```

The script regenerates the general candidate from Lean, exports SystemVerilog,
and requires its SHA-256 to match the successful storage-study RTL receipt. It
copies the physical configuration and SDC into `build/physical/core/`, and records
current source and input hashes in `inputs.json`. This prevents silently measuring
a different circuit. Large tools, PDK views, and flow artifacts stay in ignored
`build/physical/`.

The digital PDK installer verifies 544 files and links against the pinned Git
blob inventory, including transitive symlink dependencies. It excludes unrelated
analog PyCell submodules and unused SRAM views. The typical and slow standard-cell
Liberty files match the earlier study byte for byte; the physical flow adds fast
corner, geometry, routing, and extraction views.

With Docker Desktop running, the normal container installation is:

```sh
docker pull ghcr.io/librelane/librelane@sha256:32244c826f512166840284332874bd9c26e5fd780b11cf23076c5dae8e2c3e04
docker tag ghcr.io/librelane/librelane@sha256:32244c826f512166840284332874bd9c26e5fd780b11cf23076c5dae8e2c3e04 ghcr.io/librelane/librelane:3.1.0.dev3
python3 scripts/install-physical-pdk.py
python3 scripts/prepare-physical.py
python3 scripts/run-physical.py --tag initial
```

The default attempt limit is 3,600 seconds (`--timeout-seconds` overrides it).
On timeout, the runner atomically saves exit code 124 and `wall_time_limit`
before cleanup. It records container termination separately: `stopped`,
`absent`, or `unconfirmed`. Cleanup allows up to 30 seconds for the stop command
and, if needed, 10 seconds to query the daemon. A failed query never establishes
absence. Reporting refuses timed-out runs whose termination is unconfirmed,
including older timeout receipts without termination evidence; their existing
historical reports remain unchanged. Cleanup errors remain in the invocation
receipt for diagnosis. Tests exercise these paths with mocked Docker calls.

The runner checks the ARM64 image's uncompressed layer identities and runtime
configuration. Docker's containerd store can assign a different manifest digest
when importing a verified archive; that alone is not a filesystem change. The
initial installation used verified host-side downloads and archive import after
Docker registry requests timed out.

Runs have unique tags, preserve inputs and logs, and execute with networking
disabled, four CPUs, four explicit OpenROAD threads, a 6 GiB memory limit, and the
PDK mounted read-only. A separate
input snapshot is retained for each run. The initial run was launched before
snapshot support was added; its matching inputs are archived under
`build/physical/core/experiments/initial/`.

The initial run was deliberately stopped during detailed routing because the
null `OPENROAD_THREADS` default resulted in one thread despite the four-CPU
container allocation. `routed4` resumes the completed global-routing/STA checkpoint
with four threads; that is its only configuration change. No timing or area
requirement was relaxed. Resume with an explicit checkpoint when needed:

```sh
python3 scripts/physical_checkpoint.py capture --state build/physical/core/runs/initial/43-openroad-stamidpnr-3/state_out.json --manifest build/physical/core/initial-midpnr-checkpoint.json
python3 scripts/run-physical.py --tag new-resume --from-step OpenROAD.DetailedRouting --state build/physical/core/runs/initial/43-openroad-stamidpnr-3/state_out.json --checkpoint-manifest build/physical/core/initial-midpnr-checkpoint.json
python3 scripts/report-physical.py --tag new-resume
```

Capture the manifest when preserving a checkpoint. It records the JSON and every
referenced artifact, including nested corner views. Capture refuses to overwrite
an existing manifest. Missing or changed files make resume fail before Docker is
invoked. The runner copies and verifies those contents into the new experiment's
checkpoint directory, rewrites artifact paths to those copies, and mounts that
directory read-only for LibreLane. The invocation and collected report identify
the manifest and rewritten state; source file edits after copying cannot change
the snapshot consumed by the flow. This protects against accidental source edits,
not a host deliberately modifying the snapshot or its manifest during execution.

For legacy checkpoints, capture describes contents observed **now**, not verified
contents at the time of an earlier run. Existing historical receipts are not
retroactively upgraded. Do not recapture changed files to make a failed resume
pass under the old identity. A new manifest represents a new observed checkpoint.

The portable checkpoint regression uses disposable files and mocked Docker calls:

```sh
python3 -B -m unittest discover -s test -p 'test_physical_checkpoint.py'
```

It covers changed/missing artifacts, nested views, state edits, manifest
completeness, snapshot isolation, repeated resumes, and rejection before launch.
It does not run or establish a new physical measurement.

The collector requires a completed invocation, preserves failure status, and
identifies whether detailed routing and extracted multi-corner STA completed.
Intermediate flow states inherit older metrics; fast/slow figures from an early
step must not be presented as current after a typical-only timing update.

The zero-delay functional check can be applied to a synthesized or routed netlist:

```sh
python3 scripts/check-physical-netlist.py path/to/netlist.v --label synthesis
```

It checks existing independent atomic/protocol vectors and compares every defined
source-RTL output bit before and after each edge. Reference-X bits from
uninitialized storage are excluded. A deliberately inverted output must fail.
This does not perform delay-annotated simulation or prove universal equivalence.
The default LibreLane EQY step does not support this PDK; it is not silently
counted as a passing formal check.

## Implementation cost

The `initial` run completed synthesis, placement, clock-tree synthesis, timing
repair, and global routing. Its usable core is **902,417 µm²**, inside the
**916,214 µm²** diagnostic rectangle. Completed stages show why mapped cell area
alone was insufficient:

| Stage | Cell area | Cells | Core utilization |
|---|---:|---:|---:|
| Physical-flow synthesis | 579,144 µm² | 33,446 | — |
| After post-CTS timing repair | 735,199 µm² | 45,615 | 81.47% |
| After global-routing antenna repair | 736,167 µm² | 45,793 | 81.58% |
| After detailed routing and antenna repair | 736,821 µm² | 45,913 | 81.65% |

Filler insertion subsequently reports 902,417 µm² and 76,249 instances because
fill cells occupy the remaining rows. That filled area must not be mistaken for
functional-cell demand; the pre-fill utilization above is the useful comparison.

The synthesis figure differs from the storage study's 561,587 µm² because this
experiment uses a different pinned tool flow and full timing boundary; it is not
a changed Lean circuit. This is not a paired routed-area comparison with the
64-entry reference, which has not been routed.

Post-CTS repair inserted **3,959 hold buffers**, as well as 26 setup buffers and
182 cell upsizes. The initial worst setup path ran from `incoming[1]`, through
branch/successor selection, into the cached instruction. Hold repair retains the
template's extra 0.1 ns margin and the stated minimum I/O delays. Its cost is
conditional on those integration assumptions. The cache saves lookup work on
ordinary cycles but does not remove the input-dependent successor path.

The earlier synthesized netlist passed **21,409 atomic/protocol edges and
3,510,998 defined output-bit comparisons**; the inverted-output mutant was
rejected. This is functional evidence before physical implementation, recorded
in `build/physical/synthesis-check/report.json`.

## Routed timing and functional result

`routed4` completed detailed routing with **zero routing DRC errors and zero
remaining antenna violations**, after three diode-repair passes. Extracted STA
analyzes the same implemented netlist at all three PVT corners, using nominal RC
rules inherited by the pinned CMOS5L PDK. Separate best/worst RC corners were not
measured.

| Corner | Worst setup slack | Worst hold slack |
|---|---:|---:|
| Fast, 1.32 V / −40 °C | +7.020 ns | +0.0417 ns |
| Typical, 1.20 V / 25 °C | +2.184 ns | +0.1141 ns |
| Slow, 1.08 V / 125 °C | **−6.254 ns** | +0.2753 ns |

At the **20 ns target**, there are **112 setup-violating endpoints** in the slow
corner and no hold violations. The worst path remains `incoming[1]` to
`r_cached_word[49]` through successor selection and storage lookup. The design
therefore **does not close 50 MHz across the measured PVT corners**.

The electrical checks also report 48 slow-corner slew violations, up to nine
capacitance violations per corner, and 443 fanout violations against the Liberty
default maximum of eight loads. Of these, 413 are clock-buffer violations.
The synthesis configuration's fanout target is ten; the custom final SDC does
not override the library limit. Relaxing the clock alone would not fix these violations;
subtracting the setup shortfall from a clock-frequency estimate would not produce
a qualified operating frequency. `check_setup` reported no missing-clock,
missing-input-delay, unconstrained-endpoint, or combinational-loop warnings.
The flow reports 336 raw unannotated drivers and zero after its filtering.

The implemented, filled netlist passed **21,409 atomic/protocol edges and
3,510,998 defined output-bit comparisons**, and the inverted-output mutant was
rejected again. Its SHA-256 is
`ee71ab6ea567c5d7fa92e8f18bce2177960a33a34faf5356d5b14b097d31caea`;
the receipt is `build/physical/routed-check/report.json`. This preserves the
functional evidence after cell sizing, buffer insertion, clock-tree creation,
and antenna repair. It remains a zero-delay simulation, not a translation proof
or a substitute for timing closure.

## Completed physical checks

The resumed flow reached its final manufacturability report and saved final
views, then exited with **code 2 because of the slow-corner setup failure**.
This was a completed measurement with a rejected timing target, not an
interrupted physical run. The collector preserves that failure in
`build/physical/routed4-report.json`.

| Check | Result |
|---|---|
| Detailed-router DRC | 0 errors |
| Post-route antenna check | 0 violating nets or pins |
| Magic full DRC on final GDS | 0 errors |
| Netgen layout versus netlist | Circuits match uniquely; 0 errors |
| Hold timing, all three PVT corners | Pass |
| Setup timing, all three PVT corners | Fail at slow corner |
| Slew / capacitance / fanout | Violations remain, as recorded above |

Magic checked and extracted the KLayout-streamed GDS with SHA-256
`e1467f2ceb8fb55f0a2130847419b84a8ece726f069b7736183bebf28dde92c3`.
The final flow netlist is byte-identical to the netlist used by the successful
implemented-netlist regression. The independent Magic scan took about half an
hour; the resumed flow took approximately 65 minutes in the stated local
container allocation. Its layout image is
`build/physical/core/runs/routed4/16-klayout-render/pinwheel_atomic_small_dense_cached.png`.

These checks are bounded by the pinned decks and enabled flow stages. KLayout
DRC, cross-tool GDS XOR, and formal EQY were disabled; the long-wire threshold
check was skipped because no threshold was configured. OpenROAD warned that
some LEF58 enclosure forms were unsupported. The IR-drop report uses default
source assumptions without explicit supply-source locations, so it does not
qualify the eventual chip power network. The flow treats slew/capacitance
violations as warnings; their presence remains a closure failure even though
the final exit message names setup timing alone.

## Follow-up sequence at baseline closeout

The sequence below records the original follow-up plan. Its flow controls and two
architectural screens are now completed in the [successor-fetch study](successor-fetch-study.md).
[Research status](research/status.md) owns the current allocation; do not restart
these experiments from this historical plan.

Preserve this run as the first physical baseline. Before altering the machine's
observable schedule, investigate the implementation flow:

1. Align synthesis fanout and clock-leaf clustering with the library's effective
   limit. Account for the resulting clock-tree area and hold effects.
2. Enable and measure design/timing repair after global routing, with all three
   corners and the same 20 ns/I/O constraints. This baseline leaves those two
   post-global-route repair stages disabled. Post-CTS repair already loaded all
   three timing corners; merely adding a slow library is not the missing step.
3. Repeat routing, extraction, electrical checks, layout checks, and the final
   netlist regression. Compare cell area and the same worst successor path.
4. If that path still dominates, compare implementations that reduce lookup or
   selection delay. Any extra execution cycle requires a revised Lean timing
   contract and correspondence proof before it can replace this core.

The official 8×4 floorplan and external pin/loader budget remain separate
integration gates. These measurements provide a concrete route to the next
experiment; they do not establish a maximum frequency or a tapeout-ready chip.

## Acceptance boundary

Record actual core area/utilization, routing completion and violations, clock
tree cost, extracted-parasitic setup/hold results, constrained-path coverage,
antenna/physical checks, and the identity of the final netlist/layout. Preserve
failed runs and their causes. Verify functional behavior after implementation
where supported, and distinguish that check from a proof of the Lean-to-RTL
translator. A routed timing result remains conditional on the stated PDK and
boundary constraints; eventual silicon validation is separate.
