# Approved reactivation: close the Tiny Tapeout candidate

The user approved this plan after clarifying that the preceding request was
for a proposal. Work was paused and owned proof/CAD and keep-awake processes
were confirmed absent before this approval. The earlier local changes and
receipts remain preserved; they are useful starting evidence, not a completed
campaign. The saved goal still contains the preceding expired timestamps;
this user-approved window supersedes those timestamps for resumed work.

Launch: **2026-10-18 15:26:07 UTC** (11:26 a.m. Eastern).
Maximum deadline: **2026-10-19 03:26:07 UTC** (11:26 p.m. Eastern).
Stop admitting new candidate CAD: **2026-10-19 00:26:07 UTC**.
Starting committed HEAD: `1c217d1` on `codex/streaming-tt-candidate`.

## Outcome and acceptance

Close a fully routed, standard-cell-only **6×4, depth-two, 20 ns** candidate
with kernel correspondence through its actual implemented netlist. Preserve
all 6,039 semantic state bits, the 64×64 program bank, two-word TX/RX queues,
SPI 4 KiB duplex streaming, 4,097-bit JTAG, 64-byte reactive I²C, autonomous
single-frame UART and the host contract. Numeric synthesized FF names may
change with combinational emission; a fresh complete semantic-to-actual state
map is required. Capacity or behavior cannot change to manufacture closure.

Acceptance requires completed detailed routing; declared-corner extracted
setup/hold and electrical checks with justified CMOS5L RC models; power
connectivity; DRC, LVS and antenna results; applicable unchanged official TT
precheck; actual final-netlist public-wire diagnostics; complete required
kernel roots; and public/private axiom auditing. Missing, failed, unsupported
or waived checks remain gaps. A nominal RC timing estimate is not qualified
extracted timing. Full tapeout readiness is not claimed while a mandatory gate
is open. Twelve hours is a maximum budget, not a completion guarantee.

## Approved execution allocation

1. **First two hours:** finish the balanced guard integration, prove exact
   equivalence, and replay source checks from a fresh committed snapshot.
   Test critical affected modules before spending a full-library replay.
2. **Next five hours:** pursue placement, CTS and complete detailed routing
   using the corrected power grid. Address measured timing/congestion causes;
   admit each new candidate with exact source, tool, PDK and input identities.
3. **Next two hours:** finish correspondence to actual implementation changes,
   and run timing, electrical, power-connectivity and layout checks. Work on
   general proof scalability while waiting for the final physical database.
4. **Last three hours:** stop new candidate experiments, validate committed
   sources and complete mandatory checks where possible, review independently,
   retain immutable receipts and produce a reproducible final report with
   exact remaining obligations. Stop owned jobs at the deadline.

Only one heavy proof/CAD process tree may run at once. Parallel agents perform
host preparation and review. Native Lean is serial and bounded; default full
source replay is 4 GiB, smaller probes use less. CAD is at most four CPUs and
6 GiB with swap disabled. Enforce resource admission, host-memory/disk floors,
wall-time alarms, owned cleanup and frequent local checkpoints. A bounded
keep-awake assertion changes no system settings and cannot prevent a restart.
The candidate admission cutoff applies to new candidate experiments. Native
checks on an explicitly hash-bound existing parent can use `cad-validation`
during the final three hours, with the same container, resource and cleanup
requirements and the unchanged hard campaign deadline.

Local implementation, bounded proof/CAD work, incremental local commits and
reporting are approved. Paid services, external messages, shared-PDK changes,
pushes, PRs, publication and fabrication submission remain outside scope.
The two intake-dirty documents and every historical evidence artifact stay
byte-identical as specified in the preceding campaign record.

## Verified starting evidence and its limits

- The isolated PDN fixture now has a fully closed native receipt and passes
  the unchanged official pin checker. Its 52 full-height Metal4 power stripes
  clear every fixed public pin by at least 640 DBU. This fixture does not prove
  candidate routing, power connectivity, timing, DRC or LVS.
- The old global-route implementation's complete 90-module clock scope now
  closes at a bounded memory cost. The rest of that old proof family, its
  aggregate axiom audit and compatibility obligations remain separate.
- The generic 64-leaf balanced conjunction has a Native Lean kernel proof.
  Integration into both streaming cores/frontend, a fresh source replay,
  mapped state identity, new candidate correspondence and timing measurement
  are still required. Old compiled objects cannot silently certify changed
  declarations bearing the same names.

Starting receipts:
`build/streaming-physical-development/pdn-clearance-unqualified-02/report.json`,
`build/streaming-physical-development/clock-scope-renewal-closeout-unqualified-01/report.json`,
`build/streaming-tt-recovery/renewal-balanced-helper-07/report.json`.
These paths are local retained evidence, not remote publication.

References: [preceding campaign record](streaming-tt-closure-campaign-20261018.md),
[previous morning report](streaming-tt-morning-report.md), and
[extraction-model scope](streaming-tt-extraction-scope.md).
