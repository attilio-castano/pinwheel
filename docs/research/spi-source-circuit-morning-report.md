# SPI proof milestone: morning report

Session launched October 16, 2026 at 8:00:31 p.m. Eastern
(`2026-10-17 00:00:31 UTC`), with a twelve-hour maximum ending October 17
at 8:00:31 a.m. Eastern. Branch: `codex/spi-source-circuit-proof`.
Starting checkout: `a2bbdb122d2212ef0221fea6179ba83cc616eb9d`.

**Completed.** All required validation gates had passed by
`2026-10-17 01:08:06 UTC` (October 16, 9:08 p.m. Eastern), about 68 minutes
after launch. The session stopped after local closeout, well within its
twelve-hour maximum.

## Result and exact claim

The new `SpiRefinement.initialized_run` theorem connects the existing typed
SPI interpreter to the packed Reactive circuit and the actual initialized
digital SRAM state. The proof is checked by Lean 4.33.1 and is committed in
`9721a91` after incremental proof commits.

Previously the source/image interpreter and SRAM/register results ended at
different state representations. This theorem supplies that missing link for
the supported SPI family.

The theorem covers mode-0 SPI programs with one through four bytes and
half-periods of three through 256 clocks. From cold initialization, accepted
canonical source uploads, actual VALID and an admitted START, it establishes
the relation for every quiet input prefix and arbitrary raw input history
(`initialize = 0`, `command = 0`, other operands zero). Image equality,
source/circuit representation and matching pins are derived. An admitted START
may supply any 32-bit payload and TX/RX limits from zero through 32 bits; a
successful peer or fully provisioned transfer is not assumed.

The relation preserves pin levels/enables, virtual/physical execution
coordinates, nested loop counters and countdown, request identity and
generation, TX consumption and its complete shifted payload, RX prefix
packing, and retained completion or fault. It includes immediate empty-TX
fault, later TX underflow, RX overflow, release and HALT. The SRAM relation
retains both resident memory replicas and registered response invariants;
pin and buffer projections refer to the actual controller registers.

Three representation details matter:

- The source sampler is seeded with the actual START edge. Later receives
  consume the pre-edge second sampler stage.
- Hardware continues sampling after stopping; the stopped relation abstracts
  those sampler values while retaining pins, counters and owned results.
- A short logical TX request does not erase unused high bits of the physical
  shift register. The relation retains the original full payload as a ghost.

Independent review found no blocking issue in the theorem's assumptions,
START causality, RX sampling, retained-state abstraction or SRAM composition.

## Validation

The final whole-library build completed successfully (324 jobs). The axiom
audit checked 27,366 declarations and 14,992 theorems and accepted only
`propext`, `Classical.choice` and `Quot.sound`. An injected custom axiom was
rejected for the expected reason. No production proof uses `sorry`, a new
axiom or `native_decide`.

The focused SPI gate passed in 74.837 seconds with frozen inputs unchanged.
It compared 17,845 execution prefixes across ten cases, checked two ordinary
actual-circuit evaluation boundaries, rejected three independently mutated
states, and witnessed the START/stopped sampler and unused-high-TX-bit
distinctions. The Python regression suite passed (1,151 tests, six skipped)
in 50.316 seconds (50.88 seconds including the receipt wrapper).
The skipped checks require pinned Icarus/Yosys fixtures or Linux-specific
process observation; they do not supply RTL evidence for this milestone.

The full foundation gate passed in **1,982.932 seconds**: all **61 executable
suites**, one kernel suite, two independent Python oracles, the whole-library
audit and its injected-axiom rejection. All 322 production modules are reachable
from the default build. All 447 frozen source hashes still match the working
tree. The 68 recorded commands have their expected exit status, including the
one deliberate rejection. No focused, foundation or Python gate attempt failed.

Fresh local evidence directories:

- `build/validation/spi-source-circuit-focused-20261016-01/`
- `build/validation/spi-source-circuit-foundation-20261016-01/`
- `build/validation/spi-source-circuit-python-20261016-01/`

The focused gate freezes source files, audits the final theorem even if the
default import regresses, rejects an injected axiom, and compares separately
evaluated source and actual circuit equations with distinguishing mutation
controls. Verified receipt SHA-256 values:

| Receipt | SHA-256 |
| --- | --- |
| Focused SPI | `3ac844b6a767065fc26d1d88c6c20a4ba51eb417aa71db090dcbf01e593c2f19` |
| Full foundation | `d13e3118165d4e7800186793ebeed78513a35477a94ceac7029f21838d01f4df` |
| Python | `b05c9cafaab89c0355941a12e2b1c249c86be77092d1cea3182c8848b4c965cb` |

The focused receipt's 328 source hashes and eight artifact hashes were also
independently verified. Exploratory proof diagnostics are separate from these
accepted gate attempts; the retained probes are under `build/spi-proof-probes/`.

## Commits and review entry points

The local commit sequence records the plan, packing laws, initialized
geometry, interpreter transition equations, admitted source construction,
relation and held/countdown preservation, dispatch proofs, then initialized
composition. `9721a91` is the completed proof milestone; `5014bb2` adds the
passing focused gate, executable controls and foundation-suite registration.
`1720d63` records the proof scope and focused evidence; the final closeout
commit contains this report and the full foundation result.

- [The theorem](../../Pinwheel/Hardware/Buffered/SpiSimulation.lean)
- [State relation](../../Pinwheel/Hardware/Buffered/SpiRelation.lean)
- [Actual SRAM projections](../../Pinwheel/Hardware/Buffered/SpiSramRelation.lean)
- [Scope and reproduction](../protocols/buffered-spi-refinement.md)
- [Authorized session plan](spi-source-circuit-plan.md)

## Remaining gaps

This proves one admitted transfer followed by command-zero clocks at the
typed digital SRAM boundary. It does not compose serial packet delivery or
the repeated START/RELEASE/reset lifecycle. The universal Python compiler,
native emitter, emitted RTL and physical implementation remain separate
proof obligations. Reactive I²C execution still needs its own source/circuit
state relation. No analog timing, external-peer compliance or silicon result
is inferred from arbitrary raw digital inputs.

Existing source semantics, circuit definitions, RTL/ABI and historical
physical evidence are unchanged. This session runs no CAD and makes no
physical qualification claim. All commits and validation artifacts are
local; nothing was pushed or published. Ignored `build/` receipts remain
inspectable in this worktree, and the checked-in scripts reproduce them with
a fresh tag.

Reproduce the required gates with the pinned toolchain and Python 3.12+:

```sh
python3 -B scripts/check-buffered-spi-refinement.py --tag <fresh-spi-tag>
python3 -B scripts/check-foundation.py --tag <fresh-foundation-tag>
python3 -B -m unittest discover -s test -p 'test_*.py'
```
