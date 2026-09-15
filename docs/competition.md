# Competition brief

Sources checked: **2026-09-12**. This is a curated summary, not an archived copy. Linked pages and branches can change; recheck them before implementation and submission.

## Official challenge and rules

Primary authority: [Jane Street's announcement](https://blog.janestreet.com/protocol-emulator-asic-competition/), published September 10, 2026, by Benjamin Devlin and Anish Singhani.

Build an open-source protocol-emulator ASIC with programmable pin control and precise timing. It must support new protocols after fabrication within its timing and I/O limits.

| Item | Announced position |
| --- | --- |
| Process | IHP 130 nm CMOS5L through Tiny Tapeout |
| Starting point | Linked CMOS5L Verilog template; set `info.yaml` tile size to `8x4` |
| Area | Planned maximum: 32 tiles, approximately 1 mm² nominal area |
| Licensing | Submission must be open source |
| Deadline | January 18, 2027 |
| Prize | Selected designs receive funded fabrication, chips, and development boards |
| Shuttle | Target: March 2027, subject to foundry scheduling |

## Organizer guidance

These are suggestions and stated interests, not Pinwheel commitments. Source: [announcement](https://blog.janestreet.com/protocol-emulator-asic-competition/).

- Begin with UART, SPI, and I²C; stretch to low-speed USB or 10 Mbit Ethernet. Other ideas: JTAG, SWD, PS/2, CAN.
- Study RP2040 PIO and TI Sitara PRU architectures.
- Teams and FPGA prototyping are encouraged.
- Novel functionality and design/verification methods matter; formal, constrained-random, and AI-assisted verification are welcomed.
- Synthesize early; verify routed timing and area.

Formal verification is welcomed, not required. Lean is Pinwheel's selected specification and modeling language; it is not an organizer requirement. The [architecture plan](architecture.md) records our design choices separately from the competition rules.

Final submission form: forthcoming. Questions: `asic-competition@janestreet.com`.

## Primary resources

The following resources are linked directly from the announcement.

| Resource | Why keep it here |
| --- | --- |
| [CMOS5L Verilog template](https://github.com/TinyTapeout/ttihp-verilog-template/tree/cmos5l) | Starting repository for the RTL-to-GDS flow. Its README describes `src/`, `test/`, `docs/info.md`, and LibreLane automation. Preserve the explicit `cmos5l` branch when following this link. |
| [Tiny Tapeout](https://www.tinytapeout.com/) | Official entry point for HDL guides, testing, technical specifications, and fabrication documentation. |
| [SRAM example: 1024×8 test](https://www.tinytapeout.com/chips/ttihp0p2/tt_um_urish_sram_test) | Foundry SRAM macro example with controller description, pin mapping, test instructions, and a linked implementation repository. |
| [Hardcaml](https://hardcaml.org/) | OCaml hardware design and testing library linked by the organizers. Pinwheel's [UART experiment plan](uart-experiment.md) explores Lean specifications and a proposed Lean-to-CIRCT hardware generation path. |
| [Competition update form](https://docs.google.com/forms/d/e/1FAIpQLSeF7fq756MegxZRQxotBwUJYZx-cL9MrGjxV0z4uD_J0sADxQ/viewform) | Receives deadline, template, and submission-form updates. Signing up neither commits participation nor enters the competition. |

Useful next reading within the template: [project configuration](https://github.com/TinyTapeout/ttihp-verilog-template/blob/cmos5l/info.yaml) and [testbench instructions](https://github.com/TinyTapeout/ttihp-verilog-template/blob/cmos5l/test/README.md).

## Source discrepancy to resolve during setup

The [template configuration](https://github.com/TinyTapeout/ttihp-verilog-template/blob/cmos5l/info.yaml), as checked above, defaults to `1x1`; its comment listing valid sizes stops at `8x2` and omits `8x4`.

Treat the announcement as the competition's authority. The later [physical-flow
inspection](physical-validation.md#target-and-upstream-pins) checks support commit
`da63c9927411e3aca350977d653d24bbf5bca972`: its CMOS5L tile table and DEF inventory
also lack 8×4, so this is more than a stale template comment. The core experiment
uses a smaller supported 6×4 rectangle, with a separate internal-port boundary.
It does not establish an accepted competition allocation or final pin-interface
fit. The announced 8×4 integration remains unresolved.

## Open project questions

These are questions for the broader Pinwheel project, not additional competition rules. The bounded first experiment is described in [the UART plan](uart-experiment.md).

- What use case and distinctive capability should guide the design?
- Which protocol roles and speeds should the first demonstrator support?
- What architecture, memory organization, and hardware backend suit that scope, with Lean as the specification and modeling foundation?
- What evidence will demonstrate functional correctness, timing, and physical feasibility?
- What team, hardware, compute resources, and schedule are available?

Keep future project decisions separate from the external requirements above, with their rationale and supporting evidence.
