# Competition brief

Announcement rechecked **2026-11-14**. The November 9 organizer update
confirms 8×4 for the March 2027 CMOS5L shuttle. The current Verilog template
targets CMOS5L from `main`. The September inventory below records the earlier
6×4 phase. [Official announcement and FAQ](https://blog.janestreet.com/protocol-emulator-asic-competition/) ·
[Pinwheel entry draft](jane-street-8x4-entry.md)

Jane Street asks for a public repository with RTL, tests, a passing Tiny
Tapeout GDS and precheck, architecture and instruction documentation,
toolchain and example programs, and a verification write-up. The FAQ
allows the Tiny Tapeout custom-GDS action for designs that exceed hosted
hardening time and recommends gate-level simulation. The public
submission deadline is January 18, 2027. [Submission and judging](https://blog.janestreet.com/protocol-emulator-asic-competition/#submission-and-judging)

## Official challenge and rules

Primary authority: [Jane Street's announcement](https://blog.janestreet.com/protocol-emulator-asic-competition/), published September 10, 2026, by Benjamin Devlin and Anish Singhani.

Build an open-source protocol-emulator ASIC with programmable pin control and precise timing. It must support new protocols after fabrication within its timing and I/O limits.

| Item | Announced position |
| --- | --- |
| Process | IHP 130 nm CMOS5L through Tiny Tapeout |
| Starting point | CMOS5L Verilog template on `main` with `info.yaml` tile size `8x4` |
| Area | Maximum 8×4 = 32 tiles, confirmed for the March 2027 shuttle |
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
- Synthesize early; verify routed timing and area. A design that looks small enough after synthesis can still be hard to route or too slow.
- For instruction memory, SRAM can be more area-efficient than flip-flops; Tiny Tapeout has SRAM examples on this process. Pinwheel's position is in the [storage study](storage/storage-study.md) and the [primitive review](storage-primitives.md).

Formal verification is welcomed, not required. Lean is Pinwheel's selected specification and modeling language; it is not an organizer requirement. The [architecture plan](architecture.md) records our design choices separately from the competition rules.

Final submission form: forthcoming. Questions: `asic-competition@janestreet.com`.

## Primary resources

The following resources are linked directly from the announcement.

| Resource | Why keep it here |
| --- | --- |
| [CMOS5L Verilog template](https://github.com/TinyTapeout/ttihp-verilog-template/tree/main) | Starting repository for the RTL-to-GDS flow. Its README describes `src/`, `test/`, `docs/info.md`, and LibreLane automation. |
| [Tiny Tapeout](https://www.tinytapeout.com/) | Official entry point for HDL guides, testing, technical specifications, and fabrication documentation. |
| [SRAM example: 1024×8 test](https://www.tinytapeout.com/chips/ttihp0p2/tt_um_urish_sram_test) | Foundry SRAM macro example with controller description, pin mapping, test instructions, and a linked implementation repository. |
| [Hardcaml](https://hardcaml.org/) | OCaml hardware design and testing library linked by the organizers. Pinwheel's [UART experiment plan](history/uart-experiment.md) explores Lean specifications and a proposed Lean-to-CIRCT hardware generation path. |
| [Competition update form](https://docs.google.com/forms/d/e/1FAIpQLSeF7fq756MegxZRQxotBwUJYZx-cL9MrGjxV0z4uD_J0sADxQ/viewform) | Receives deadline, template, and submission-form updates. Signing up neither commits participation nor enters the competition. |

The template provides [project configuration](https://github.com/TinyTapeout/ttihp-verilog-template/blob/main/info.yaml) and [testbench instructions](https://github.com/TinyTapeout/ttihp-verilog-template/blob/main/test/README.md).

## The outline and the pinned files

Checked 2026-09-18 against support commit
`da63c9927411e3aca350977d653d24bbf5bca972`, the one recorded in
`tools/physical-toolchain.json`.

- The September CMOS5L tile table listed the official `6x4` rectangle of
  **1,289.28 × 710.64 µm** used by the early Pinwheel routing studies.
- The official floorplan template is in the same commit:
  `tech/ihp-sg13cmos5l/def/tt_block_6x4_pgvdd.def` (SHA-256
  `b46d9a0ee8352160e48dbc8312f092f985629061df736c7f46d58686535a76f4`). It fixes 186 placement rows of 2,674 sites (a core of
  902,417 µm², the same core area as the routed runs report) and **43 pins, all
  on Metal4 on the top edge between x = 29.76 and 191.04 µm** — the top-left
  corner, 3.84 µm apart — plus the `VPWR`/`VGND` nets. The routed runs so far
  did not apply this template: their 200-odd stand-in ports were placed by the
  tool around the edge. This describes the historical core runs; the later
  [whole-chip SRAM experiment](chip-physical-study.md) now applies the template.
- The September tile table and DEF inventory omitted `8x4`. The current
  [8×4 allocation receipt](../physical/streaming_8x4/allocation.json) identifies
  the template used for the frozen candidate.

Consequences for Pinwheel are recorded in
[status](research/status.md#the-official-outline-2026-09-18).

## Open project questions

These are questions for the broader Pinwheel project, not additional competition rules. The bounded first experiment is described in [the UART plan](history/uart-experiment.md).

- What use case and distinctive capability should guide the design?
- Which protocol roles and speeds should the first demonstrator support?
- What architecture, memory organization, and hardware backend suit that scope, with Lean as the specification and modeling foundation?
- What evidence will demonstrate functional correctness, timing, and physical feasibility?
- What team, hardware, compute resources, and schedule are available?

Keep future project decisions separate from the external requirements above, with their rationale and supporting evidence.
