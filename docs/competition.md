# Competition brief

Announcement rechecked: **2026-09-19**; template inventory checked 2026-09-18 (first read 2026-09-12). This is a curated summary, not an archived copy. Linked pages and branches can change; recheck them before implementation and submission.

**Changed since the first read:** the announcement first asked for `8x4` tiles (32 tiles, about 1 mm²). It now sets the maximum at `6x4`; see [the outline](#the-outline-and-the-pinned-files) below.

## Official challenge and rules

Primary authority: [Jane Street's announcement](https://blog.janestreet.com/protocol-emulator-asic-competition/), published September 10, 2026, by Benjamin Devlin and Anish Singhani.

Build an open-source protocol-emulator ASIC with programmable pin control and precise timing. It must support new protocols after fabrication within its timing and I/O limits.

| Item | Announced position |
| --- | --- |
| Process | IHP 130 nm CMOS5L through Tiny Tapeout |
| Starting point | Linked CMOS5L Verilog template; set `info.yaml` tile size to `6x4` |
| Area | Current maximum: 6×4 = 24 tiles, about 0.7 mm² of nominal tile area (about 200 × 150 µm per tile); the organizers suggest budgeting about 1,000 logic cells per tile. They are working on the possibility of 8×4 (about 30% more area) and will update the page and email sign-ups if it becomes available |
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
| [CMOS5L Verilog template](https://github.com/TinyTapeout/ttihp-verilog-template/tree/cmos5l) | Starting repository for the RTL-to-GDS flow. Its README describes `src/`, `test/`, `docs/info.md`, and LibreLane automation. Preserve the explicit `cmos5l` branch when following this link. |
| [Tiny Tapeout](https://www.tinytapeout.com/) | Official entry point for HDL guides, testing, technical specifications, and fabrication documentation. |
| [SRAM example: 1024×8 test](https://www.tinytapeout.com/chips/ttihp0p2/tt_um_urish_sram_test) | Foundry SRAM macro example with controller description, pin mapping, test instructions, and a linked implementation repository. |
| [Hardcaml](https://hardcaml.org/) | OCaml hardware design and testing library linked by the organizers. Pinwheel's [UART experiment plan](history/uart-experiment.md) explores Lean specifications and a proposed Lean-to-CIRCT hardware generation path. |
| [Competition update form](https://docs.google.com/forms/d/e/1FAIpQLSeF7fq756MegxZRQxotBwUJYZx-cL9MrGjxV0z4uD_J0sADxQ/viewform) | Receives deadline, template, and submission-form updates. Signing up neither commits participation nor enters the competition. |

Useful next reading within the template: [project configuration](https://github.com/TinyTapeout/ttihp-verilog-template/blob/cmos5l/info.yaml) and [testbench instructions](https://github.com/TinyTapeout/ttihp-verilog-template/blob/cmos5l/test/README.md).

## The outline and the pinned files

Checked 2026-09-18 against support commit
`da63c9927411e3aca350977d653d24bbf5bca972`, the one recorded in
`tools/physical-toolchain.json`.

- The CMOS5L tile table has a `6x4` entry: **1,289.28 × 710.64 µm**. This is the
  rectangle every Pinwheel routed run has used, so those runs were made on the
  official die area, not on a stand-in for a larger one.
- The official floorplan template is in the same commit:
  `tech/ihp-sg13cmos5l/def/tt_block_6x4_pgvdd.def` (SHA-256
  `b46d9a0ee8352160e48dbc8312f092f985629061df736c7f46d58686535a76f4`). It fixes 186 placement rows of 2,674 sites (a core of
  902,417 µm², the same core area as the routed runs report) and **43 pins, all
  on Metal4 on the top edge between x = 29.76 and 191.04 µm** — the top-left
  corner, 3.84 µm apart — plus the `VPWR`/`VGND` nets. The routed runs so far
  did not apply this template: their 200-odd stand-in ports were placed by the
  tool around the edge. This describes the historical core runs; the later
  [whole-chip SRAM experiment](chip-physical-study.md) now applies the template.
- `8x4` is absent from the tile table and the DEF inventory, which matches the
  announcement: it is a possibility, not an allocation. The template's
  `info.yaml` comment listing valid sizes stops at `8x2` and is stale.

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
