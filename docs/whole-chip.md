# The whole chip in Lean

Status: **experimental top level, proved in Lean from a host's serial session to
a running program; emitted; the emitted RTL has not been simulated or routed yet.**

## Question

Every physical result so far is about the core alone, on a test rectangle, with
its 67-wire loader port and about 130 observation wires exposed as if they were
pins, and with assumed arrival times at those stand-in pins. The chip the
competition asks for has 24 user pins, a clock and a reset. What is between the
two, and can the Lean specification cover it — so that the object we place and
route is the object the theorems are about?

## The stack

| Layer | What it is | Lean | Status |
| --- | --- | --- | --- |
| Protocols | UART, SPI, I²C as pin-level contracts | `UART/`, `SPI/`, `I2C/` | proved |
| Compilers | requests to engine programs | `Compile/` | proved against the protocols |
| Engine and records | the reactive engine, 64-bit records, images | `Engine/`, `Binary/`, `Hardware/Execution/` | proved |
| Reference machine | atomic loader, scheduler, two program banks | `Hardware/Loader/` | proved |
| Core backends | dense storage, cached word, fetch policies | `Hardware/Storage/` | proved to refine the reference, edge for edge |
| **Serial loader** | three pins in place of the 67-wire port | `Hardware/Serial/` | **new: proved** |
| **Pin samplers** | two registers on every input | `Hardware/Feeder.lean` | **new: generic, proved** |
| **Pin map and output map** | Tiny Tapeout's ports | `Hardware/Chip.lean` | **new: proved** |
| **Upload theorem** | "this session leaves this program running" | `Hardware/Loader/Upload.lean`, `Program.lean`, `Storage/ProgramUpload.lean`, `ChipUpload.lean` | **new: proved** |
| Emitted RTL of the chip | `tt_um_pinwheel` | `test/ChipEmit.lean` | emitted and mapped; not simulated |
| Routed chip | official 8×4 outline | — | not started; the outline is not in the pinned Tiny Tapeout files |

## Feeders

A layer in front of a netlist's inputs is a `Feeder`: for each inner input an
expression, and for each of the layer's own registers a next-state expression,
over the outer inputs and the layer's registers only. `Feeder.wrap` rewires any
inner netlist behind it, reusing its expressions unchanged.

One theorem covers every layer and every inner netlist (`Feeder.wrap_pairTrace`,
and `Feeder.Model.pairTrace_eq` on records): behind a feeder, a netlist takes
exactly the edges it would take on the *fed* history — none added, removed or
reordered. Structural timing passes through the same way
(`wrap_arrivalNext`), and a feeder whose inner inputs all come from its own
registers shields whatever is behind it from the outer inputs
(`wrap_shields`). The two-register sampler of every input (`Feeder.sampler`) and
the serial receiver are instances; layers compose by nesting. An output map
(`Netlist.mapOutputs`) is the same idea on the output side, without state.

## The serial loader

Three pins, SPI mode 0 as seen from the host: `sck`, `mosi`, `csn`. A frame is
72 bits while `csn` is low: one command byte (its low three bits are the
loader's command; 7 is the core's `reset` input), then the 64-bit word, most
significant bit first. The receiver works on pins already sampled into the
chip's clock: it takes a bit at the sample where `sck` is first seen high,
shifts it in, latches the command after the first byte, and on the 72nd bit
raises `fire` for one edge. On that edge the core sees the command and the
word; on every other edge it sees no command. `csn` high abandons a partial
frame; `init` clears the bit counter. 76 flip-flops.

`Serial.model` proves the circuit equal to its functions, register by register.
`Serial.session_delivers` is the contract with the host. A *session* is any
sample history made of idle samples and frames; a bit is the clock seen low at
least once and then high at least twice, with `mosi` carrying the bit at the
first high sample. Nothing else is asked — durations may differ from bit to
bit, `mosi` is free at every other sample, the protocol pins may do anything.
On any session the core consumes exactly the session's commands, in order, each
on one edge with its word, and every other edge is quiet (`Delivers`).
`no_path_from_host`: the three pins reach the core only through the receiver's
registers, so the core's command and word ports are register-launched — the
assumed 4 ns arrival at the test design's ports has no counterpart here.

In hardware terms the hypothesis is a serial clock no faster than a quarter of
the chip's clock with the usual mode-0 data timing. The theorem is about
digital samples: metastability, skew between the three pins near a clock edge,
and board timing are outside it, as for the pin sampler.

## The chip

`Chip.netlist n` is any core `n` with the loader machine's ports behind:

    pins → pin map → two-register samplers → serial loader → core → output map

Pins: `ui_in[0]` `sck`, `ui_in[1]` `mosi`, `ui_in[2]` `csn`; `uio[2:0]` the
three protocol pins, driven through their enables, `uio_in[1:0]` sampled as the
engine's inputs; `uo_out` = mode (3 bits), rejected, active, pending, valid,
busy; `rst_n` low is `init`; `ena` is unused. Every input is sampled twice, the
reset included.

- `Chip.trace_eq`: for every pin history and every core, the core takes the
  edges of the fed history (`Chip.history`) and the pins show the output map of
  what the core shows.
- `Policy.chip_trace`, `OnePort.chip_trace`, `TwoPort.chip_trace`: with a proved
  fetch-policy backend as the core, the pins show what the **atomic reference
  machine** shows on the fed history, for any power-up contents of the samplers
  and the receiver — for every pin history with two ports, and on histories
  whose fed pushes satisfy the readiness rule with one.
- `Chip.pins_shielded`: no pin has a combinational path to the core, the
  receiver or an output; each ends at one flip-flop.

The emitted module is the Tiny Tapeout template's `tt_um_*` interface
(`clk`, `rst_n`, `ena`, `ui_in`, `uo_out`, `uio_in`, `uio_out`, `uio_oe`), so
no hand-written wrapper stands between Lean and the flow.

## From the pins to a running program

Four statements, each usable alone, and one that chains them.

- **What an upload does** (`Machine.upload_loads`). With the engine stopped, any
  consumed history that delivers begin, 322 words and commit — however spaced —
  leaves the other bank selected and valid, holding exactly those words register
  by register (`imageOf`), the bank that was active untouched, and the engine
  stopped with the new image's idle pins. Pushes pass an admission predicate, so
  the one theorem covers the machine itself and the capacity-checked reference
  that the dense backends refine, which is what a chip runs.
- **The stream is the program** (`Storage/ProgramUpload.lean`). For the 322 words
  a host builds from a program `p` (`Readiness.upload`): the bank they leave
  reads as `p` at every address, with `p`'s idle pins and last address
  (`upload_holds`); every word passes the loader's validation at its position
  (`upload_good`); and, for images with at most 32 distinct records, the small
  store's capacity check (`upload_fits`).
- **A held program is the one that runs** (`Machine.runs_program`). While the
  selected bank holds `p`, the scheduler is fed as by the fixed program `p`, so
  each machine edge is one edge of the instruction-level engine on `p` — for any
  history without an `init` or a commit, uploads to the other bank and starts
  included, and equally behind the capacity check (`runs_program_with`). This is
  the link to the compilers' and protocols' theorems.
- **Sessions reach the core through the samplers** (`Chip.session_delivers`):
  with idle samples in the samplers and the receiver between frames, a session
  on the pins followed by two more samples of anything delivers exactly its
  commands.
- **In one statement** (`TwoPort.chip_runs_upload`, `OnePort.chip_runs_upload`).
  Upload `p` over the serial pins, then let the pins do anything: the chip's
  pins show the atomic reference machine throughout, and after the upload that
  machine has `p` committed and its engine reset on `p`. Two ports: any fitting
  program. One port: fitting programs that are ready (`Readiness.Image`), and
  the pushes that follow must keep the rule; `chip_upload_ready` shows the
  upload itself does.

`test/SerialUpload.lean` is an executable host for the same frame format: it
serializes the compiled I²C write's upload and a start into 70,855 Tiny Tapeout
pin samples, runs them through the sampler and receiver models, and checks that
the core consumes exactly the 325 commands — with uneven phases, with garbage on
the data pin everywhere but the sample the theorem names, with command 7 as
reset — and that an inverted or least-significant-first driver, a frame cut by
the select line and a missing two-sample tail are all visible. It also checks
the theorem's hypotheses on that program: 322 words, at most 32 distinct
records, every word ready and within capacity; the UART receiver is not ready.

## First measurements

Mapped screen, same recipe as the backends (typical corner, no placement):

| | Test-boundary core behind the sampler | Whole chip |
| --- | ---: | ---: |
| One port | 557,736 µm² | 562,152 µm² (+0.8%), ABC delay 5,364 ps |
| Two ports | 628,939 µm² | 614,555 µm² (−2.3%), ABC delay 5,391 ps |

The loader, the samplers and the pin map cost about as much as the observation
logic that disappears with the stand-in pins. Against the sampled candidate
(547,995 µm²) the whole one-port chip is +2.6% and the two-port chip +12.1%.

## Boundary

Proved: the netlist of the whole chip against the reference machine on the fed
history; what a host session delivers; what an upload leaves; that the loaded
program is the one the engine runs. The statements are about two-valued
registers and digital samples, with the receiver between frames and idle
samples in the samplers at the start of a session — the state any host reaches
by holding the select line high for two clocks. Not done: simulation of the emitted `tt_um_pinwheel`
against an independent serial driver, gate equivalence, any placed or routed
run, the official 8×4 outline (absent from the pinned Tiny Tapeout files), read
back of status over the serial pins, and any electrical or metastability claim.

## Reproduction

```sh
lake build Pinwheel chip_emit
lake env lean -DwarningAsError=true test/ProofAudit.lean
lake env lean -DwarningAsError=true --run test/SerialUpload.lean
.lake/build/bin/chip_emit build/chip/NAME
```
