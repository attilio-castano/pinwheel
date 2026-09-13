# Hardware baseline

Design record: **2026-09-13**. The encoding and raw-program semantics below are implemented in Lean; the [countdown slice](countdown-hardware.md) has also been generated, simulated, and synthesized. The complete execution core and physical loading interface remain future work. This is an internal baseline, not a frozen external ABI.

## Instruction words

The instruction store contains 32 words of 16 bits. Action fields are:

| Bits | Meaning |
| --- | --- |
| 15 | 0 for action, 1 for halt |
| 14:12 | Three output levels, with the existing compiler pin mapping |
| 11:4 | Duration minus one: 0 means one cycle; 255 means 256 cycles |
| 3 | Input capture enabled |
| 2:0 | Receive slot, 0–7; must be zero when capture is disabled |

`0x8000` is the only halt word. Other opcode-one words, and actions with disabled capture but nonzero slot bits, are malformed. Exactly 18,433 of the 65,536 words are accepted. A malformed fetched word stops with fault, applies the program's idle levels, retains receive bits, and exposes no completed result. It never captures input.

`Encoding.decode_encode` proves every typed instruction round-trips. `encode_decode` excludes aliases. `Raw.step_encoded` and `run_encoded` prove that encoding any typed program preserves the existing engine's steps and runs for arbitrary input histories. `malformed_fault` covers rejection separately. Checked host conversion rejects integers above 65,535 rather than wrapping them. These are executable decoder/engine proofs, not a structural decoder circuit yet.

## Selected core contract for the next implementation

All core signals use one rising-edge clock and stable two-valued inputs at that edge. Execution reset is synchronous, active high, and takes priority over start and program commit; the separate cold-initialization request takes highest priority. There is no execution clock enable. Physical pin synchronization and loading transport are later interfaces; their timing must be modeled explicitly.

| Register or signal | Width and convention |
| --- | --- |
| Status register | 2 bits: `00` ready, `01` active, `10` completed, `11` fault; all encodings defined |
| Program counter | 5 bits, valid addresses 0–31; never wrap slot 31 to slot 0 |
| Remaining duration | 8 bits, stores duration minus one at action entry |
| Output levels | 3 bits, registered |
| Receive slots | 8 bits; physical bit `k` holds abstract slot `k` |
| Idle profile | 3 bits, part of the committed program |
| Committed-program valid | 1 bit, cleared by cold initialization, retained by execution reset |
| Logical execution inputs | `initialize`, `reset`, `start`, one observed input bit |
| Logical execution outputs | levels, `busy`, `completed`, `fault`, receive bits |

The existing `samplesByte` packs slot 0 as the most significant byte bit. Thus a packed receive port in that byte order reverses the physical slot-indexed register bits; do not silently reinterpret slot order. Outputs are meaningful after cold initialization. `busy` means active; a result is valid only in completed status and lasts until initialization, reset, accepted start, or accepted program commit. Fault and completion retain the captured data but only completion marks it valid.

A reset clears status to ready, the receive register, PC, and timer, and applies the committed idle profile (zero if no program exists). It retains committed instruction contents, idle profile, and validity. A separate synchronous, active-high `initialize` request clears validity, idle profile, and all execution registers without clearing instruction memory. It takes priority over reset and all commands and must be asserted at cold startup before any observations or requests are relied upon. Keeping initialization distinct lets ordinary reset retain a committed program without assuming memory powers up zero. The eventual physical interface must provide this initialization behavior; its transport/pin mapping is not selected.

After initialization, starts without a committed program are rejected, keeping ready and zero idle. This pre-program state has no counterpart in today's abstract `Machine`, which always contains a program. Whole-core refinement applies after an accepted program commit. The selected initialization protocol is a contract for milestone 3, not an implemented core interface.

Use a 32×16 register-backed instruction store with combinational read and clocked writes for the first core. Its physical timing/cost is unmeasured. The read address is zero for accepted start and `PC + 1` for an action boundary. Guard the increment at 31. The path is status/timer → address selection → instruction read → decode → next output/timer/status/sample registers. All register updates use the same pre-edge state and input snapshot. Consecutive duration-one actions require this full path to settle within one clock; pipelined fetch cannot add an observable cycle.

Logical load/commit retains the existing atomic contract: accepted only while stopped, replaces all words and idle profile, clears execution/results, and establishes validity. Reset suppresses commit/start at the same edge; an accepted stopped commit takes priority over start. Busy commit is rejected without changing the executing program. Physical staging writes must preserve the previous committed program; bank storage, port wiring, and serialized transport are deferred to milestone 5. A parallel full-program value in a proof is not a proposed package pinout.

## Edge schedule

State and pin levels described here are **after** the named edge. Input capture uses the snapshot at that edge.

| Edge | Precondition | Register updates |
| --- | --- | --- |
| Initialization | `initialize` asserted | Clear validity/profile/execution; leave instruction words untouched |
| 0 | Stopped, valid program, accepted start | Clear samples; fetch slot 0; enter action/halt/fault immediately |
| 1 | Slot 0 action has duration one | Fetch slot 1, update levels and capture if requested; no bubble |
| 2 | Slot 1 also has duration one | Fetch slot 2 with the same rule |
| Entry + `D` | Current action duration `D` | Enter next instruction; elapsed time is exactly `D` cycles |
| Halt entry | Decoded word is `0x8000` | Completed, idle levels, retained samples |
| Final action boundary | PC is 31 | Fault, idle levels, retained samples; no wrapped fetch |
| Any execution edge | Reset asserted, initialization inactive | Reset wins, including when start is asserted or the action expires |

Start requests observed while active are ignored, including the edge that completes an action or enters halt. A held start can be accepted on the following stopped edge. All three existing engine/protocol suites remain the behavioral reference.
