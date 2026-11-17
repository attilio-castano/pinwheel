# Memory library and streaming accelerator campaign

The first reusable memory component will implement the existing exclusive
single-port command contract. The two existing RAM semantics must stay distinct:

| Existing module | Reusable behavior |
| --- | --- |
| `Hardware.Memory` | One enabled write and unconditional reads; read-first collisions; configurable modeled read latency |
| `Memory.Flops` | Decoded full-word writes and balanced combinational reads, proved against latency-zero memory |
| `Memory.Registered` | Output registers update on every edge, including writes; proved against latency-one memory |
| `Memory.SinglePort` | Exclusive idle/read/write: read updates Q, write holds Q, idle holds both memory and Q |
| `Memory.Sram` | A partial initialized-value model related to arbitrary initial physical memory; replicated read ports and broadcast writes |

`Memory.Registered` therefore cannot be used directly as an implementation of
`SinglePort.Contract`. Neither contract silently supplies reset, initialized
contents, response validity, backpressure or byte enables. Current capacities
are powers of two, so all address-bit patterns are legal.

## First implementation slice

1. Add a complete typed command interface: enable, write, address, write data
   and Q. Disabled commands decode to idle. Prove physical codec round trips.
2. Construct `CommandFlops` from the existing decoded word updates and balanced
   read mux. Update Q only on reads. Preserve the existing memory array on idle
   and preserve Q on idle and writes.
3. Prove the state transition for arbitrary input and register bits, then
   package both `SinglePort.Contract` and the shared `Implementation` certificate.
   Provide exact state encode/view correspondence without an initialization or
   reset assumption.
4. Check independent model/RTL replay, complete endpoint correspondence and
   state/output mutation rejection. Cover disabled writes, consecutive reads,
   same-address read/write/read sequences, all addresses and arbitrary initial
   arrays and Q.

The generic read mux currently lives in `Hardware.Execution.Memory`. Reuse it
first; a later move should preserve compatibility aliases and rerun its existing
clients. The command RAM adds no fictitious memory-clearing reset.

## Streaming adapter and accelerator

Add a request/response adapter with one outstanding read and a held response
under downstream stalls. Reset cancels pending responses while preserving the
array. Reuse the stream FIFO and elastic-stage proofs, then move a bounded range
from one source memory through a proved transform into a separate destination
memory.

The central completion theorem should establish that after `N` completed writes,
each address in the destination range contains the transform of the corresponding
initial source value; all other destination addresses are unchanged. Assumptions
include initialized source coverage and nonwrapping ranges. Reset may leave a
written prefix, but must suppress stale responses and further writes from the
aborted transfer. Eventual completion requires explicit service assumptions.

External SRAM remains a supplied implementation contract. Digital trace proofs
do not independently qualify a macro's electrical behavior. Byte enables,
non-power-of-two depth, multiple outstanding reads and shared source/destination
storage are later extensions with explicit semantics.
