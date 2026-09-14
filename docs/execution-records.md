# E64 execution records

Decision: **2026-09-13**. Lower programs at load time into fixed-width, literal
64-bit execution records. Keep PWL V0 as the existing load-image format. E64 is
an internal hardware representation, not a new upload protocol or file version.

The [bounded I²C register read](i2c-register-read.md) supplies the capacity test:
its four-phase bit schedule needs 155 logical addresses and eleven meaningful
capture slots. E64 therefore targets the same reactive instruction semantics
with 256 addresses and 16 capture slots. Timers remain eight bits, storing
duration or budget minus one. No new instruction or extra execution cycle is
needed for repeated START, receive, final NACK, or STOP.

## Layout

Bit zero is the least significant bit. The record has one fixed set of wires;
the operation selects which fields matter.

| Bits | Width | Field |
|---|---:|---|
| 0–2 | 3 | Kind: action 0, wait 1, checked 2, qualify 3, halt 4 |
| 3–5 | 3 | Output levels |
| 6–8 | 3 | Output drive enables |
| 9–16 | 8 | Duration minus one; wait uses its budget minus one here |
| 17–24 | 8 | Qualification wait budget minus one |
| 25–28 | 4 | Guard: input mask in low two bits, value in high two bits |
| 29–34 | 6 | Entry capture |
| 35–40 | 6 | Terminal capture |
| 41–42 | 2 | Finish: sequential 0, jump 1, sample branch 2 |
| 43–46 | 4 | Branch sample index |
| 47–54 | 8 | Jump target or branch-true target |
| 55–62 | 8 | Branch-false target |
| 63 | 1 | Reserved; zero |

A capture uses enable in its low bit, input selector in the next bit, and a
four-bit destination above them. Disabled captures are exactly zero. Wait uses
only the low two guard-field bits: input selector followed by desired level.
Action permits entry capture; checked permits entry and terminal capture plus
finish; qualify uses the guard and both timer fields. Halt is exactly the word
`4`. All unused fields are zero. Unknown kinds, finish 3, nonzero reserved bits,
and noncanonical captures/unused fields are rejected.

`Hardware/Execution/Record.lean` owns the schema and typed codec.
`RecordProofs.lean` proves field extraction and typed encode/decode round trips,
and that every accepted word is the canonical encoding of its decoded operation.
These claims cover all supported operations, including eight-bit branch targets
and four-bit capture destinations.

## Two storage candidates

Both candidates expose two combinational reads, intended for current and
successor instruction access. They share the E64 decoder and synchronous raw
write interface. A registered read would require a new fetch-latency argument
before preserving the existing terminal-capture/branch/pin-update edge.

| Candidate | Allocated storage | Lookup |
|---|---:|---|
| Direct | 256 × 64 = 16,384 bits | Address selects a literal record |
| Indexed | 64 × 64 + 256 × 6 = 5,632 bits | Address selects a dictionary index, then a literal record |

The indexed store deduplicates complete records. It is distinct from executing
the counted byte-loop syntax directly. Counted operands are resolved during
loading; the hardware does not traverse a syntax tree or calculate loop operands
on each protocol edge. The 715-byte explicit and 205-byte counted V0 write files
lower to identical E64 words and therefore the same deduplicated contents.

The indexed capacity is **at most 64 distinct records**, including padding.
Programs exceeding it are rejected. This is a capacity tradeoff: the direct
store can represent 256 distinct records. UART, SPI, I²C write, and the register
read examples use respectively **3, 11, 14, and 25 distinct records**, with
canonical halt padding through address 255. Those are example counts, not a
proof that every future protocol program fits the dictionary.

`Images.lean` owns lowering and the functional fetch adapters. Its indexed
lowerer returns a certificate that all 256 expanded lookups equal the source
words. Agreeing direct/indexed stores preserve typed fetch. Existing V0 numeric
operands are widened without changing values, and unused upper addresses halt.
Native checks compare actual explicit/counted V0 files after lowering. E64 does
not enlarge V0's source-format limits or provide a V0 encoding for the wider read.

The next implementation step is to measure writable decoder/store circuits with
the same ports and synthesis flow. Allocated bits alone do not measure selection
logic, delay, total processor cost, or physical area. Program idle pins and the
last-address limit remain separate metadata; a concrete loader must eventually
commit them together with the records.
