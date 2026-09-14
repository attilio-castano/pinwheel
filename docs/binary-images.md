# PWL version 0: binary program images

Implementation record: **2026-09-13**. Pinwheel now encodes explicit and counted programs into canonical binary files, decodes them in Lean, and proves that decoded execution preserves the existing engine semantics. The I²C examples occupy **715 bytes explicit** and **205 bytes counted**. This is an exact serialized-image comparison, including metadata and explicit bank padding. Physical memory allocation, a circuit decoder, and synthesis cost remain open.

V0 uses byte-aligned, tagged records to make the first load-image contract inspectable and independently implementable. It is not a commitment to byte-wide physical instruction memory. The decoder currently reconstructs the typed program before execution; the bytes do not execute directly from a structural memory/decoder circuit.

## Header and framing

Every value below is an unsigned byte. Fields narrower than eight bits must be within their stated range; high bits are rejected rather than truncated. There are no multibyte scalar fields or implicit host endianness. Records occur in the order listed, with no alignment padding.

| Offset | Meaning |
| --- | --- |
| 0–2 | Magic `50 57 4c` hexadecimal: ASCII `PWL`. |
| 3 | Format version: `00`. |
| 4 | Image kind: `00` explicit, `01` counted. |
| 5 | Idle output levels, 0–7. |
| 6 | Idle drive enables, 0–7. |

An **explicit** image then contains one byte for its inclusive last execution address, 0–127, followed by exactly **128 instruction records**. Every operand must be literal. All bank slots are preserved, including those beyond the execution limit and any halt padding. This supports round trips for every existing `Reactive.Program`, without assuming unused slots are zero or halt.

A **counted** image instead contains two data bytes at offsets 7–8, followed by one layout tree encoded in preorder. Its last execution address is derived from the decoded tree's span minus one. The decoder checks span ≤128, total nodes ≤64, and loop nesting ≤2 before constructing the program. Repeat counts range from one to eight. Tree-parser recursion has a fuel bound of 64; a valid bounded program always fits that bound.

The caller supplies one complete byte sequence, such as a file or an externally framed message. V0 has no transport, length prefix, checksum, or physical write/commit protocol. Truncation, extra bytes, unknown magic/version/kind, and noncanonical encodings are rejected. A future streaming transport must provide its own framing and integrity contract.

## Operand records

Square brackets below mean concatenation, not additional stored delimiters. `Bool` is one byte, exactly 0 or 1. Durations and wait budgets store **cycles minus one**, 0–255.

| Record | Byte sequence |
| --- | --- |
| Pins | `[levels, enables]`, each 0–7. |
| Index | `[0, literal]`, literal 0–7; or `[1, depth]`, depth 0–1. |
| Pin expression | `[0, Pins]`; or `[1, Pins, pin, enableField, byteIndex, bitIndex, msbFirst, invert]`. |
| Optional capture | `[0]`; or `[1, input, destinationIndex]`, input 0–1. |
| Single-input condition | `[input, level]`, input 0–1, level Bool. |
| Masked check | `[mask, value]`, each 0–3. |
| Target | `[0, address]`, address 0–127; or `[1]` for the next execution address. |

In a serial pin expression, `pin` is 0–2; `enableField`, `msbFirst`, and `invert` are Booleans. `byteIndex` and `bitIndex` are Index records. A true `enableField` updates a drive-enable bit; false updates an output-value bit. Loop depth zero names the innermost loop. The existing counted-store rules govern index lookup, bit order, and polarity.

A transfer is `[0]` for sequential execution, `[1, Target]` for a jump, or `[2, sampleIndex, trueTarget, falseTarget]` for a branch. A successor permits those three forms plus `[3, index, comparisonValue, equalTransfer, otherTransfer]`; the comparison value is 0–7. The conditional form contains two ordinary transfers, not recursively nested conditionals.

These are structural validity rules. A representable program can still fault during execution—for example, by selecting data byte 7 from a two-byte bank or jumping beyond its execution limit. Encoding preserves those semantics. It does not assert that every admitted program is useful, safe for a particular peripheral, or terminating.

## Instruction and layout records

Both image kinds use the same instruction-record grammar:

| Opcode | Fields following the opcode byte |
| --- | --- |
| 0: Action | Pin expression, duration, optional entry capture. |
| 1: Wait | Pin expression, single-input condition, wait budget. |
| 2: Checked | Pin expression, duration, masked guard, optional entry capture, optional terminal capture, successor. |
| 3: Qualify | Pin expression, masked condition, duration, wait budget. |
| 4: Halt | None. |

Explicit images reject serial pin expressions, loop-index operands, `next` target expressions, and conditional successor selectors, even when a dynamic expression would happen to evaluate to a literal at startup. Counted images admit the complete grammar.

The counted tree records are:

| Tag | Fields following the tag byte |
| --- | --- |
| 0: Emit | One instruction record. |
| 1: Sequence | First child tree, then second child tree. |
| 2: Repeat | Count minus one, then the body tree. |

An emit tag is additional to the instruction opcode. The I²C tree stores 15 emit tags, 14 sequence tags, and two repeat tags plus their count bytes: **33 layout bytes**. No tree nodes are silently discarded or treated as free hardware. A later flat descriptor table or packed format must prove correspondence with this representation.

For example, the counted halt program with released idle pins and data bytes `12 34` is exactly:

```text
50 57 4c 00 01 00 00 12 34 00 04
```

The last two bytes are the emit tag and halt opcode. `test/Binary.lean` checks this independent golden and a longer record exercising serial pins, both captures, and conditional continuation.

## Proof boundary

Every field/record parser has a prefix-preservation theorem: decoding an encoded value followed by any suffix recovers that value and leaves the suffix unchanged. The tree proof uses induction and the node bound. These compose into whole-image round trips:

- `decode (encode image) = some image` for every typed image, including all bank slots and counted program data.
- Every successfully decoded byte sequence equals the encoder's output for that image. Canonicality concerns the decoded representation; distinct typed programs may still have equivalent behavior.
- Conversion between Lean bytes and native `ByteArray` preserves every byte, and native encode/decode round trips agree.
- Loading a valid encoded image has the existing atomic stopped-load behavior. Invalid images leave the machine unchanged; busy replacement remains rejected.
- Encoded explicit and counted I²C images produce the same complete state for every sampled input history and elapsed cycle, composing with the existing reference correspondence.

The full-run I²C claims retain the existing no-reset/reload boundary. These theorems prove codecs, decoded-program execution, and abstract loading. They do not prove a raw-byte cycle interpreter, circuit memory ports, decoder delay, a physical upload interface, compiler lowering, or electrical behavior. Native file IO and the independent Python implementation are tested, not formally verified. All **37 public binary theorems** pass the standard-axiom audit; there are no unfinished proofs or custom assumptions.

## Exact storage comparison

The generated examples use duration 4; I²C uses wait budget 8, address `0x53`, and payload `0xA6`. UART transmits `0x53`; SPI transmits `0xA6`.

| Image | Header | Instruction records within limit | Layout | Data | Records beyond limit | Total bytes |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| UART explicit | 8 | 82 | 0 | 0 | 96 | **186** |
| SPI explicit | 8 | 141 | 0 | 0 | 96 | **245** |
| I²C explicit | 8 | 658 | 0 | 0 | 49 | **715** |
| I²C counted | 7 | 163 | 33 | 2 | 0 | **205** |

The explicit header includes its last-address byte. Embedded UART/SPI retain execution limit 31, so their first 32 records can include halt padding; 96 more halt records remain outside that limit. I²C's first 79 records occupy 658 bytes, followed by 49 one-byte halts. The counted layout contains only its actual tree, within the 64-node bound.

The counted image is **510 bytes smaller** under this common V0 grammar. Even excluding the explicit bank's 49 padding bytes, its header plus first 79 records would occupy 666 bytes; that prefix alone is **not a valid V0 explicit image**, because the format preserves the complete bank. This separates instruction reuse from bank-capacity overhead.

These files are not the older hardware's 32×16-bit instruction bank and cannot be loaded directly into that RTL. Byte alignment, variable record lengths, staging storage, decoded representation, and configured physical capacities all affect a future chip implementation. The numbers above do not establish area savings or operating frequency.

## Reproduction and evidence

```sh
python3 scripts/check-binary.py
python3 scripts/check-reactive.py
```

Only the pinned Lean toolchain and Python are required. The binary runner builds the library, audits all binary theorems, validates files, runs an independent Python grammar/lookup implementation, and executes both decoded I²C backends through the existing wire target and monitor.

Evidence includes 1,280 image round trips with all 128 fetched instructions checked per image; 920 rejected truncations; malformed headers, fields, tags, bounds, and trailing data; native-byte and file checks; and file-backed UART → SPI → explicit I²C → counted I²C replacement. The independent reader matches **512 fetched instructions across four files**. Each decoded I²C backend passes **4,224 transactions / 822,896 cycles**, including the unchanged 255/282-cycle quiet/stretched examples and sampled error forks. The existing typed negative variants remain additional checks.

`build/binary/` contains the four `.pwl` files, `storage.csv`, fetch-oracle CSVs, logs, theorem audit, and source/artifact hashes. Decoded wire traces/coverage live in `build/binary-explicit/` and `build/binary-looped/`. `report.json` is removed before validation and published only after all checks pass. The full library build now has 53 jobs; no hardware flow was rerun.

## Hardware decision and remaining integration

The [E64 milestone](execution-records.md) selects load-time lowering into fixed-width literal records. Actual explicit and counted V0 write files lower to identical 256-slot E64 images. V0 remains unchanged; it does not encode the wider register-read program. A bounded dictionary deduplicates literal records after counted operands are resolved, so this hardware is not a runtime interpreter of the counted syntax tree.

The [decoder/store hardware record](execution-hardware.md) measures direct and indexed register stores with the same two-read-port interface and raw write protections. Lean proofs, independent RTL checks, and generic synthesis now cover those frontends. Physical timing, mapped area, the wider reactive scheduler, and an atomic upload/commit interface remain open. Staging and metadata costs must be included when that loading contract is implemented; serialized file size remains distinct from allocated hardware cost.
