# Checked paired upload images

The paired host can now take canonical E64 programs, produce its actual
**290-word upload**, and ask Lean to check the exact bytes before sending them.
The implementation is in `Pinwheel/Hardware/Storage/PairedImage.lean`; the
untrusted renderer is `scripts/paired_image_certificate.py`. This closes the
image-to-dispatch part of the [complete design iteration](../research/complete-design-iteration.md),
not the complete timed controller or chip refinement.

## What the certificate establishes

Lean decodes the source words independently and proves that re-encoding gives
the same words. A malformed source cannot pass by falling back to HALT. It then
checks all 256 addresses and both successor choices against the uploaded image:

- The boot token, idle levels/enables, token operation/levels/duration and
  reserved bits match the source.
- Each referenced parameter entry has the source's capture, condition and
  budget fields. Parameter placement is the compiler's choice; its contents
  are checked independently.
- Branch and fall-through successors come from the source instructions and
  last address, rather than a compiler-supplied successor table.
- HALT and out-of-range fault stop dispatch. Their token row bits are not
  interpreted as executable addresses. Unused image rows contain HALT pairs.
- The serialized words equal the checked parameters, rows, boot and idle data.

`check_sound` turns a successful finite check into `Corresponds`.
`step_matches` and `run_matches` preserve that relation; `checked_trace` proves
it for **every finite sequence of successor choices** from the boot token.
`upload_length` proves that this representation has 290 words. Concrete
certificates use `decide +kernel`; both the certificate and the general trace
theorem are audited for standard axioms only.

The theorem does not derive branch choices or dispatch times from the actual
controller. It does not yet prove serial loading, initialized SRAM behavior,
capture timing, package composition or emitted-RTL correspondence. Resident
SHIFT/KEEP extensions are outside this canonical E64 certificate. Those are
explicit remaining obligations, not premises silently discharged by simulation.

## Reproduce

With the pinned Lean toolchain, the portable image gate needs no CAD tools or
previous build artifacts:

```sh
python3 scripts/check-paired-image.py --tag paired-image-example
```

Use a fresh tag. The gate checks six positive images, including 256 positions
and all 32 parameter entries, and ten meaningful corruptions. Each corruption
must fail acceptance **and** have its exact acceptance proposition proved false
by the kernel. The latter prevents a resource or tactic failure from being
mistaken for rejection of a bad image. Optional captured protocol fixtures
require both `--images PATH` and `--images-sha256 HASH`.

For an actual pin-level demonstration, install the pinned macro models and
Lean/CIRCT/Icarus tools described in [development](../development.md), then run:

```sh
python3 scripts/pinwheel-host.py demo --backend paired --tag paired-demo
```

The host certifies each valid image before uploading it. Its explicit JSON
format is `pinwheel-paired32-v1`; the host rejects a program whose format does
not match the selected backend before I/O. Backend selection is configuration:
the chip does not yet advertise a format identifier through its status pins.
Direct use of the low-level Python `Host` class does not itself invoke Lean.

## Recorded result, 2026-09-26

`build/validation/paired-image-02/report.json` passes six images and ten
kernel-proved rejection cases. The [host workflow](../host-workflow.md) receipt,
`build/host/design-iteration-paired-01/report.json`, additionally binds eight
checked image certificates to successful UART, SPI, I²C and trigger scenarios,
plus malformed-upload recovery on one unchanged RTL chip.

That demonstration's generated RTL is byte-identical to the audited design-A
RTL. Each upload costs 85,285 chip edges including host status operations,
or 1.7057 ms at the assumed 20 ns period. The demonstrated protocol timing
remains unchanged; these are simulation edge counts, not measured board rates.
