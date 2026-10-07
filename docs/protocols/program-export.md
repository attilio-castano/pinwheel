# Export protocol requests through Lean

The production exporter calls the existing Lean I²C register-read and SPI
transaction compilers. It accepts one JSON request and emits canonical E64
source words for the paired hardware. It does not change the chip or generate
Lean source for each request.

Prepare the imported module once, then send a request file or standard input:

```sh
lake build Pinwheel.Program.Requests
python3 scripts/export-program.py request.json
```

A compact one/two-byte I²C register read uses:

```json
{
  "schema": "pinwheel-protocol-request-v1",
  "protocol": "i2c-register-read",
  "address": 45,
  "register": 113,
  "byte_count": 2,
  "phase_cycles": 7,
  "wait_cycles": 19
}
```

`address` is 0–127, `register` is 0–255, `byte_count` is 1 or 2, and both
timing values are 1–256 chip edges. The compact result contract remains the
existing compiler's success payload, timeout, or aggregate NACK/bus fault.

An SPI transaction uses:

```json
{
  "schema": "pinwheel-protocol-request-v1",
  "protocol": "spi-transaction",
  "mode": 3,
  "payload": [59, 201],
  "half_cycles": 5
}
```

`mode` is 0–3, `payload` contains one or two bytes in wire order, and
`half_cycles` is 1–256 chip edges. This frontend embeds the payload in the
compiled program; the separately named resident SPI program accepts its byte
at START.

The response has schema `pinwheel-compiled-program-v1`, a `request` containing
the validated input object, and a `program` with the existing host fields
`format`, `words`, `last`, `idle_levels`, and `idle_enabled`. Its format is
`pinwheel-paired32-v1`; its 256 words are canonical E64 source records, which
the host lowers to the paired upload. Bind result decoding to the returned
request, including the I²C byte count. JSON whitespace and key order are not
request identity; callers can retain a digest of their original request bytes
when byte custody is required.

Unknown/missing fields, wrong types, unsupported schemas/protocols and values
outside these bounds fail before finite compiler operands are constructed.
No clamping or modulo conversion is accepted. Successful stdout contains one
JSON response; failure uses stderr and a nonzero exit code. The wrapper runs
the static `scripts/ProgramExport.lean` entrypoint through the local Lean
environment.

The pure interface is `Pinwheel.Program.Export.compileRequest` in
[`Requests.lean`](../../Pinwheel/Program/Requests.lean). Run its focused checks
with `lake env lean --run test/ProgramExport.lean`; package behavior and physical
timing continue to use their existing, separate acceptance gates.
