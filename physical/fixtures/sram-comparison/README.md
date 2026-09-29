# SRAM fixture comparison policy

This experimental recipe compares the four [unchanged context fixtures](../sram-context/README.md)
in both hierarchical (`deep`) and flat extraction. It addresses comparison
hierarchy, resistor dimensions and physical port ownership. It does not qualify
the full SRAM or chip. The [study](../../../docs/physical/sram-comparison-results.md)
owns the result, limitations and correction to the preceding database-only verdicts.

`policy.rb` runs after the pinned deck's extraction. It binds ports by the source
top cell's own GDS labels and the extracted metal net at each label's position.
Child labels remain internal. Existing `VDD!`/`VSS!` spellings map to the declared
`VDD`/`VSS` names without merging wires or changing any device connection.

The recipe flattens only the two small **netlists**, verifies expanded device
counts, compares both metal-resistor dimensions, preserves all six resistors
individually and keeps declared ports through preparation. All named boundary
correspondences are mandatory. The native comparison, final native port verdict,
database and complete policy audit must all pass. A zero exit code is insufficient.

`run.py` checks the exact fixture and 183-file deck inventories, creates a private
deck copy and modifies only `sg13cmos5l.lvs`. Device-recognition/connectivity rules,
installed PDK, original GDS and original fixture files are unchanged. The existing
`.metal1.cdl` translation remains restricted to the dummy's one dimensional
resistor; it is not an analog resistance model. `--controls` generates deliberate
defects in separate files, including geometry-preserving text mutations, and
checks an unchanged physical carrier before attributing its mutations.

Inside the pinned CAD image, with this directory at `/policy`, the unchanged
fixture directory at `/fixtures`, the PDK at `/work/pdk` and a fresh writable
output directory under `/out`, run:

```sh
python3 -B /policy/run.py \
  --pdk-lvs-dir /work/pdk/ihp-sg13cmos5l/libs.tech/klayout/tech/lvs \
  --fixtures-dir /fixtures --output /out/qualification --controls
```

Use image `sha256:5825633bea1f9cbc705ece2de2bc31de6e4ec83d233739205a0f265ef9d92f92`,
no network, a read-only root, read-only source mounts, four CPUs, 6 GiB, writable
`/tmp`, one container and a 180-second outer timeout. Each native comparison also
has a 60-second timeout. Existing output paths are refused. Retain the complete
output and cleanup receipt; the protocol's campaign budget still applies.

The first policy experiment used 8/2 labels globally. The retained version only
reads top-owned labels for boundary binding, so it needs no general label-rule
change. Native simplification without the interface safeguards can accept the
disconnected-output counterexample. Keep both the negative controls and the
counterexample ablation in the [manifest](../../experiments/sram-comparison-results.json).
