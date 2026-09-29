# SRAM context fixtures

These four small GDS layouts reproduce the two internal SRAM LVS failures with
complete local geometry. They contain the two failing cells and their complete
parents, including neighboring devices, wells, contacts, resistor markers and
all source instance transforms. Polygon XOR and text comparisons pass after
export. The entire fixture input set is 51,017 bytes.

Read the [result](../../../docs/physical/sram-context-results.md) and
[manifest](../../experiments/sram-context-results.json) for measured controls,
identities and limits. These are source-derived test inputs, not replacement
SRAM IP or a chip signoff result. The source license is retained in [NOTICE](NOTICE)
and each CDL file.

| GDS / CDL stem | Contents | Native deep / flat result |
| --- | --- | --- |
| `RSC_IHPSG13_WLDRVX8` | One driver, four MOS devices | Pass / pass |
| `RM_IHPSG13_1P_WLDRV16X8` | Sixteen drivers, 64 MOS devices | Fail / pass |
| `RSC_IHPSG13_CDLYX1_DUMMY` | Two MOS devices and one resistor | Fail / fail |
| `RM_IHPSG13_1P_DLY_2` | Six dummy cells and two delay cells; 28 MOS devices and six resistors | Fail / fail |

The two `.metal1.cdl` files retain every original node and dimension while
translating only the dummy's `R0` model from `lvsres` to `res_metal1`, justified
by its complete metal-1 marker. With these files the isolated dummy passes both
modes; its complete parent passes deep mode but **still fails flat mode**. Keep
that result: the default reader combines the six schematic resistors into one,
whereas the layout retains six. No PDK file was edited.

## Check and reproduce

From the repository root, run the portable input guard:

```sh
python3 -B physical/fixtures/sram-context/check_inputs.py
```

It checks all ten input identities, both parent interfaces, both exact model
translations, and the disconnected-output counterexample. The native comparator
alone accepted that counterexample after discarding its unused declared pin;
the explicit pin-use check is required. This guard is scoped to these fixtures
and is not a general interface or physical validator.

Use the pinned CAD image and exact `ihp-sg13cmos5l` PDK from the experiment
manifest, with this directory mounted read-only at `/fixtures`, the PDK at
`/work/pdk`, and a fresh writable `/results`. Inside that offline environment,
the driver neighborhood comparison is:

```sh
python3 -B /work/pdk/ihp-sg13cmos5l/libs.tech/klayout/tech/lvs/run_lvs.py \
  --layout=/fixtures/RM_IHPSG13_1P_WLDRV16X8.gds \
  --netlist=/fixtures/RM_IHPSG13_1P_WLDRV16X8.cdl \
  --topcell=RM_IHPSG13_1P_WLDRV16X8 --run_mode=flat \
  --run_dir=/results/driver-flat
```

Change `flat` to `deep` and use a new output directory to reproduce the driver
failure. Substitute `RM_IHPSG13_1P_DLY_2` for the delay parent, first with its
original CDL and then with `RM_IHPSG13_1P_DLY_2.metal1.cdl`. The top-cell name
remains `RM_IHPSG13_1P_DLY_2`. Do not add port-ignore or cell-ignore options.
The recorded invocation limit is four CPUs, 6 GiB and at most 600 seconds;
each native fixture comparison here took under two seconds.

Inspect the native summary and `.lvsdb` circuit cross-reference. This wrapper
returns exit code zero for both matching and nonmatching circuits. A completed
process therefore does not establish a pass.

`inputs.json` binds these tracked inputs to the exact locally executed files;
the only packaging changes to CDL are source-license and context comments.
Full native reports and mutation geometries remain in the ignored local evidence
directory named by the manifest. A fresh checkout retains these reproductions,
but does not contain the complete chip, installed PDK or historical CAD outputs.
