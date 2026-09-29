# Protected-load hold repair experiment

The pinned OpenROAD hold optimizer can select failing loads, remove every
selected load because it is protected, and then try to insert a buffer with
no loads. `protected-loads.patch` excludes protected pins when selecting the
timing subset. It keeps their capacitance in the excluded-load calculation
and leaves unresolved protected timing checks visible.

This directory targets OpenROAD commit
`dcf36133a369abc8f3c5e5738cd4d82e4903c0e0` only. It does not change Pinwheel's
default tool image. See the [study](../../docs/physical/hold-repair-experiment.md)
for the measured chip result and evidence boundaries.

## Experimental native adapter

`extension.cc` copies the native `Resizer::repairHold` adapter and exposes it
as a Tcl command. The build compiles the original or patched `RepairHold.cc`
against the exact pinned headers. `-Wl,-Bsymbolic` binds those two functions
inside the extension; other calls use the resident OpenROAD APIs. Existing
resizer objects, journals and protections remain in use. A revision check
rejects other OpenROAD versions. This is an experiment-specific build, not a
stable OpenROAD plugin ABI.

The retained run contains the source fetch receipt, exact headers and hashes,
compiler commands, both binaries, failed configuration attempts, fixtures,
and circuit readbacks. `build.py` expects that run mounted at `/probe` and
this directory mounted at `/support` in the recorded image. It refuses to
replace its `native-02` build directories. External dependency headers use
system include paths, matching imported CMake dependency treatment.

## Native regression gate

From the pinned image with the retained dependencies and binaries mounted:

```sh
python3 -B /support/regression.py /probe /probe/regression-new
python3 -B /support/verify_regression.py /probe/regression-new
```

Both commands must succeed. A zero exit from the fixture runner alone is not
acceptance: original-tool failures are intentional and the verifier checks
their exact cause and the successful circuit readbacks. Each OpenROAD command
has a 20-second cap; a fixture matrix has a 300-second cap.

The matrix covers all-protected loads, a protected failing branch sharing its
net with a passing editable branch, a mixed net requiring editable repair,
and an unprotected control. It compares the unchanged extension against the
native command, checks protected connectivity and original cell geometry,
checks the inserted buffer chain, and requires the control's final netlist,
placement and reported hold slack to match all three implementations.

To use the qualified patched implementation in a separately recorded recipe:

```tcl
load /probe/native-02/patched/libpinwheel_hold.so Pinwheelhold
rename rsz::repair_hold rsz::repair_hold_original
interp alias {} rsz::repair_hold {} pinwheel_repair_hold
```

The normal `repair_timing -hold` wrapper still handles units and arguments.
The launcher must bind the binary and regression receipt by hash before use.
The [upstream BSD license](OPENROAD-LICENSE) covers copied OpenROAD code.
