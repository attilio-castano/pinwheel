# Pinned detailed-route import preservation

This isolated native adapter targets OpenROAD
`dcf36133a369abc8f3c5e5738cd4d82e4903c0e0`. It does not replace the default
tool image or change Pinwheel's RTL, ABI, cell inventory, placement, macros,
power grid, clock topology, technology rules or routing guides.

The original importer ignores serialized per-path `RULE` opcodes. It therefore
loses default/TAPER exceptions on NDR nets and imports their widths using layer
defaults. The repaired importer tracks the actual path rule, resets it at each
new path, retains it across orthogonal segments/vias, sets native taper flags,
and preserves the effective width and default/explicit endpoint extensions.
Distinct per-path `TAPERRULE` overrides and NDR `RECT` patches are unsupported
and rejected before routing, rather than silently normalized.

`prepare-03.py` retains the fetched source and creates a patched copy of `io.cpp`
and copies of `TritonRoute::initDesign`, `TritonRoute::main`, and
`TritonRoute::endFR`. The main
copy adds a read-only semantic/geometry audit before PA/GC/TA/DR and rejects
the native fallback to global routing if the supplied guides fail admission.
`-Wl,-Bsymbolic` binds the adapter's main/init/importer sequence inside its
shared library; other calls use the resident native APIs. The pinned writer
also tests the begin style when deciding whether to emit a variable end
extension. The repair tests the end style and compares implicit extensions
against the encoded path's effective default/NDR width. The byte-identical
local `endFR` binds this corrected writer for the final database export;
resident debug snapshots remain unsupported because they use the old writer.
A generated friend
declaration exposes only the import-boundary fixture entry. It changes no
member or object layout. Runtime admission must pin the actual ELF and the
compiled adapter, headers, build receipt and regression receipt by hash.

The pre-GC audit compares every imported detailed wire/via/patch geometry and
per-object default/NDR association with the serialized database. Empty routes,
unmatched objects and ambiguous coincident default/NDR associations fail
closed. No post-route output patch, DRC waiver, capacity change, single-step
strategy or pin-access skip is used.

Build only inside the recorded offline image, with the new bundle mounted at
`/taper`, this directory at `/support`, and the retained matching dependency
headers at `/deps`:

```sh
python3 -B /support/build-05.py /taper
python3 -B /support/regression-06.py /taper /taper/regression-06
```

The native regressions compare original and patched importers, mixed default
and NDR branches, equal and unequal widths, vias, default RECT patches,
explicit/truncated endpoints, fixed/non-NDR controls, and fail-closed cases.
The original same-width and unequal-width importers must fail the semantic
audit; supported patched cases must preserve full NETS/SPECIALNETS/NDR DEF
sections. Each fixture checks both the actual ELF and its original/patched
adapter binary against the recorded hashes before importing the design.
Each native fixture has a 20-second cap; the matrix has a 300-second
cap. These are import-boundary checks. A fresh real-P2 ordinary `end_iter0`
no-edit control remains mandatory before any actual repair iteration.

Install the qualified patched binary before the unchanged Tcl procedure:

```tcl
load /taper/native-05/patched/libpinwheel_drt_preservation.so Pinwheeldrtpreservation
rename drt::detailed_route_cmd drt::detailed_route_cmd_original
interp alias {} drt::detailed_route_cmd {} pinwheel_drt_preservation_detailed_route_cmd
```

Set `PW_DRT_PRESERVATION_AUDIT` to a fresh JSON filename. The replacement
dispatch accepts exactly the pinned twenty arguments and forwards identical
parameters to the ordinary native scheduler. It rejects distributed routing,
single-step execution and skipped pin access. Source hashes, source guides,
exact no-edit rules/geometry, actual iteration labels and independent scope
readbacks remain experiment-level acceptance gates. Neither this adapter nor
a successful routing command establishes DRC/LVS/STA or tapeout readiness.

The retained build05 and native regression06 pass all twelve import-boundary
cases. The original importer fails the intended equal-width and unequal-width
counterexamples. Earlier missing-header, fixture setup and endpoint-writer
failures remain in their original job directories. Reproducing a job requires
a fresh output directory; never rerun a writer over retained receipts.

The [OpenROAD BSD license](OPENROAD-LICENSE) covers adapted source. The
supplemental matching LLVM OpenMP header is generated from the official
LLVM 21.1.8 template using its source CMake substitutions; its original
Apache-2.0-with-LLVM-exception notice, license and source receipt are retained
with that header.
