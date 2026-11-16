# Frozen 8×4 timing coverage, November 11, 2026

The frozen November 7 hold/capacitance candidate has complete endpoint
accounting across the nine retained draft timing scenarios. The audit reused
the exact three SPEFs, three Liberty PVTs, implemented netlist and provisional
20 ns SDC with a propagated clock. The same pinned OpenSTA binary reproduced
the earlier global setup and hold slack within 1 fs in all nine cases. The
bounded native replay took 60.692 seconds, exited zero and verified container
cleanup. [Original timing inputs and results](streaming-8x4-hold-cap-trial-20261107.md)

| Check | Result in every draft scenario |
| --- | --- |
| Setup and hold | 6,039 FF data pins and 12 active outputs each have a constrained min and max path. Worst hold was +31.572 ps at MAX/fast. Worst setup was +1.554538 ns at MAX/slow. |
| Public inputs | All ten consumed nonclock inputs have a constrained min and max path. The eight `uio_in` bits have no sinks. |
| Public output exceptions | Twelve tied-low bits have no path, comprising `uio_oe[3..7]`, `uio_out[3..7]` and `uo_out[6..7]`. |
| Constraint diagnostics | `check_setup -verbose` reported no findings. The native search and physical graph census account for every endpoint. |
| Clock pulse width | All 12,078 high and low checks across 6,039 FF clock pins passed per case. Worst slack was +9.714266 ns at MAX/slow. |
| Recovery and removal | No applicable paths. All 6,039 cell `RESET_B` pins have distinct constant-high drivers. Public `rst_n` has constrained data paths. |
| Minimum period | The loaded Liberty and SDC yielded no applicable minimum-period check. |

OpenSTA enumerated 6,675 search endpoints per case. Besides the 6,051
constrained data and output endpoints, each case had the same 624 endpoints
with the following physical or logical explanations. The twelve tied-low
outputs and 6,039 tied-high resets were outside this search inventory.

| Other search endpoint | Count |
| --- | ---: |
| Passive antenna diode inputs | 160 |
| Open clock-load outputs | 78 |
| Connected combinational outputs with no instance or public-output sink | 196 |
| Input pins on gates with a constant output | 188 |
| Input pins whose own arcs are masked by a constant on a live-output gate | 2 |

The separate endpoint readback reopens all nine raw logs against the exact
ODB export and the three pinned Liberty functions. It propagates constants
through the combinational graph and checks which individual pins can affect
each output. On the two live-output gates, `A2` is tied low and the reported
`A1` input cannot affect `Y`.

The native endpoint census records one constrained path per endpoint and
delay mode and one witness per consumed input and mode. It establishes
coverage under the retained draft models. Qualified CMOS5L extraction and
the accepted host timing and clock contract are still needed. The pulse
inventory uses OpenSTA's full per-pin report.
[Pinned OpenSTA command](https://github.com/The-OpenROAD-Project/OpenSTA/blob/857316ff001b2a8dbbdc5996944d08a6d38c87ab/search/Search.tcl#L728-L749)

## Local evidence and reproduction

The candidate is the `dc654986…` ODB and `d4cd48f0…` GDS from the
[verified rehearsal bundle](streaming-8x4-hold-cap-rehearsal-20261107.md).
The replay and endpoint readback are separate ignored evidence under
`build/8x4-hold-cap-20261107/trial-02/timing-coverage-01/`. The original
timing readback and rehearsal archive were preserved.

| Artifact | SHA-256 |
| --- | --- |
| `execution.json` | `23b98e9205d48646fc92dca4b90eb040eb5799f0e495c0815f0f19d4ae46ed7e` |
| `request.json` | `a9325c95cee847824d2903c2c4e264c9f51d8bd432e2c620f31ffa4a87a8d68d` |
| `probe.tcl` | `9aa4256f766f4ab645a01145b95138eda6a455a9c5c457905642c05191643a7a` |
| `readback.json` | `19892a8d2aba61b4d5c0ef8fa3bf8255bb154b39f6099f25eec2b8caeab2a88c` |
| `endpoint-readback.json` | `9b516f3f726473f2b049fd28c4004c9331d67356bf92a5b4828d32bf754b9709` |

Set `PINWHEEL_HISTORY` to the retained history checkout. Use a fresh ignored
output directory beside the original `timing/` directory for a new replay.
The second command independently reopens the completed November 11 run.

```sh
python3 -B scripts/streaming_8x4_hold_cap_timing_coverage.py \
  --history "$PINWHEEL_HISTORY" \
  --out build/8x4-hold-cap-20261107/trial-02/timing-coverage-02 \
  --deadline "$(( $(date +%s) + 1350 ))"
python3 -B scripts/streaming_8x4_hold_cap_endpoint_readback.py \
  --history "$PINWHEEL_HISTORY" \
  --coverage build/8x4-hold-cap-20261107/trial-02/timing-coverage-01/readback.json \
  --coverage-sha256 19892a8d2aba61b4d5c0ef8fa3bf8255bb154b39f6099f25eec2b8caeab2a88c
```
