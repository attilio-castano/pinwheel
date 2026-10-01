# Package-power request checker

`contract.json` binds the saved A candidate and records missing parent/provider
inputs. `validate.py` checks a request and writes JSON only to stdout. It does not
run CAD, create a report directory, qualify components or change acceptance.
The [contract study](../../../docs/physical/package-power-contract.md) explains
the typed values, activity coverage and stop conditions.

From the repository root:

```sh
python3 -B physical/fixtures/package-power-contract/validate.py --require-ready
```

Exit 2 is the expected result while inputs are missing. Exit 1 refuses malformed,
changed or disconnected evidence. Without `--require-ready`, a valid incomplete
request exits 0; read `ready_for_scoped_analysis`. A separate `--artifact-root`
may locate recovered `build/validation` receipts while the selected manifest
continues to come from `--repository`. All evidence paths stay relative to those
roots. Existing frozen reports are never modified.

For a new proposal, copy the request to a new file, fill individual requirements
with `status: supplied`, a typed `value` and an identity-bound `evidence` file,
then select it with `--contract`. Keep the default request's missing values null.
A completed request is structurally ready for review and scoped analysis; contact
containment and provider claim applicability still require the existing evaluator
and technical review. File identity alone is insufficient.

The checker verifies the candidate, readback, retained power report, waveform
windows and unknown-bit summary against the frozen power manifest. Its activity
audit consumes recorded summaries without rerunning simulation or reauditing all
raw waveform/annotation bytes. The broader frozen
[power replay](../power-boundary/README.md) retains that evidence audit.

Focused controls:

```sh
python3 -B -m unittest discover -s test -p 'test_package_power_contract.py' -v
```
