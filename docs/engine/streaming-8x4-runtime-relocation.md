# Checking a restored October 22 CAD runtime

Use the historical audit hash from the trusted recovery record. Set
`RESTORED_RECOVERY` to the restored recovery directory and `AUDIT_OUT` to a
fresh directory outside it. The historical request and assembly must be present
at their recorded relative paths.

```sh
python3 scripts/streaming_8x4_relocate_runtime.py \
  --recovery "$RESTORED_RECOVERY" \
  --historical-report-sha256 "$HISTORICAL_AUDIT_SHA256" \
  --output "$AUDIT_OUT"
```

On success, `report.json` in the output directory records a fresh host custody
audit. The helper checks the tool identities and archive membership against the
historical audit after translating the old root to the restored path. It leaves
the historical receipts intact. A failure can leave diagnostic files in the
output directory. Use a new output directory for a retry. Physical timing and
CAD execution are outside the scope of this audit.
