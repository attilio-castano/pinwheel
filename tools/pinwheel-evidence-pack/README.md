# Receipt-bound local evidence packing

`pack.py` is host-only. It invokes no CAD, Docker, network, archive executable,
restore operation or image export. It reads an explicitly SHA-pinned selection
of settled native receipts and independent review anchors. It does not scan or
copy the whole dirty checkout, infer a clean Git state, or promote a partial
checkpoint.

The native receipt's `input_sha256` and `artifact_sha256` maps are authoritative.
The collector follows recursively referenced owned receipts and these declared
top-level metadata contracts: `source_sha256`, campaign protected/reference maps,
`staged_sha256`, `files_sha256`, and the overlay's regular-file/symlink maps.
Relative input/source paths use the selection's exact `origin_root`; artifact,
staged and helper-manifest paths use their document directory. Overlay paths use
`overlay_PDK_root`. Origin/helper provenance strings and arbitrary prose paths
are not treated as launch inputs. The three known native inventory filenames
(`inventory.json`, `native-inventory.json`, `source-inventory.json`) over 32 MiB
are copied as opaque blobs. Other JSON above that bound is rejected, so an
unknown document cannot silently conceal dependency maps. Nondependency native
telemetry retains its exact bytes, including duplicate telemetry keys; declared
dependency manifests use strict duplicate-key rejection.
Add any other required evidence explicitly as an anchor; this is a finite
declared-map closure, not a dependency inference engine.

Every selected or discovered owned receipt needs final status, exit code,
completed closeout, complete input/artifact maps, unchanged inputs and absent
ownership. Settled diagnostic failures can be retained, with their actual
failure status unchanged. Producer success, physical scope, DRC/LVS/timing and
scientific qualification remain separate. The pack seals bytes, not tapeout
acceptance.

The selection JSON has this structure. Every root path is absolute and every
root hash is pinned. The candidate checkpoint must be in the receipt closure.

```json
{
  "schema": "pinwheel-evidence-selection-v1",
  "origin_root": "/absolute/original/checkout",
  "receipts": [{"path": "/absolute/job/report.json", "sha256": "64 hex characters"}],
  "anchors": [{"path": "/absolute/independent-review.json", "sha256": "64 hex characters"}],
  "candidate": {"checkpoint": "/absolute/job/after/checkpoint.odb", "checkpoint_sha256": "64 hex characters"},
  "external_runtime": {
    "image_id": "sha256:64 hex characters",
    "observed_local_repo_digest": "captured from actual image inspect, not inferred from image ID",
    "packed": false,
    "remote_availability_proven": false
  }
}
```

Create a fresh selection after the final source/qualification choice. A running
C17 is excluded; its final receipt/artifacts may be selected only when settled.
Keep old selectors, receipts and original absolute paths unchanged. Record the
selection SHA independently, then inspect a size estimate without copying:

```sh
python3 -B tools/pinwheel-evidence-pack/pack.py plan \
  --selection SELECTION.json --selection-sha256 SELECTION_SHA
```

The plan is a stat/expected-map estimate, not fresh recustody. Full collection
checks every origin path against its expected digest, including duplicate
aliases, and writes at most one byte copy per SHA256:

```sh
python3 -B tools/pinwheel-evidence-pack/pack.py collect \
  --selection SELECTION.json --selection-sha256 SELECTION_SHA --out NEW_PACK
```

`NEW_PACK` must not exist. It contains `index.json`, `seal.json` and
`objects/sha256/<digest>`. Objects are regular byte copies, never hardlinks.
Record the emitted **seal SHA256 outside the pack**, then verify offline:

```sh
python3 -B tools/pinwheel-evidence-pack/pack.py verify \
  --pack NEW_PACK --seal-sha256 EXTERNALLY_RECORDED_SEAL_SHA
```

The verifier checks every object, index identity and the complete declared-map
closure without the original worktree. A later failure during collection leaves
a new unsealed directory; it is not overwritten or accepted as a finished pack.

For a lightweight final index/seal without payload copies, append `--index-only`
to `collect`. It still hashes every source path but creates no CAS objects. Its
later verification requires `--origins`; it is not a portable payload archive.
The exact runtime image and its Nix resources remain external in either mode.
An observed local RepoDigest does not prove future registry availability. Keep
the actual image-inspect anchor and native ELF/source/model identities, and
report the absence of an image export explicitly.

Symlinks retain their literal target text, resolved path and target-content
identity. The PDK overlay's directory symlinks are retained as metadata too;
regular target bytes come from its explicit manifest. The tool never creates
symlinks or writes to historical absolute paths. No restore command is provided.
With `--origins`, both file and directory links must still exist as symlinks,
with the same literal target, resolved path and file/directory kind. Offline CAS
verification checks the sealed historical bytes/metadata and does not claim
that current origin links are unchanged.
A later restore must use a fresh isolated directory, reject existing mismatched
paths and preserve original-path identity separately from any new replay
mapping. Expired campaign receipts must not be edited to permit a rerun: a new
authorized policy/window, new outputs and a reviewed relocation are required.

Host regressions use temporary synthetic bytes only:

```sh
python3 -B -m unittest discover -s tools/pinwheel-evidence-pack -v
```

Before closing a managed worktree, use the separate
[whole-build retention utility](WHOLE_BUILD_RETENTION.md) when earlier ignored
experiment outputs also need preservation. The receipt-bound CAS alone is not
an archive of every file under `build/`.
