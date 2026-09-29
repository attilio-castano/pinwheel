# Replaying diagnostic connection reports

The diagnostic reader distinguishes a measured violation, an absent library
bound, and incomplete evidence. An absent maximum fanout bound remains `null`;
capacitance, slew, load counts, and both timing directions are still required.
A successful replay establishes agreement with saved measurements, not physical
qualification.

[`parse_diagnostic_measurements`](../../scripts/physical_organization.py) derives
the permitted absences from the exact physical driver and its corner-specific
Liberty pin. It includes inherited bus/range/bit attributes and the owning
library's `default_max_fanout`. Standard-cell drivers retain strict requirements.
`default_fanout_load` describes load weighting and is not a maximum fanout bound.
Malformed present report sections always fail.

The exception is restricted to the reviewed comparison SDC, whose SHA-256 is
`860a5afd856cc92bbecc838b147a9f7c8259abd66bcd62c0f211cb7e8edc4db1`.
That program supplies no fanout constraints. A different SDC keeps strict
behavior until its constraint semantics have been reviewed; the reader does not
attempt to interpret arbitrary Tcl. The caller must bind the SDC and libraries
actually used by the pinned comparison flow. This policy does not authorize
omissions for flows with additional constraint scripts.

Both organization diagnostic commands use this adapter, including the family
and parent-net replay paths in `report-physical-organization.py`. Reports list
absent fanout bounds explicitly. Routing/admission readers remain strict, and
the distribution acceptance gate rejects a missing required numerical bound.

## Standalone replay

Use the committed command to replay saved connection measurements without the
experiment's local analysis script or a new CAD run:

```sh
python3 -B scripts/replay-physical-connections.py \
  --request /path/to/replay-request.json \
  --output /path/to/new-replay-receipt.json
```

The schema below shows a one-corner request. Each reference has exactly `path`
and `sha256`; use the digests from the retained collection's manifest. Paths are
absolute or relative to the request file. Include every saved corner and every
declared connection. `measurements.json` maps corners to net measurement rows.

```json
{
  "schema": 1,
  "context": {"path": "context.json", "sha256": "<retained SHA-256>"},
  "sdc": {"path": "core.sdc", "sha256": "<retained SHA-256>"},
  "measurements": {"path": "measurements.json", "sha256": "<retained SHA-256>"},
  "connections": ["memory.mem_q0[51]", "memory.mem_q0[53]"],
  "corners": {
    "nom_typ_1p20V_25C": {
      "libraries": [
        {"path": "stdcell_typ.lib", "sha256": "<retained SHA-256>"},
        {"path": "sram_typ.lib", "sha256": "<retained SHA-256>"}
      ],
      "report": {"path": "connections.rpt", "sha256": "<retained SHA-256>"}
    }
  }
}
```

The command checks all referenced bytes, independently derives allowed absences,
reparses the raw reports, requires exact equality with the saved measurements,
and verifies that inputs stayed unchanged. Its receipt records source/input
hashes, connection/corner coverage, missing bounds, and
`physical_qualification: false`. An existing output is never overwritten.
Hash binding verifies identity; the retained collection owns provenance and
scope. Historical ignored artifacts and pinned libraries are still required.

## Regression checks

```sh
python3 -B -m unittest discover -s test -p 'test_physical_connection*.py' -v
python3 -B -m unittest discover -s test -p 'test_physical_organization*.py' -v
python3 -B -m unittest discover -s test -p 'test_physical_distribution_acceptance.py' -v
```

The command-level fixture contains a standard-cell driver and two SRAM outputs
in three corners. Controls reject missing required limits, malformed sections,
changed drivers, constrained macro pins, library defaults, unknown SDC programs,
stale hashes, incomplete corners, and changed saved values. A separate
qualification regression ensures that a preserved `null` bound cannot pass
admission.
