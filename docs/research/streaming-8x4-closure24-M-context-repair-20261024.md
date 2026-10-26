# Fresh actual-M source-N context adapter

The first actual-target M generation attempt failed before any Lean execution.
Its preserved `final24-M-01/producer/generate.py` references
`bound_path(prepared['worker_config'])` after the earlier relocation adapter
removed that local `prepared` binding. The original GEN04 intentionally included
the original source-N worker configuration in its custody inputs. The failure
is an orchestration/context bug, not a mathematical counterexample. M01 and
every original producer, request, receipt and output remain unchanged.

The intended configuration is the historical N worker configuration. It is
different from the new final public-wire configuration and from the relocated
in-memory generation configuration. The exact authority chain is:

| Authority | SHA-256 |
| --- | --- |
| Relocated N02 report | `f97c0046afa824f3f8ca5fe5a8c6929fcd96f7b5430be9213f1b9e140eef6216` |
| Original N prepared receipt | `9205b15a9efec38ee72c8f4e21e4971883faac9a63fdf5881caa4d276d9d1113` |
| Original/restored worker-config bytes | `d43a1ead636a48c3a42a60010b4f5f93e7969b24f20966c4b18a677bebf73adb` |
| Config-owner archive metadata | `76c5222965115c3105dbfaba2f4e581772f13e35e12283d96d02d178bf2cf8e6` |

The original receipt names
`/Users/attiliocastano/.codex/worktrees/1373/pinwheel/build/validation/streaming-tt-balanced-device-02/worker-config.json`.
The restored, byte-identical file is under
`build/campaigns/8x4-20261022-01/recovery/final-N-config/build/validation/streaming-tt-balanced-device-02/worker-config.json`.
Neither historical path claims nor historical JSON are rewritten.

`streaming_8x4_closure24_m_context.py` calls the unchanged N verifier, checks the
original prepared receipt and its exact worker-config binding, checks the
restored consumed-input seal, and reopens the unique `final-N-config` archive
metadata row joining original `wt1373` path, restored relative path and hash.
The typed context records those original and restored authorities separately.
The existing complete dependency context is extended with that verified
`source_worker_config` binding. Its full input map already contains the file;
the explicit GEN04 custody use is retained rather than dropped.

The new generated source replaces exactly one expression:

```diff
-bound_path(prepared['worker_config'])
+bound_path(dependency['source_worker_config'])
```

The exact final-target admission, all6039 transitions/state pairing, all24
outputs, clock/reset DAGs, packing, initialization, mathematical source body,
module partition/order, generated namespace and final audit remain unchanged.
Static scope checking covers every top-level generated function; the undefined
`prepared` reference is removed without a dummy receipt or expected-path stub.

The new generation and execution entry points are
`streaming_8x4_closure24_context_m.py` and
`streaming_8x4_closure24_context_m_execute.py`. They deterministically adapt the
exact pinned existing controller bodies into isolated module namespaces. This
reuses the complete implementation without editing its files or redirecting
its existing globals. `controller_source('generation')` and
`controller_source('execution')` return the complete adapted text and unified
diff for review without running generation. The base controller hashes are:

| Immutable controller | SHA-256 |
| --- | --- |
| `streaming_8x4_closure24_final_m.py` | `37743b7d1ee01d49df3816e225b19534f28384a83714ce0d6586031af8186bad` |
| `streaming_8x4_closure24_final_m_execute.py` | `a37202d67f3f0b99ad94de501c51bea7b1263d02c05371696f4315a4a36f6346` |

New preparation/generation/positive/private schemas use the
`pinwheel.closure24-context-...` scope. Preparation and the generation manifest
both bind the typed source-worker context; reopening independently derives and
compares it. The complete original dependency recheck at the end of GEN04
generation still runs. The new helper, both new entry points and both immutable
base controllers are included in the committed producer seals.

Complete source rederivation before Native, fresh generated-stage ownership,
all imports/object membership, complete14923-file runtime observations before
and after execution, full positive owner audit and the separate unused-private
axiom pair remain mandatory. Native compiler arguments,180-second default and
six exact600-second module allowances,4GiB/one-thread proof limits and the
four-hour positive job cap are unchanged. A prefix or positive-only receipt
cannot claim final correspondence.

Eleven portable HOST controls pass normally and with `python3 -O`. Controls
include wrong original receipt/path/hash, missing consumed seal, wrong or
ambiguous archive mapping, source identity, unresolved names, whole GEN04 byte
identity after the one custody repair and typed names, unchanged Native
algorithm ASTs/helper identities, owner isolation and exact budget reuse.
Fixtures do not read ignored campaign artifacts. A separate read-only actual
N binding check completed in1.39s and confirmed the exact original/restored
configuration and archive metadata above.

This is source preparation only. No new M generation, Lean execution, Root GO,
proof pass, physical acceptance, model qualification or timing qualification is
created by this adapter. Root must review and commit the new sources before a
fresh guarded generation owner; the original failed M01 must never be reused.
