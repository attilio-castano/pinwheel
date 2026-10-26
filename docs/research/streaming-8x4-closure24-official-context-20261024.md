# Separate prior-view authority and official replay producer

The first 6 GiB replay controller failed in HOST context before creating its
output directory or starting KLayout. The guard closes failed/1 in 10.528
seconds with unchanged inputs and confirmed cleanup. Its report SHA256 is
`7f7b9665ddfde28570bee061641ee1fa15b10e233af24d623a903df05d484b9b`;
the preserved traceback SHA256 is
`049553a9681c2bcfacf4c017f7e4be9c243eda51a0edbd70b923aa8cf9596663`.
It ends at `Final view producer dependency membership differs`. No 6 GiB Native
attempt was consumed and `final24-official-budget-01` remains absent.

The cause is a producer-context collision. The resource adapter appends its
three new files to `SOURCE_ENTRIES`, giving its staged replay producer 68 files.
The cloned `closed_views` and `verify_views_preparation` functions also read that
same expanded global, although the immutable final-view receipt correctly
authenticates the original 65-file producer. Neither receipt was wrong; those
two independently valid source universes were compared as if they were one.

The new context adapter keeps both exact memberships. Its owned isolated
controller explicitly binds:

```python
closed_views = S.OLD.BASE.closed_views
```

That function retains its unchanged original module globals and exact 65-file
preparation/metadata equality. The new replay producer separately includes the
old 68 files plus its three new files, giving 71. No original module globals,
source files, metadata equality or failed receipt is redirected or rewritten.
The complete controller and reader context diffs are available for inspection.

`streaming_8x4_closure24_official_context.py` explicitly exports the unchanged
6 GiB `native_klayout` and `native_journal` functions. This is necessary because
the staged wrapper calls `runpy.run_path(...)["native_klayout"]`; module
`__getattr__` delegation alone does not populate that returned dictionary. The
matching entry and reader are `streaming_8x4_closure24_official_context_replay.py`
and `streaming_8x4_closure24_official_context_readback.py`.

Eight portable controls pass normally and with `python3 -O`. They extract the
actual immutable-view membership predicate and reproduce the 68-versus-65
failure, require authority/producer separation, compare the complete adapted
controller/reader after only the declared custody changes, preserve old module
globals and test exact no-output/failed-source seals. A temporary unittest
fixture copies the complete 71-file source closure and exercises the exact
staged-wrapper `runpy` import path in a clean isolated HOST Python process. It
checks both explicit function dictionary keys and their staged source root;
it invokes no Native function. This is not executable producer staging and does
not bypass the unchanged actual `git show` commit-first stage.

Crucially, HOST preparation also exercises the real new controller's
`closed_views` callback on the actual `final24-views-01/report.json`. Its result
must equal the unchanged base callback's result, with the exact original
producer dependency metadata retained. That live preflight passed: 65 authority
files, 71 replay files, views SHA256
`97666bf7dee7da0d7e2b1d241134f4e591b46e1c9af2bdb257bb883b8096e198`.

Fresh context preparation01 binds the failed 68-file plan/proposal/launcher,
actual failed guard and traceback, original 2 GiB memory-stop evidence, same
closed views and all 71 new producer identities. Its plan SHA256 is
`59e054ed3aa00784b1f64e14586f77ad2e907f97950486467083799be83c36e7`;
proposal SHA256
`31648b3a2640a949042debaab90b7fc44395c4c96dbce9f1cbfa67505a8238dc`;
launcher SHA256
`f5bc27433d0d7312d41089b13387267122a43e9aa844050c2f5f4ac5e3867d4f`.
The launcher has 107 unique resource input paths. Preparation and proposal
reopening together took 29.38 HOST seconds. No Root GO or Native invocation
exists at this preparation checkpoint.

The single permitted full Native attempt remains exactly one CPU, 6 GiB
memory/memory-plus-swap, no additional swap, unchanged 256 MiB tmpfs, fixed
3,600-second whole-precheck and 3,660-second outer guard. All nine official
checks and three fresh Native calls, support/deck bytes, mode/thread/default
flags, result readers, numerical checks, cleanup and four-hour ceiling remain
unchanged. Only new ownership/schema/custody context differs. The old 2 GiB
reader stays strict and no prefix can pass.

After independent review and Root's commit/GO, Root may use the saved
`resource_supervisor_argv` in `final24-official-context-launch-reopen-01.json`.
The fresh Native owner is `final24-official-context-01`. Following terminal
cleanup and Root's signal, `HOST_closeout_argv` writes
`final24-official-context-independent-readback-01.json`. Both older failures
remain failed/incomplete. Official precheck is one gate and does not imply
qualified timing, LVS, antenna, power or full model acceptance.
