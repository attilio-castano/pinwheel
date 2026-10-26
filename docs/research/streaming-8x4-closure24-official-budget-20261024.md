# One explicit official resource replay

The original official attempt stopped on its memory guard, not on timeout and
not with a DRC verdict. Its unchanged main foundry deck had not completed. The
resource receipt reports `Container approaching memory limit`, stopped/124,
1,743.422 seconds elapsed, confirmed cleanup and unchanged inputs. The final
retained container sample is 90.92% of 2 GiB; the guard rejects a later reading
at or above 95% before appending that failed observation. No kernel OOM claim
follows from this guard result.

The first pin-label KLayout call completed in 1.32 seconds. The native journal
has three records: that intent/result pair and the unclosed main-deck intent.
The worker reports `KeyboardInterrupt: signal 15` and 1,736.038 seconds, with
`executed=false`, `passed=false`, cleanup absent and input/PDK/runtime seals
unchanged. The coordinator's interrupted-path capture does not retain a
`precheck.log`; existing receipts, journal and pin-label report are preserved.

The exact failed worker report SHA256 is
`d62014b6dfe17ab47a1662a5f7c92a744048a285bbe6fea99e62553b238bbd02`;
resource receipt SHA256 is
`abeecc53edb77728efa327a3f880c2dfec246e63b363a7e21de0bbb6f6bb4f02`.
The new preparation requires these exact measured-failure identities and the
same closed final views/candidate. It cannot reinterpret their prefix as a
completed official check or DRC failure.

## Unchanged execution scope

Official support commit `d66cf179e7bc4d296362ab7e2e3b344dc3c4f665`
selects all nine applicable checks in their original order and three fresh
Native KLayout calls. The main deck is the actual
`ihp-sg13cmos5l.drc`, SHA256
`12b03e309986ed7f079ca9283eb29d6635918f53ddd09c3c82ea232cca739567`.
It is not the unused minimum-rule deck described elsewhere in support notes.
No rule switches are disabled. Default main tables, FEOL, BEOL, off-grid, angle,
pin, forbidden and recommended checks are retained; `precheck_drc` is false.

The official source passes `thr=1`. The main foundry deck reads `$threads` and
defaults it to `Etc.nprocessors`, so this flag is not proof of one internal
worker thread. The container CPU quota is exactly one. With no `run_mode`
argument, the deck's initial DSL branch selects deep mode; the unset variable
also makes the layer helper use `ps.merged`, and source-default large-layout
rules can temporarily select tiling. All these exact source/default behaviors
remain unchanged. No explicit mode, thread, deck or numerical flag is added.

The new separately typed resource context changes only:

| Resource | Original attempt | One new attempt |
| --- | --- | --- |
| Native CPU quota | 1 | 1 |
| Native memory / memory-plus-swap | 2 / 2 GiB | 6 / 6 GiB |
| Extra swap / tmpfs | 0 / 256 MiB | 0 / 256 MiB |
| Whole official precheck coordinator budget | 1,800 s | Fixed 3,600 s |
| Outer supervisor / host RSS ceiling | 1,860 s / 2,048 MiB | 3,660 s / 2,048 MiB |
| Per-job campaign ceiling | 14,400 s | 14,400 s |

This provides more measured-resource headroom; it does not guarantee completion
or a passing design. Every check and Native call must execute fresh. No cached
pin-label result, successful prefix, skipped case, alternate rule deck or
partial journal can pass.

## New source and custody

`streaming_8x4_closure24_official_budget.py` derives an isolated controller from
the exact frozen source and exposes the full deterministic diff. It derives
two distinct Native functions from the unchanged signoff helper: the launcher
and journal reader change only their `2g` memory/swap tokens to `6g`. The old
2 GiB reader stays unchanged and rejects the new 6 GiB journal. A typed Native
configuration is mandatory for the new wrapper.

`streaming_8x4_closure24_official_replay.py` exposes only preparation,
verification, proposal and the one fixed full attempt. Actual execution still
uses the unchanged commit-first `stage_producer`: each of the complete 68
source files must match `git show` before staging. HOST preparation does not
stage executable producers or bypass that gate. The wrapper imports the newly
staged helper, so all three new files are in the copied producer closure and
resource input seals. Historical sources and the failed attempt remain intact.

`streaming_8x4_closure24_official_readback.py` independently checks the complete
ordered nine-case XML, exact closed three-call 6 GiB journal, all same-target
copied design files, Python/runtime/support identities, staged committed
producers, immutable inputs and the actual fixed-parent/shared-lease/resource
context. A stopped attempt is retained as incomplete; its partial journal
cannot confer a passing verdict. Official omissions still include qualified
timing, transistor LVS, antenna and CMOS5L power-pin checking.

Ten portable controls pass normally and with `python3 -O`. They execute no
KLayout or Docker. They compare complete Native function bodies and controller
source after only declared adaptation normalization; test strict 6-versus-2 GiB,
CPU/swap/mode/flag differences, complete check/journal membership, skips,
original namespaces, fresh-output admission and exact resource/custody joins.

Fresh HOST preparation03 has plan SHA256
`d23284b98af8bdad4865c5ff16d208eedde5ff0e0ef449cfffd54aca2355f4e2`;
proposal SHA256
`c27f9db6cf144137e2fcce3e46bce545b1fd129a9508ed347219c39579352047`;
launcher SHA256
`6b1b2c448a520fdc8da507291f7bc822116523a73c3af731a3c6da13ddae6d5a`.
It binds 68 sources and 100 supervisor input paths. Preparations01/02 are
preserved unexecuted/superseded after HOST resource-reader tightening.

No new Root GO, producer staging or Native attempt exists at preparation time.
Following independent review and Root's commit/GO, only Root may execute the
saved `resource_supervisor_argv` in
`final24-official-budget-launch-reopen-03.json`. The new attempt owns
`final24-official-budget-01`. After terminal cleanup and Root's signal, the saved
`HOST_closeout_argv` writes
`final24-official-budget-independent-readback-03.json`. The full official result
is one gate; physical acceptance, extracted timing and full model qualification
remain separate.
