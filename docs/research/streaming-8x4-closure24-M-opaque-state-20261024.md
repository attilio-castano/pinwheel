# Complete-M opaque scheduling-state observation

Scheduling state is telemetry, not a proof acceptance predicate. The latest
attempt demonstrated that a semantic state allowlist was the wrong boundary.
The canonical compiler exited0 and its process group closed for index2
`PhysicalFrontendWord2Values` in1.099s, but the observer then rejected the raw
state token `?Es`. That entire attempt remains failed. Its two reported modules
and third retained exit0 object cannot be reused for complete acceptance.

The exact inner report is `21b5562c474dcb146c587527bbe81bd85591935e3e9355123db5d7b4d80dfbfb`;
the resource report is `1ff419e6f80549ce5e2765a606a3b0fc5b6ff16cd6764f786159d2025c9e7a44`.
The resource failed1 normally in173.519s, with cleanup and input closure. This
was neither a memory stop nor a compiler failure. The complete rederivation
child passed in128.205607s and closed before compilation. That is historical
evidence only; the next complete attempt requires its own fresh source/object
owner and complete independent child rederivation.

The raw memory journal SHA79bdd251c0d63a51b2f69751995d99ded497f280cac65a563e6267108d9a3602
retains at1.018012s: parent15376 with full absolute Python command/state `Ss`,
child17053/PPID15376/PGID17053/birth `Sat Oct 24 17:50:40 2026`, kernel RSS0,
state `?Es` and command `(lean)`. Kernel RSS0 is an observed datum; it is not
invented memory evidence for an unavailable command identity. The separate
canonical result journal SHA602c1517c02bf9af4d65dd3007e499b86df858cd700d3c4c60b0439a63c5f146
preserves all three exit0/group-closed results. Complete correspondence remains
false, including for the two earlier failed observer families and memory stop.

Apple primary [tasks.c](https://github.com/apple-oss-distributions/adv_cmds/blob/6bed8737a34dbb54782a18f47dccf933a9967a12/ps/tasks.c)
defines `STATE_MAX=7`, initializes task state to7 before task-inspection error
returns, and maps its thread/task states through `" RUSITH?"` (lines30–48,
98–113,233–235). The retained [print.c formatter](https://github.com/apple-oss-distributions/adv_cmds/blob/6bed8737a34dbb54782a18f47dccf933a9967a12/ps/print.c)
uses SSTOP→T, SZOMB→Z, otherwise that table, then appends nice `<`or`N`, traced
X, non-zombie exiting E, V,L,s,+ in order (450–511). Thus `?Es` is source
supported; it does not establish zombie/death. Argument collection independently
prints `(p_comm)` on sysctl/allocation/parsing fallback (299–303). Which exact
task-inspection or argument failure occurred in this capture is unknown.

The new immutable four-file intake is
`build/campaigns/8x4-20261024-01/m-observer-comm-source-03/manifest.json`,
SHA4fa092b43ab6465347ad1feef9d7f3651f69032a7847b310dfdb06979bde9a56.
Its new tasks.c SHA56d7b23faa1f6387fa7f53561d4ecd7011ada80af9f39346d58d803b84e9432d
has independently matching observed/computed Git blob
d2fcb07b422cfbb12718f048856e0575eb0237d0. The three-file source02 intake remains
byte-identical and separately bound. Installed `/bin/ps` is hash-bound, while
equivalence to that particular Apple source release remains explicitly unproven.

The new `m_process_ps` observer accepts any1–15-character ASCII-printable
nonwhitespace scheduling token, retaining it exactly. This is bounded input
syntax, not a state enum; the pinned formatter uses a16-byte buffer. The only
state interpretation retained is explicit leading Z, for terminal zombie
handling. Parse, snapshot, full-identity checks, parent/sample validation,
startup and journal reopening all apply this same contract. In particular:

- An absolute observed argv can supply full identity regardless of a non-Z
  scheduling token. No unknown state is inferred to mean live or dead.
- An exact `(expectedcomm)` child token under any non-Z state means unknown
  executable/argv/identity-qualified memory. Raw state and kernel RSS remain.
  It does not supply full-command coverage or replace unknown fields with the
  expected compiler or last observed command. Full→unknown→full is permitted
  only with unchanged PID/PPID/PGID/birth and all known full identities.
- Parents must be present, have full absolute identity and not be explicit Z.
  Relative commands, wrong comm roles, changed lifetime or changed known argv/
  executable still reject. Explicit Z remains terminal; no Z→non-Z revival.
- Required long-child coverage needs an actual full-command witness. Fast
  absent/Z/fallback-only compiler observations remain explicitly unknown under
  the existing finite-sampling allowance. Canonical child wait/exit/group
  closure, exact source/import/runtime checks and the outer aggregate RSS guard
  retain their authority. Scheduling telemetry never replaces those gates.

`m_ps_isolation` and `ps_m_execute` are separate typed source families. Their
operational callbacks are compiled into fresh namespaces using the new observer
for both the complete rederivation barrier and every positive/private compile
and reader. Exact body-normalization controls preserve the full mathematical
GEN04/6039state/24output/3966module plan, independent `M.verify(True)`,14923-file
runtime before/after checks, imports, complete positive audit, separate private
pair,180/600s module limits,4h whole job and4GiB aggregate/one-thread limits.
Canonical results remain durable before observational failure. Historical
context checks hashes and input maps without recursively loading old logical
verification graphs in the parent. All previous source/receipt bytes stay fixed.

Portable controls reproduce the exact old `?Es` rejection, replay that capture
with unknown command metadata, cover1632 primary formatter paths/flag
combinations, and admit other bounded printable states without an allowlist.
They cover every startup/identity/reader API, kernel-zero versus unknown memory,
full↔unknown metadata, explicit-Z terminality, strict parent/lifetime/known
identity/relative-command rejection, raw-before-error persistence, canonical
exit0 persistence, exact source/global ownership and unchanged complete proof
bodies/budgets. They run no Lean, CAD or mathematical source generation and
establish no complete-proof, physical, timing or model qualification.
