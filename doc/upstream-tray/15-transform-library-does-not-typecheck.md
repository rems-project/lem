# 15 — `library/transform.lem` does not type-check: `unbound variable: find_non_pure`

Target: `rems-project/lem`, `library/transform.lem`. State: **Draft**, not
filed. Drafted 2026-10-03.

## Affected code (upstream `3802cb0`)

`library/transform.lem:213`, in the `List` transformation section:

```lem
  let lem_transform find = find_non_pure
```

`find_non_pure` is not defined anywhere in the library; the function in
`library/list_extra.lem:133-136` is `findNonPure`. The file's header
(`:1-8`) describes it as the tool for transforming "old lem" sources
(`open import Transform`, then `lem -lem`). It is not in the library's
`LIBS` list, so the library build does not check it. lem-lean's copy has
the same line at 220.

## Classification

**TRUE BUG** (minor). The file cannot be loaded, so the documented
transformation workflow fails at its first step. The fix is a rename.

## Reproducer

`user.lem`:

```lem
open import Transform

let x : num = 1
```

## Verbatim output

Captured 2026-10-03, upstream Lem `3802cb0` (`lem -v`: `Lem 3802cb0`);
conventions in README §4. First the library file itself, from
`library/`, then a user file:

```
$ (cd $LEMSRC/library && lem -lem -outdir <scratch> transform.lem)
File "transform.lem", line 213, character 28 to line 213, character 40
  Type error: unbound variable: find_non_pure
[exit 1]
$ lem -lem -outdir out user.lem
File "/home/dev/projects/linksem-lean/deps/lem-upstream/library/transform.lem", line 213, character 28 to line 213, character 40
  Type error: unbound variable: find_non_pure
[exit 1]
```

(`$LEMSRC` is the upstream checkout; full transcript
`repro/transform/transcript-2026-10-03.txt`.)

## Observed vs expected

Observed: type error, exit 1. Expected: the file loads and `user.lem` is
processed.

## Impact

The "old lem" transformation library is unusable. `git log` shows
`transform.lem` last changed in `64c0d3a` (2013-11-26), and
`find_non_pure` renamed to `findNonPure` in `list_extra.lem` by `600d172`
(2014-02-25, "Fixed naming scheme in Lem list library, moved things
around"), which did not touch `transform.lem`. Whether the file is still
wanted is for the Lem authors to decide.

## Proposed remedy

`let lem_transform find = findNonPure`; or delete `transform.lem` if the
workflow is retired. Checked 2026-10-03 on a scratch copy of the upstream
library (`LEMLIB` pointing at it): with that one-line change,
`lem -lem transform.lem` and `lem -lem user.lem` both exit 0 (the latter
writes `user-processed.lem`). Whether the transformations themselves are
still right for today's library was not checked.

## Origin

lem-lean mainline `doc/lean-backend/2026-09-30_library-parity-coverage.md`
§2, paragraph "`lnot` at `nat` is not a reachable discrepancy (correction,
review round 2)": "`library/transform.lem`, which does not typecheck
("Type error: unbound variable: find_non_pure") and is not in the library
build". That record is [AGENT] work; the tray scope is the [USER 2026-10-03]
ruling: all 16, re-verified.

## Provenance

Found and analysed by AI agents (Claude, Anthropic) working under the
direction and review of a human operator. Any filed issue must say so
(INDEX.md, "Provenance labelling").
