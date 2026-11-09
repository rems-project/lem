# Consumer note for cerberus-lean: re-pinning to the unreferenced-binders lem (TODO item 54)

Date 2026-11-07. Worker [AGENT]; for the cerberus re-pin slice the orchestrator charters after the three
in-flight cerberus slices land. The lem-lean commits on `fix/unreferenced-binders` (base `b154377`): M1
`4a2a72e` (the backend, LemLib, the gate flags), M2 `2d9b36f` (the probes, the measurement), M3 `5362006`
(the record, the docs, this note), the pre-merge review `b8ba843` and its fix round `c846d39` (the code) plus
the docs commit carrying this text; the commit to pin is the ff-merged mainline head after the operator's
merge. The record: [2026-11-07_unreferenced-binders-record.md](2026-11-07_unreferenced-binders-record.md).

## 1. What changes for the consumer

- **Lean output only.** The generated OCaml is byte-identical (measured on the pinned sources: 86 of 86
  files, §3).
- **The generated Lean tree:** 52 modules change, in exactly three shapes and nothing else (every hunk
  classified at TOKEN level, §3): 147 `termination_by structural cmpx_`/`sizex_` lines removed (the derived
  comparison and size definitions that do not recurse), 601 pattern variables and parameters renamed
  `_<name>` (the source name kept under the underscore; a name already spelled `_x` is left as it is — no
  identifier gains a second underscore), 75 derived `Inhabited` constant-function binders `(fun (x<n> : T)
  => …)` → `(fun (_ : T) => …)`. These join the warnings Lake stored for the primary checkout's last build one
  for one: 601 + 75 = 676, 147 = 147. The per-module table is in §3.
- **Hand-written Lean:** none is expected to change. No hand-written file under `lean_frontend/`,
  `test/Unit/` or `speclab/` (171 files, read-only scan) passes a named argument to a parameter of a
  generated definition that the rule renamed; the fuel-forms tool finds `lemFuel`/`lemHyp` by NAME in the
  obligation statement (unchanged text) and compares the worker's arguments with the wrapper's by
  POSITION, so a worker parameter rendered `_x` is invisible to it; the measure proofs
  (`*_lemMeasureProofs.lean`) are stated over the wrapper and obligation binders (`binder_of`, unchanged).
  The two warnings in `CerbMem.lean` belong to the half-mirrors slice, not to this re-pin.
- **LemLib:** four regenerated lines (`List_extra.lean:39,47`, `Word.lean:197`, `Machine_word.lean:40`:
  `x :: _xs`, `_x :: xs`, `BitSeq _len s bl`, `(_x : itself a)`); no API or theorem change. The lem-lean
  packages now build with `-DwarningAsError=true`; cerberus may adopt the same line in
  `lean_frontend/lakefile.toml` once its tree is at zero warnings (this re-pin removes the 823 generated
  ones; the 2 hand-written ones are the other slice's).

## 2. The re-pin recipe (the container doc's pin dance; the two-repo order: lem-lean merged first)

1. From `cerberus-lean-proj/`: `git -C deps/lem-pinned reset --hard <merged lem-lean commit>`.
2. From `cerberus-lean/`: `scripts/ce opam upgrade --switch=. --no-depexts lem` (the path form, the local
   switch; `--no-depexts` in the sandbox). `lem -v` must then show the new hash.
3. The Lake pins. First edit the `rev` pinned in `lean_frontend/lakefile.toml`'s `[[require]]` block for
   `LemLib` (today `rev = "e6d8db5680962f49060257d6c2bcb13c284b910f"`) to the merged commit — with the `rev`
   pinned in the lakefile, `lake update` cannot move the manifest past it (review F2). Then, from each of
   the three packages with a manifest — `lean_frontend/`, `lean_frontend/speclab/`,
   `tests/mem-scale-probes/micro/` (the latter two carry no `rev` in their lakefiles, only in their
   manifests) — run `scripts/ce capped lake update LemLib` (`scripts/ce` for the `deps/gitconfig` redirect
   that resolves `LemLib` to the local lem-lean checkout — without it Lake tries GitHub and fails offline —
   and `capped` as for every lake invocation); the `rev` in each `lake-manifest.json` must then be the merged
   commit.
4. `scripts/fork_drift_manifest.txt`: the `lem-pin` value = the full 40-hex merged commit (the fork-drift
   gate compares it as a prefix of `lem -v`).
5. `scripts/ce make clean-prelude-src prelude-src lean-prelude-src` (the primary checkout follows the
   landing: regenerate from scratch, never over a stale tree).
6. Confirm the expected delta before building: `git status --short ocaml_frontend/generated` empty (the
   OCaml is byte-identical); the Lean tree's diff against the pre-re-pin generation is §3's table and
   nothing else. Classify at TOKEN level, not line level (review F6): a `_` makes a binder one character
   longer and the width-100 layout re-wraps lines, so a line diff shows re-flowed hunks (13–15 of them)
   that are token-identical apart from the three shapes — join each hunk's old and new lines, tokenize,
   and compare position by position: a removed `termination_by structural (cmpx_|sizex_)` line, an
   identifier that gained a leading underscore, or `x<n>` → `_` inside `fun (… : T) => default`; any
   other token difference, or any identifier starting `__`, is a finding against this lem commit.
7. Rebuild and gate: the OCaml side (`dune build backend/driver/main.exe cerberus-lib.install`, the
   install, `cerberus.install`), `capped lake build` in `lean_frontend/` and `speclab/`; the regenerated
   auxiliary modules import the hand-written measure proofs, which re-elaborate unchanged; run the named
   kernel-replay gate (`lake env leanchecker` over the measured modules and their proofs modules) and the
   fuel-forms gate (`test/Unit/FuelFormsTool.lean`) per `lean_frontend/VALIDATION.md`; ladder row 1 (the
   axiom censuses); the battery per `scripts/LADDER.md`.
8. Report the warning count after (derived from the build log): expected 0 in the generated tree and 2 in
   `CerbMem.lean` until the half-mirrors slice lands. A remaining warning in a generated module is a shape
   the rule misses — report it to lem-lean as a finding with the module and line; an `unknown identifier`
   error naming an underscored binder is a wrong rename — likewise (none is expected: the lem-lean suite
   builds at zero warnings and errors under the flag).
9. Stale artefacts: this re-pin adds and removes no module (the generated set is the same 172 files), so
   nothing under `lean_frontend/.lake/build/` needs deleting by hand; Lake rebuilds every changed module by
   trace, and the recipe's own `rm -f lean_frontend/generated/Core_unstruct*.lean` runs as always. Delete
   a `.olean`/`.ilean` only if it has no source module after the regeneration (none expected).

## 3. The expected delta (derived; generation only, no compile; §4.2 of the record)

Generated from the `frontend/` sources of cerberus mainline `1e5f2cbca` (extracted from the object store)
with the cerberus Makefile's exact `lem` flags, compared with the primary checkout's generated trees at
that commit (`frontend/` clean against it; the `lem` warning logs identical). OCaml: 86 files, 0 differ.
Lean, 172 files generated (the reference set minus its 57 hand-written copies), 52 modules differ:

| Module | `termination_by` removed | binders `_name` | Inhabited `x<n>` → `_` |
|---|---|---|---|
| `AilSyntax` | 4 | 0 | 0 |
| `AilTypesAux` | 0 | 15 | 0 |
| `AilTyping` | 0 | 1 | 0 |
| `Annot` | 6 | 3 | 0 |
| `Cabs` | 8 | 0 | 0 |
| `Cabs_to_ail` | 0 | 17 | 0 |
| `Cabs_to_ail_aux` | 0 | 2 | 0 |
| `Cabs_to_ail_effect` | 8 | 9 | 0 |
| `Cmm_aux` | 0 | 1 | 0 |
| `Cmm_csem` | 16 | 120 | 8 |
| `Cmm_op` | 0 | 22 | 0 |
| `Cn` | 10 | 1 | 0 |
| `Constraint` | 4 | 0 | 0 |
| `Core` | 2 | 2 | 0 |
| `Core_aux` | 0 | 23 | 0 |
| `Core_eval` | 0 | 10 | 0 |
| `Core_linking` | 0 | 1 | 0 |
| `Core_reduction` | 8 | 33 | 15 |
| `Core_reduction_aux` | 0 | 1 | 0 |
| `Core_rewrite` | 0 | 3 | 0 |
| `Core_run` | 6 | 41 | 1 |
| `Core_run_aux` | 0 | 2 | 0 |
| `Core_sequentialise` | 0 | 3 | 0 |
| `Core_typing` | 0 | 53 | 0 |
| `Core_typing_aux` | 0 | 5 | 0 |
| `Ctype` | 0 | 1 | 0 |
| `Ctype_aux` | 2 | 3 | 0 |
| `Defacto_memory` | 0 | 92 | 0 |
| `Defacto_memory_aux` | 0 | 20 | 0 |
| `Defacto_memory_types` | 2 | 0 | 0 |
| `Desugaring_init` | 6 | 1 | 6 |
| `Dlist` | 2 | 0 | 1 |
| `Driver` | 2 | 17 | 0 |
| `ErrorMonad` | 2 | 0 | 1 |
| `Errors` | 14 | 0 | 0 |
| `Formatted` | 4 | 5 | 0 |
| `GenTypesAux` | 0 | 1 | 0 |
| `GenTyping` | 2 | 45 | 0 |
| `Implementation` | 0 | 1 | 0 |
| `IntegerImpl` | 2 | 4 | 2 |
| `IntegerType` | 4 | 0 | 0 |
| `Mem` | 0 | 2 | 0 |
| `Mem_common` | 14 | 1 | 0 |
| `Mini_pipeline` | 0 | 2 | 0 |
| `Monadic_parsing` | 2 | 0 | 1 |
| `Nondeterminism` | 5 | 9 | 1 |
| `Scope_table` | 0 | 1 | 0 |
| `Symbol` | 4 | 1 | 0 |
| `Translation` | 2 | 24 | 0 |
| `Translation_aux` | 2 | 3 | 39 |
| `TypingError` | 2 | 0 | 0 |
| `Undefined` | 2 | 0 | 0 |
| **total (52 modules)** | **147** (29 modules) | **601** (41 modules) | **75** (10 modules) |

Every count joins the warnings Lake stored for the primary checkout's last build by module, line and name:
147 clauses = the 147 inert-clause warnings (per module), 601 + 75 = the 676 unreferenced-variable warnings,
nothing unmatched either way; the step-8 compile is the confirmation, not the resolution.
