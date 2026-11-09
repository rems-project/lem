# The synthesized-name (reserved-binder) contract (arc-14 re-mark, be:S2)

Date: 2026-08-22. Status: normative for the Lean backend's synthesized
binders. Enforcement: the generation-time reserved_binder_check in
src/lean_backend.ml (located, fail-closed) + the negative probes
tests/comprehensive/negative/neg_fuel_shadow.lem /
neg_reader_shadow.lem; the none-binder class is separately pinned
POSITIVE (the avoid machinery renames it —
tests/comprehensive/test_name_capture.lem + TestNameCaptureCheck.lean).

## Reserved (user parameters may not use these; checked)

| name | synthesized by | shadow failure mode (pre-check, measured) |
|------|----------------|-------------------------------------------|
| `lemFuel` | fuel'd workers (`declare {lean} fuel val`) | the worker matched the USER's binder: `shadow_probe 0 3` returned the 999 sentinel (probe 2026-08-22) |
| `_lemReader_*` (prefix) | reader lifting / reader_seed injection | the injected leading parameter is shadowed by the user's |

Checked for every fuel'd, seed-marked, or reader-lifted def: clause
PARAMETERS (Pattern_syntax.pat_vars_src) AND every binder inside the
compiled clause BODY (exp_bound_names — match/let/fun/do/quantifier
binders; arc-14 re-mark RG1, closing professor A's hole: pre-RG1 a
body-level `(_lemReader_amb, y)` tuple binder COMPILED AND RAN silently
wrong — use2 100 (1,2) = 5 instead of 103 — and a body-level lemFuel
tuple binder shadowed the fuel; both are now the negative probes
neg_fuel_shadow_body.lem / neg_reader_shadow_body.lem).

## Registered residuals (documented, not yet checked)
- Worker-name collisions (`<f>_lemFuel` vs an existing def of that
  name) and the derived-code-internal families (`x<n>`, `cmpx_`/`cmpy_`,
  `<T>.beq_derived`, `<T>.<kind>_deriv_aux<n>`, `default_inhabited`,
  `ctor_rank_ocaml`) — internal to generated modules, no user-binder
  interaction surface; loud Lean duplicate-definition errors if ever
  wrong.

## Not reserved (defended differently)

Constructor-named binders (`none`, `some`, `true`, `false`, …): lem's
avoid machinery RENAMES them (`none` → `none1`) in both pattern and
body — probe-measured correct; pinned as a build-failing regression
guard (TestNameCaptureCheck).
