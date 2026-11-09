#!/bin/sh
# Non-Lean output regression net (m2 of the 2026-08-31 backend quality
# review; effect-retirement charter L0 item ii).
#
# The Lean backend fork must not disturb the other emitters. This net
# generates the library corpus (library/*.lem, the LIBS list) and every
# tests/backends/*.lem source for the 9 non-Lean emitters
#   ocaml hol isa coq html tex lem ident tex_all
# into a scratch tree, records every produced artifact (generated files,
# captured stdout/stderr, and per-run exit codes), and compares sha256
# manifests against the committed goldens:
#   tests/nonlean-regress/golden.sha256     (one row per artifact)
#   tests/nonlean-regress/golden.exitcodes  (one row per lem run)
# ANY drift — changed bytes, missing or new artifact, changed exit
# code — fails loudly, naming the target and file (the differing
# manifest rows are printed). A run that produces implausibly few rows
# also fails (vacuity guard): a broken corpus must never pass silently.
#
# Rebaseline ONLY for a reviewed, intended output change:
#   NONLEAN_REGRESS_REBASELINE=1 tests/nonlean-regress/run.sh
# and commit the regenerated goldens with the change that justifies them.

set -u

ROOT=$(cd "$(dirname "$0")/../.." && pwd)
LEM="$ROOT/lem"
NET="$ROOT/tests/nonlean-regress"
GOLDEN_SHA="$NET/golden.sha256"
GOLDEN_EXIT="$NET/golden.exitcodes"
SCRATCH="$NET/.scratch"
REBASELINE="${NONLEAN_REGRESS_REBASELINE:-0}"

# Minimum plausible row counts (derived from the baseline size; the
# guard is against vacuous passes, not an exact pin — the manifest
# comparison is the exact pin).
MIN_SHA_ROWS=400
MIN_EXIT_ROWS=200

fail() { echo "nonlean-regress: FAIL: $*" >&2; exit 1; }

[ -x "$LEM" ] || fail "lem binary not found/executable at $LEM (run make first)"

rm -rf "$SCRATCH"
mkdir -p "$SCRATCH"
EXITS="$SCRATCH/exitcodes"
: > "$EXITS"

# The library corpus, verbatim from library/Makefile LIBS.
LIBS="bool.lem basic_classes.lem function.lem maybe.lem num.lem tuple.lem list.lem either.lem set_helpers.lem set.lem map.lem relation.lem sorting.lem function_extra.lem assert_extra.lem list_extra.lem string.lem num_extra.lem map_extra.lem set_extra.lem maybe_extra.lem string_extra.lem word.lem show.lem show_extra.lem machine_word.lem pervasives.lem pervasives_extra.lem debug.lem"

DIR_TARGETS="ocaml hol isa coq html tex lem ident"

record_exit() { # label rc
  printf '%s %s\n' "$1" "$2" >> "$EXITS"
}

# --- library corpus ---------------------------------------------------
cd "$ROOT/library" || fail "no library/ dir"
for t in $DIR_TARGETS; do
  out="$SCRATCH/lib/$t"
  mkdir -p "$out"
  extra=""
  [ "$t" = hol ] && extra="-hol_remove_matches"
  # shellcheck disable=SC2086
  "$LEM" -"$t" $extra -outdir "$out" -wl ign -wl_auto_import err \
    $LIBS -auxiliary_level none \
    > "$out.stdout" 2> "$out.stderr"
  record_exit "lib/$t" $?
done
out="$SCRATCH/lib/tex_all"
mkdir -p "$out"
# shellcheck disable=SC2086
"$LEM" -tex_all "$out/lem-libs.tex" -wl ign -wl_auto_import err $LIBS \
  > "$out.stdout" 2> "$out.stderr"
record_exit "lib/tex_all" $?

# --- tests/backends corpus -------------------------------------------
cd "$ROOT/tests/backends" || fail "no tests/backends dir"
found_backend_src=0
for f in *.lem; do
  [ -f "$f" ] || continue
  found_backend_src=1
  base=$(basename "$f" .lem)
  for t in $DIR_TARGETS; do
    out="$SCRATCH/backends/$t/$base"
    mkdir -p "$out"
    "$LEM" -"$t" -outdir "$out" -wl ign "$f" \
      > "$out.stdout" 2> "$out.stderr"
    record_exit "backends/$t/$base" $?
  done
  # tex_all over a single file (the 9th emitter, single-file form)
  out="$SCRATCH/backends/tex_all/$base"
  mkdir -p "$out"
  "$LEM" -tex_all "$out/$base.tex" -wl ign "$f" \
    > "$out.stdout" 2> "$out.stderr"
  record_exit "backends/tex_all/$base" $?
done
[ "$found_backend_src" = 1 ] || fail "tests/backends contains no .lem sources (corpus vanished)"

# --- path normalization ----------------------------------------------
# tex_all outputs (and some error messages) embed ABSOLUTE library
# paths; rewrite the repo root to a fixed token so the manifest is
# byte-identical across checkouts/worktrees.
find "$SCRATCH" -type f -exec sed -i "s|$ROOT|LEMROOT|g" {} + \
  || fail "path normalization failed"

# --- exit-code list: locale-independent order -------------------------
# The per-run exit rows were appended in `for f in *.lem` glob order,
# which depends on the locale's collation (measured 2026-09-04: `classes`
# vs `classes2`, `indreln` vs `indreln2` swap between environments). Sort
# them under LC_ALL=C like the sha manifest below, so the golden compares
# byte-for-byte in every environment.
LC_ALL=C sort "$EXITS" > "$EXITS.sorted" && mv "$EXITS.sorted" "$EXITS" \
  || fail "sorting the exit-code list failed"

# --- manifests --------------------------------------------------------
cd "$SCRATCH" || fail "scratch dir vanished"
MANIFEST="$SCRATCH/manifest.sha256"
find . -type f ! -name manifest.sha256 ! -name exitcodes -print \
  | LC_ALL=C sort \
  | xargs -d '\n' sha256sum > "$MANIFEST" \
  || fail "hashing failed"

sha_rows=$(wc -l < "$MANIFEST")
exit_rows=$(wc -l < "$EXITS")
[ "$sha_rows" -ge "$MIN_SHA_ROWS" ] || fail "vacuity guard: only $sha_rows artifact rows (< $MIN_SHA_ROWS) — corpus or generation is broken"
[ "$exit_rows" -ge "$MIN_EXIT_ROWS" ] || fail "vacuity guard: only $exit_rows exit rows (< $MIN_EXIT_ROWS) — corpus or generation is broken"

if [ "$REBASELINE" = 1 ]; then
  cp "$MANIFEST" "$GOLDEN_SHA"
  cp "$EXITS" "$GOLDEN_EXIT"
  echo "nonlean-regress: REBASELINED: $sha_rows artifact rows, $exit_rows exit rows written to"
  echo "  $GOLDEN_SHA"
  echo "  $GOLDEN_EXIT"
  echo "Commit these ONLY with the reviewed change that justifies the new baseline."
  rm -rf "$SCRATCH"
  exit 0
fi

[ -s "$GOLDEN_SHA" ] || fail "golden manifest missing/empty: $GOLDEN_SHA (baseline with NONLEAN_REGRESS_REBASELINE=1)"
[ -s "$GOLDEN_EXIT" ] || fail "golden exitcodes missing/empty: $GOLDEN_EXIT (baseline with NONLEAN_REGRESS_REBASELINE=1)"

status=0
if ! diff -u "$GOLDEN_EXIT" "$EXITS" > "$SCRATCH/exit.diff" 2>&1; then
  echo "nonlean-regress: EXIT-CODE DRIFT (rows are '<target/file> <exit>'):" >&2
  cat "$SCRATCH/exit.diff" >&2
  status=1
fi
if ! diff -u "$GOLDEN_SHA" "$MANIFEST" > "$SCRATCH/sha.diff" 2>&1; then
  echo "nonlean-regress: OUTPUT DRIFT (rows are '<sha256>  ./<corpus>/<target>/<file>'):" >&2
  grep -E '^[+-][0-9a-f]' "$SCRATCH/sha.diff" >&2
  status=1
fi

if [ "$status" -ne 0 ]; then
  echo "nonlean-regress: FAIL — non-Lean emitter output changed; scratch kept at $SCRATCH" >&2
  exit 1
fi

echo "nonlean-regress: OK ($sha_rows artifact rows, $exit_rows exit rows, 9 emitters, byte-identical to golden)"
rm -rf "$SCRATCH"
exit 0
