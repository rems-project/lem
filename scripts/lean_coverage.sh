#!/bin/bash
# Generate code coverage report for the Lean backend using bisect_ppx.
# Requires: .coverage-switch/ local opam switch with OCaml 4.14.2 + bisect_ppx.
# Usage: bash scripts/lean_coverage.sh
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
SRC="$ROOT/src"
COV_DIR="$ROOT/coverage-report"
SWITCH="$ROOT/.coverage-switch"

if [ ! -d "$SWITCH" ]; then
    echo "Error: coverage switch not found at $SWITCH"
    echo "Create it with: opam switch create $SWITCH 4.14.2"
    exit 1
fi

# Activate coverage switch (overrides the project-local _opam switch)
export OPAMSWITCH="$SWITCH"
eval $(opam env --switch="$SWITCH" --set-switch)

# Verify bisect_ppx is available
if ! ocamlfind query bisect_ppx >/dev/null 2>&1; then
    echo "Error: bisect_ppx not found in coverage switch"
    echo "Install with: OPAMSWITCH=$SWITCH opam install -y bisect_ppx"
    exit 1
fi

# --- Instrument ---
echo "=== Instrumenting source files ==="
cp "$SRC/_tags" "$SRC/_tags.bak"

cat >> "$SRC/_tags" <<'TAGSEOF'

# Coverage instrumentation (temporary — added by lean_coverage.sh)
<lean_backend.ml> : package(bisect_ppx)
<backend_common.ml> : package(bisect_ppx)
<def_trans.ml> : package(bisect_ppx)
<process_file.ml> : package(bisect_ppx)
<patterns.ml> : package(bisect_ppx)
<rename_top_level.ml> : package(bisect_ppx)
<target_trans.ml> : package(bisect_ppx)
<output.ml> : package(bisect_ppx)
<main.native> : package(bisect_ppx)
TAGSEOF

# Clean and rebuild with instrumentation
echo "=== Building instrumented compiler ==="
make -C "$SRC" clean
make -C "$SRC"

# --- Run all Lean tests ---
# Remove any stale coverage data
rm -f "$ROOT"/bisect*.coverage

# Use the lem symlink (resolves share directory correctly)
LEM="$ROOT/lem"

echo ""
echo "=== Running backend tests ==="
cd "$ROOT/tests/backends"
for f in types.lem pats.lem pats3.lem classes2.lem classes3.lem exps.lem \
         coq_test.lem record_test.lem op.lem let_rec.lem indreln2.lem \
         coq_exps_test.lem; do
    printf "  %-30s" "$f"
    if BISECT_FILE="$ROOT/bisect" "$LEM" -wl ign -lean "$f" 2>/dev/null; then
        echo "ok"
    else
        echo "FAIL (non-fatal)"
    fi
done

echo ""
echo "=== Running comprehensive tests ==="
cd "$ROOT/tests/comprehensive"
for f in test_*.lem; do
    [ -f "$f" ] || continue
    printf "  %-50s" "$f"
    if BISECT_FILE="$ROOT/bisect" "$LEM" -wl ign \
        -i "$ROOT/library/pervasives.lem" -lean "$f" 2>/dev/null; then
        echo "ok"
    else
        echo "FAIL (non-fatal)"
    fi
done

echo ""
echo "=== Running library generation ==="
cd "$ROOT/library"
BISECT_FILE="$ROOT/bisect" make lean-libs 2>/dev/null || echo "  (some library files may have failed)"

echo ""
echo "=== Running cpp example ==="
cd "$ROOT/examples/cpp"
printf "  %-30s" "cmm.lem"
if BISECT_FILE="$ROOT/bisect" "$LEM" -wl ign -lean cmm.lem 2>/dev/null; then
    echo "ok"
else
    echo "FAIL (non-fatal)"
fi

echo ""
echo "=== Running ppcmem-model example ==="
cd "$ROOT/examples/ppcmem-model"
for f in *.lem; do
    printf "  %-50s" "$f"
    if BISECT_FILE="$ROOT/bisect" "$LEM" -wl ign -lean "$f" 2>/dev/null; then
        echo "ok"
    else
        echo "FAIL (non-fatal)"
    fi
done

# --- Generate report ---
echo ""
echo "=== Generating coverage report ==="
cd "$ROOT"
COVERAGE_FILES=$(ls bisect*.coverage 2>/dev/null | wc -l)
echo "  Found $COVERAGE_FILES coverage data files"

if [ "$COVERAGE_FILES" -eq 0 ]; then
    echo "Error: No coverage data collected!"
    mv "$SRC/_tags.bak" "$SRC/_tags"
    exit 1
fi

rm -rf "$COV_DIR"
bisect-ppx-report html --coverage-path "$ROOT" --source-path "$SRC" -o "$COV_DIR"
echo ""
bisect-ppx-report summary --coverage-path "$ROOT" --per-file

# --- Restore ---
echo ""
echo "=== Restoring uninstrumented build ==="
mv "$SRC/_tags.bak" "$SRC/_tags"
make -C "$SRC" clean >/dev/null 2>&1
make -C "$SRC" >/dev/null 2>&1

# Clean up coverage data files
rm -f "$ROOT"/bisect*.coverage

echo ""
echo "Coverage report: $COV_DIR/index.html"
echo "Open with: open $COV_DIR/index.html"
