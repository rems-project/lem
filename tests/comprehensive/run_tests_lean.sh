#!/bin/bash
# Comprehensive test runner for the lem Lean backend
# Generates Lean from .lem files and compiles with Lake
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
cd "$SCRIPT_DIR"

LEM="../../lem"
LEMLIB="../../library"
LEMFLAGS="-wl ign -i ${LEMLIB}/pervasives.lem"
LEAN_TEST="lean-test"

# Colors
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[0;33m'
NC='\033[0m'

pass=0
fail=0
xfail=0
total=0

is_expected_failure() {
    local file="$1"
    local backend="$2"
    grep -q "^${file},${backend}," expected_failures.txt 2>/dev/null
}

echo "=== Lem Comprehensive Test Suite ==="
echo ""

# Phase 1: Generation
echo "--- Phase 1: Generate Lean files ---"
for f in test_*.lem; do
    [ -f "$f" ] || continue
    total=$((total + 1))
    base=$(basename "$f" .lem)

    if is_expected_failure "$f" "lean"; then
        echo -e "  ${YELLOW}XFAIL${NC}: $f (expected failure)"
        xfail=$((xfail + 1))
        continue
    fi

    if $LEM $LEMFLAGS -lean "$f" > /dev/null 2>&1; then
        echo -e "  ${GREEN}OK${NC}: $f"
        pass=$((pass + 1))
    else
        echo -e "  ${RED}FAIL${NC}: $f"
        $LEM $LEMFLAGS -lean "$f" 2>&1 | head -5 | sed 's/^/    /'
        fail=$((fail + 1))
    fi
done

echo ""
echo "Generation: $pass passed, $fail failed, $xfail expected failures (of $total total)"

if [ $fail -gt 0 ]; then
    echo -e "${RED}Some tests failed during generation.${NC}"
fi

# Phase 2: Symlink and compile
echo ""
echo "--- Phase 2: Symlink generated files ---"
for f in Test_*.lean *_auxiliary.lean; do
    if [ -f "$f" ] && [ ! -L "${LEAN_TEST}/$f" ]; then
        ln -sf "../$f" "${LEAN_TEST}/$f"
        echo "  Linked: $f"
    fi
done

echo ""
echo "--- Phase 3: Compile with Lake ---"
cd "$LEAN_TEST"
if lake build 2>&1; then
    echo -e "${GREEN}Lake build succeeded.${NC}"
else
    echo -e "${RED}Lake build FAILED.${NC}"
    exit 1
fi

echo ""
echo "=== SUMMARY ==="
echo "  Passed:           $pass"
echo "  Failed:           $fail"
echo "  Expected failures: $xfail"
echo "  Total:            $total"

[ $fail -eq 0 ] && echo -e "${GREEN}ALL TESTS PASSED${NC}" || exit 1
