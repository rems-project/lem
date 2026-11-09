#!/usr/bin/env bash
# A registered expected difference cannot excuse a broken compiler/build.
set -euo pipefail
here=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
scratch=$(mktemp -d "${TMPDIR:-/tmp}/parity-admission.XXXXXX")
trap 'rm -rf "$scratch"' EXIT
printf '#!/bin/sh\necho "planted OCaml compiler failure" >&2\nexit 2\n' > "$scratch/ocamlfind"
chmod +x "$scratch/ocamlfind"
if PATH="$scratch:$PATH" "$here/run.sh" f_int32_overflow > "$scratch/log" 2>&1; then
    cat "$scratch/log"
    echo 'test_failure_admission: FAIL — broken build admitted as expected difference' >&2
    exit 1
fi
grep -q 'planted OCaml compiler failure' "$scratch/log"
grep -q 'not XFAIL' "$scratch/log"
if grep -q 'XFAIL (expected' "$scratch/log"; then
    cat "$scratch/log"
    exit 1
fi
echo 'test_failure_admission: OK (registered probe with compiler failure is red, not XFAIL)'
