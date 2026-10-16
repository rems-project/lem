#!/usr/bin/env bash
# Lean keyword coverage check (linksem 2026-09-28, B5).
#
# Derives, from the Lean toolchain pinned in lean-lib/lean-toolchain, every
# identifier-shaped token of the core (Init) grammar that CANNOT be used as a
# plain binder name (`let t := x; t` and `fun (t : Nat) => t`), and checks
# that each one is in BOTH of the backend's avoid lists:
#   - src/lean_backend.ml `lean_syntax_keywords` (local names, escaped «t»)
#   - library/lean_constants (top-level names, renamed by the rename pass).
# Exit 1 naming the missing tokens; exit 0 when both lists cover the set.
# Re-run whenever the Lean toolchain moves (new keywords appear).
# Every lean invocation runs under the repository's cgroup memory cap: the
# script re-executes itself once through scripts/capped, so the whole batch
# (including the parallel per-token checks) is ONE capped job
# (CERB_MEM_MAX, default 32G here). A missing wrapper is a hard error.
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
if [ "${LEM_KEYWORD_PROBE_CAPPED:-}" != 1 ]; then
  [ -x "$ROOT/scripts/capped" ] || { echo "lean_keyword_probe: $ROOT/scripts/capped missing or not executable" >&2; exit 2; }
  export CERB_MEM_MAX="${CERB_MEM_MAX:-32G}" LEM_KEYWORD_PROBE_CAPPED=1
  exec "$ROOT/scripts/capped" "$0" "$@"
fi
# The marker only says "re-executed"; it is not trusted. Verify that a
# memory cap is actually in force on this process's cgroup (a numeric
# memory.max), so setting LEM_KEYWORD_PROBE_CAPPED=1 by hand cannot skip the
# cap. CERB_MEM_MAX=none is capped's own explicit, loudly reported opt-out.
if [ "${CERB_MEM_MAX:-}" = none ]; then
  # capped reports its own opt-out loudly; a hand-set marker bypasses
  # capped, so the opt-out is reported here too (never silent).
  echo "lean_keyword_probe: CERB_MEM_MAX=none — running UNCAPPED (explicit opt-out)" >&2
else
  cg="/sys/fs/cgroup$(cut -d: -f3 /proc/self/cgroup)"
  mm="$(cat "$cg/memory.max" 2>/dev/null || true)"
  case "$mm" in
    ''|*[!0-9]*) echo "lean_keyword_probe: refused — no memory cap in force (cgroup $cg memory.max='$mm'); run the script directly (it re-executes itself under scripts/capped), or set CERB_MEM_MAX=none to opt out explicitly" >&2; exit 2;;
  esac
fi
TC="$(cat "$ROOT/lean-lib/lean-toolchain")"
LEAN="$HOME/.elan/toolchains/$(echo "$TC" | sed 's|/|--|; s|:|---|')/bin/lean"
[ -x "$LEAN" ] || { echo "lean_keyword_probe: no lean binary for $TC at $LEAN" >&2; exit 2; }
W="$(mktemp -d)"; trap 'rm -rf "$W"' EXIT
cat > "$W/Tok.lean" <<'LEAN'
import Lean
open Lean Elab Command
#eval show CommandElabM Unit from do
  let tt := (Lean.Parser.parserExtension.getState (← getEnv)).tokens
  for s in tt.values do
    if s.length > 0 && s.front.isAlpha && s.all (fun c => c.isAlphanum || c == '_') then
      IO.println s
LEAN
"$LEAN" "$W/Tok.lean" | grep -E '^[A-Za-z][A-Za-z0-9_]*$' | sort -u > "$W/toks"
[ -s "$W/toks" ] || { echo "lean_keyword_probe: empty token table (vacuous probe)" >&2; exit 2; }
mkdir "$W/p"
while read -r t; do
  printf 'def probe (x : Nat) : Nat :=\n  let %s := x\n  %s + (fun (%s : Nat) => %s) 1\n' "$t" "$t" "$t" "$t" > "$W/p/$t.lean"
done < "$W/toks"
# No imports: exactly the core grammar every generated file sees.
ls "$W"/p/*.lean | xargs -P8 -I{} sh -c '"$0" "$1" >/dev/null 2>&1 || basename "$1" .lean' "$LEAN" {} | sort > "$W/kw"
n=$(wc -l < "$W/kw")
[ "$n" -ge 50 ] || { echo "lean_keyword_probe: only $n keywords found (vacuous probe?)" >&2; exit 2; }
python3 - "$ROOT" "$W/kw" <<'PY'
import re, sys
root, kwf = sys.argv[1], sys.argv[2]
kw = [l.strip() for l in open(kwf) if l.strip()]
src = open(f"{root}/src/lean_backend.ml").read()
m = re.search(r'let lean_syntax_keywords = \[(.*?)\n\]', src, re.S)
if not m: sys.exit("lean_keyword_probe: lean_syntax_keywords not found")
syn = set(re.findall(r'"([^"]+)"', m.group(1)))
consts = set(l.strip() for l in open(f"{root}/library/lean_constants"))
bad = 0
for name, have in (("src/lean_backend.ml lean_syntax_keywords", syn), ("library/lean_constants", consts)):
    miss = [k for k in kw if k not in have]
    if miss:
        bad = 1
        print(f"MISSING from {name} ({len(miss)}): {' '.join(miss)}")
print(f"lean_keyword_probe: {len(kw)} core keywords checked")
sys.exit(bad)
PY
