#!/bin/sh
# Two-target parity runner (suite phase `lean-parity`; parity-fix slice
# 2026-09-03, landing the noodler's tests/noodle/run_parity.sh as the
# suite's real runner). The OCaml target is the REFERENCE semantics of a
# lem program; the Lean target must compute the same thing.
#
# For each probe probes/<name>.lem (exporting `results : list string`,
# printed one per line by the default drivers):
#   1. OCaml leg: generate with -ocaml, build a native binary against
#      ocaml-lib/_build_zarith (the same library the lem OCaml backend
#      links), run it. Its stdout is the reference output. It is compared
#      byte-for-byte with the committed pin expected/<name>.out — drift
#      FAILS (the pin is the record; rebaseline explicitly with
#      REBASELINE=1 and commit the diff).
#   2. Lean leg: generate with -lean into lean-test/, build the exe with
#      lake (through the cgroup cap), run it, diff against the reference
#      output byte-for-byte. Any difference FAILS.
# FAILURE probes (probes/f_*.lem): the lem program must FAIL on both
# targets (OCaml: uncaught exception, non-zero exit; Lean: run under
# LEAN_ABORT_ON_PANIC=1, non-zero exit) after printing the same stdout
# prefix — the [USER 2026-09-03] exception class (a): failure-vs-success
# must agree per program, the failure TEXT may differ (runtime-specific
# exception names / positions), so only stdout is compared and both
# exits must be non-zero. The pin records the OCaml stdout prefix. A
# failure probe exports `steps : list (nat -> string)` instead of
# `results`: the default drivers print each step as it is computed (the
# lines before the failing step must appear on both targets), passing a
# RUNTIME nat (the argument count, 0) so neither compiler can fold the
# failing operation into module initialisation.
# Optional per-probe files: <name>.ext.ml (extra OCaml module linked into
# the OCaml binary, e.g. an impure counter standing for a `supply`),
# <name>.main.ml / <name>.main.lean (custom drivers replacing the
# default `print each line of results`), <name>.proofs.lean (the
# hand-written fuel_measure obligation proofs, installed as
# <Mod>_lemMeasureProofs.lean and rooted — fuel-measure slice).
#
# Vacuity guards: a probe without a pin fails; an empty reference output
# fails; a Lean exe that did not get built fails. lean-test/lakefile.lean
# is REGENERATED from the probe list on every run (a probe can never be
# silently absent from the roots — the L0 record's lakefile gotcha).
#
# EXPECTED FAILURES: expected_failures.txt lists probes
# ("<name>,<class>,<reason>", class one of fix / ruled / open — see the
# file's header) whose divergence is KNOWN: such a probe must still FAIL
# its parity check — a listed probe that PASSES is reported as a failure
# of the suite ("the expected failure now passes: remove it from the
# list"), so the list cannot go stale and a fix cannot land silently. The
# file is validated before any probe runs: a malformed line, an unknown
# class, a duplicate, or an entry naming a probe that does not exist is a
# hard error. A listed probe counts as XFAIL only if (1) it reaches a real
# parity disagreement: different output with Lean exiting 0, or
# (non-failure probe) a Lean panic abort (exit 134 after a "PANIC at"
# line) where the OCaml reference succeeded — a broken build or any other
# crash is red (test_failure_admission.sh); AND (2) the Lean side of the
# disagreement is EXACTLY the pinned expected/<name>.lean.out: the Lean exit
# status, the Lean stdout (for non-failure probes stdout+stderr, as run)
# and, for failure probes, the Lean stderr. Nothing is deleted from the
# captured output: noise is suppressed at the SOURCE (the Lean exe runs
# with LEAN_BACKTRACE=0, so the runtime prints no backtrace, and under
# `( ulimit -c 0; exec "$exe" )`, so the shell's "Aborted (core dumped)"
# goes to the runner's own stderr, not the capture). The only
# normalisation is masking the source position in a PANIC line
# (`:<pos>:`), so a LemLib edit that moves line numbers does not churn pins. Together
# with the OCaml pin this fixes the whole disagreement: a NEW or CHANGED
# difference in a registered probe is red, not absorbed. Every registered
# probe must have a Lean pin and every Lean pin must be registered.
# Rebaseline the Lean pins of registered probes explicitly with
# REBASELINE_XFAIL=1 and commit the diff. A run with REBASELINE=1 or
# REBASELINE_XFAIL=1 writes pins, so it is never a gate: it always EXITS
# NON-ZERO with a summary of the pins it rewrote.
# Usage: ./run.sh [<name>...]   (default: every probes/*.lem), from any cwd,
#        with the complete opam environment (opam exec --). Env: CAPPED, CERB_MEM_MAX.
set -u
HERE=$(cd "$(dirname "$0")" && pwd)
ROOT=$(cd "$HERE/../../.." && pwd)
LEM="$ROOT/lem"
LEMFLAGS="-wl ign -i $ROOT/library/pervasives_extra.lem"
LEM_OCAML_RUNTIME="$ROOT/ocaml-lib/_build_zarith"
CAPPED=${CAPPED:-$ROOT/scripts/capped}
if [ ! -x "$CAPPED" ]; then
  echo "FAIL: capped Lean runner not executable: $CAPPED (set CAPPED to an executable wrapper)" >&2
  exit 1
fi
export CERB_MEM_MAX=${CERB_MEM_MAX:-16G}
OUT="$HERE/_out"
LT="$HERE/lean-test"
mkdir -p "$OUT/ocaml" "$OUT/lean" "$LT"

# --- the expected-failure registry: validated up front, fail-closed ---
XF="$HERE/expected_failures.txt"
if [ ! -f "$XF" ]; then echo "FAIL: registry $XF missing"; exit 1; fi
xf_bad=$(awk -F, -v probes="$HERE/probes" -v expdir="$HERE/expected" '
  /^[[:space:]]*(#|$)/ { next }
  { r = $0; sub(/^[^,]*,[^,]*,?/, "", r)
    if (NF < 3 || r ~ /^[[:space:]]*$/) { printf "line %d: want <probe>,<class>,<non-blank reason>: %s\n", NR, $0; next }
    if ($2 != "fix" && $2 != "ruled" && $2 != "open") { printf "line %d: unknown class \"%s\" (fix|ruled|open)\n", NR, $2 }
    if (seen[$1]++) { printf "line %d: duplicate entry for %s\n", NR, $1 }
    if (system("test -f \"" probes "/" $1 ".lem\"") != 0) { printf "line %d: orphan entry, no probe %s/%s.lem\n", NR, probes, $1 }
    if (system("test -f \"" expdir "/" $1 ".lean.out\"") != 0 && ENVIRON["REBASELINE_XFAIL"] != "1") { printf "line %d: registered probe %s has no Lean pin %s/%s.lean.out\n", NR, $1, expdir, $1 } }' "$XF") \
  || { echo "FAIL: the registry validator itself failed (awk exit $?) — refusing to run"; exit 1; }
for pin in "$HERE"/expected/*.lean.out; do
  [ -e "$pin" ] || continue
  pn=$(basename "$pin" .lean.out)
  grep -q "^$pn," "$XF" || xf_bad="$xf_bad
orphan Lean pin $pin: $pn is not registered"
done
if [ -n "$xf_bad" ]; then echo "FAIL: invalid expected-failure registry $XF:"; echo "$xf_bad" | sed '/^$/d; s/^/  /'; exit 1; fi

if [ $# -eq 0 ]; then
  set -- $(cd "$HERE/probes" && ls *.lem | sed 's/\.lem$//')
fi
if [ $# -eq 0 ]; then echo "  FAIL (vacuous): no probes in $HERE/probes"; exit 1; fi

# --- regenerate the Lean test package from the FULL probe list ---
{
  printf 'import Lake\nopen Lake DSL\n\n'
  printf -- '-- GENERATED by tests/comprehensive/parity/run.sh from probes/*.lem\n'
  printf -- '-- (one lean_lib root triple + one lean_exe per probe). Do not edit.\n'
  printf 'package LemParity where\n  version := v!"0.1.0"\n  moreLeanArgs := #["-DautoImplicit=false"]\n\n'
  printf 'require LemLib from "../../../../lean-lib"\n\n'
  printf '@[default_target]\nlean_lib LemParity where\n  srcDir := "."\n  roots := #[\n'
  first=1
  for f in "$HERE"/probes/*.lem; do
    n=$(basename "$f" .lem); M=$(echo "$n" | sed 's/^\(.\)/\U\1/')
    [ $first = 1 ] || printf ',\n'; first=0
    printf '    `%s, `%s_auxiliary, `Run_%s' "$M" "$M" "$n"
    # fuel-measure slice: a probe with measured functions ships its
    # obligation proofs as probes/<name>.proofs.lean, installed as the
    # module its auxiliary file imports (a root, so the build gates it)
    if [ -f "$HERE/probes/$n.proofs.lean" ]; then
      cp "$HERE/probes/$n.proofs.lean" "$LT/${M}_lemMeasureProofs.lean"
      printf ', `%s_lemMeasureProofs' "$M"
    fi
  done
  printf '\n  ]\n'
  for f in "$HERE"/probes/*.lem; do
    n=$(basename "$f" .lem)
    printf '\nlean_exe «run-%s» where root := `Run_%s\n' "$n" "$n"
  done
} > "$LT/lakefile.lean"
cp "$HERE/../lean-test/lean-toolchain" "$LT/lean-toolchain"

status=0
n_ok=0; n_xfail=0; n_fail=0; n_rebased=0; n_rebased_changed=0
# write a pin (rebaseline runs only); count it, and whether it changed
write_pin() { if ! cmp -s "$1" "$2"; then n_rebased_changed=$((n_rebased_changed+1)); fi; cp "$1" "$2"; n_rebased=$((n_rebased+1)); }
# The Lean side of a run, normalised for pinning: exit status, stdout, and
# (failure probes) stderr; backtrace lines dropped, PANIC positions masked.
lean_norm() { sed -E 's/^(PANIC at [^ ]+ [^ :]+):[0-9]+:[0-9]+:/\1:<pos>:/' "$1"; }
lean_record() {
  { echo "lean-exit: $ln_st"; echo "--- lean stdout ---"; lean_norm "$OUT/lean/$name.out"
    if [ -f "$OUT/lean/$name.err" ]; then echo "--- lean stderr ---"; lean_norm "$OUT/lean/$name.err"; fi
  } > "$OUT/lean/$name.xfail"
}
run_one() {
  parity_mismatch=0
  name=$1
  src="$HERE/probes/$name.lem"
  pin="$HERE/expected/$name.out"
  Mod=$(echo "$name" | sed 's/^\(.\)/\U\1/')
  if [ ! -f "$src" ]; then echo "  FAIL: no such probe $src"; return 1; fi
  # --- OCaml leg (the reference) ---
  rm -rf "$OUT/ocaml/$name"; mkdir -p "$OUT/ocaml/$name"
  if ! ( cd "$OUT/ocaml/$name" && cp "$src" . && $LEM $LEMFLAGS -ocaml "$name.lem" ) > "$OUT/ocaml/$name/gen.log" 2>&1; then
    echo "  FAIL: OCaml generation failed:"; sed -n 1,10p "$OUT/ocaml/$name/gen.log"; return 1; fi
  case "$name" in f_*) failure_probe=1;; *) failure_probe=0;; esac
  if [ -f "$HERE/probes/$name.main.ml" ]; then cp "$HERE/probes/$name.main.ml" "$OUT/ocaml/$name/main.ml"
  elif [ $failure_probe = 1 ]; then echo "let () = let n = Array.length Sys.argv - 1 in List.iter (fun f -> print_endline (f n); flush stdout) $Mod.steps" > "$OUT/ocaml/$name/main.ml"
  else echo "let () = List.iter print_endline $Mod.results" > "$OUT/ocaml/$name/main.ml"; fi
  ext=""
  if [ -f "$HERE/probes/$name.ext.ml" ]; then cp "$HERE/probes/$name.ext.ml" "$OUT/ocaml/$name/parity_ext.ml"; ext="parity_ext.ml"; fi
  if ! ( cd "$OUT/ocaml/$name" && ocamlfind ocamlopt -package zarith -linkpkg -I "$LEM_OCAML_RUNTIME" "$LEM_OCAML_RUNTIME/extract.cmxa" $ext "$name.ml" main.ml -o run.native ) > "$OUT/ocaml/$name/build.log" 2>&1; then
    echo "  FAIL: OCaml build failed:"; sed -n 1,20p "$OUT/ocaml/$name/build.log"; return 1; fi
  ( cd "$OUT/ocaml/$name" && ./run.native ) > "$OUT/ocaml/$name.out" 2> "$OUT/ocaml/$name.err"; oc_st=$?
  if [ $failure_probe = 1 ]; then
    if [ $oc_st -eq 0 ]; then echo "  FAIL (vacuous): failure probe, but the OCaml reference SUCCEEDED (exit 0)"; return 1; fi
    echo "  ocaml: failed as expected (exit $oc_st): $(head -c 160 "$OUT/ocaml/$name.err" | tr '\n' ' ')"
  else
    if [ $oc_st -ne 0 ]; then echo "  FAIL: OCaml reference binary exited $oc_st:"; tail -5 "$OUT/ocaml/$name.err"; return 1; fi
    if [ -s "$OUT/ocaml/$name.err" ]; then echo "  FAIL: OCaml reference wrote to stderr:"; head -5 "$OUT/ocaml/$name.err"; return 1; fi
  fi
  if [ ! -s "$OUT/ocaml/$name.out" ]; then echo "  FAIL (vacuous): OCaml reference printed nothing"; return 1; fi
  if [ "${REBASELINE:-0}" = 1 ]; then write_pin "$OUT/ocaml/$name.out" "$pin"; echo "  REBASELINED pin $pin"; fi
  if [ ! -f "$pin" ]; then echo "  FAIL: no pin $pin (record the OCaml reference with REBASELINE=1 and commit it)"; return 1; fi
  if ! cmp -s "$pin" "$OUT/ocaml/$name.out"; then
    echo "  FAIL: OCaml reference DRIFTED from the committed pin (re-adjudicate, then REBASELINE=1):"
    diff "$pin" "$OUT/ocaml/$name.out" | head -20; return 1; fi
  # --- Lean leg ---
  rm -f "$OUT/lean/$name.out" "$OUT/lean/$name.err" "$OUT/lean/$name.xfail"
  rm -f "$LT/$Mod.lean" "$LT/${Mod}_auxiliary.lean" "$LT/Run_$name.lean"
  if ! ( cd "$LT" && $LEM $LEMFLAGS -outdir "$LT" -lean "$src" ) > "$OUT/lean/$name.gen.log" 2>&1; then
    echo "  FAIL: Lean generation failed:"; sed -n 1,10p "$OUT/lean/$name.gen.log"; return 1; fi
  if [ -f "$HERE/probes/$name.main.lean" ]; then cp "$HERE/probes/$name.main.lean" "$LT/Run_$name.lean"
  elif [ $failure_probe = 1 ]; then printf 'import %s\ndef main (args : List String) : IO Unit := steps.forM fun f => do\n  IO.println (f args.length)\n  (← IO.getStdout).flush\n' "$Mod" > "$LT/Run_$name.lean"
  else printf 'import %s\ndef main : IO Unit := results.forM IO.println\n' "$Mod" > "$LT/Run_$name.lean"; fi
  if ! ( cd "$LT" && $CAPPED lake build "run-$name" ) > "$OUT/lean/$name.build.log" 2>&1; then
    echo "  FAIL: Lean build failed:"; grep -n -A6 'error' "$OUT/lean/$name.build.log" | head -40; return 1; fi
  exe="$LT/.lake/build/bin/run-$name"
  if [ ! -x "$exe" ]; then echo "  FAIL (vacuous): Lean exe $exe was not built"; return 1; fi
  if [ $failure_probe = 1 ]; then
    ( ulimit -c 0; LEAN_ABORT_ON_PANIC=1 LEAN_BACKTRACE=0 exec "$exe" ) > "$OUT/lean/$name.out" 2> "$OUT/lean/$name.err"; ln_st=$?; lean_record
    if [ $ln_st -eq 0 ]; then parity_mismatch=1; echo "  FAIL: failure probe, but the Lean binary SUCCEEDED (exit 0) where the OCaml reference fails"; return 1; fi
    if diff "$OUT/ocaml/$name.out" "$OUT/lean/$name.out" > "$OUT/$name.diff"; then
      echo "  OK: both fail (lean exit $ln_st: $(head -c 120 "$OUT/lean/$name.err" | tr '\n' ' ')); stdout prefix identical ($(wc -l < "$OUT/lean/$name.out") lines)"; return 0
    else
      parity_mismatch=1; echo "  FAIL: both fail but the stdout prefixes differ (< OCaml, > Lean):"; head -20 "$OUT/$name.diff"; return 1
    fi
  else
    ( ulimit -c 0; LEAN_ABORT_ON_PANIC=1 LEAN_BACKTRACE=0 exec "$exe" ) > "$OUT/lean/$name.out" 2>&1; ln_st=$?; lean_record
    if diff "$OUT/ocaml/$name.out" "$OUT/lean/$name.out" > "$OUT/$name.diff"; then
      if [ $ln_st -ne 0 ]; then echo "  FAIL: Lean binary exited $ln_st (output identical)"; return 1
      else echo "  OK: parity ($(wc -l < "$OUT/lean/$name.out") lines byte-identical to the OCaml reference; pin matches)"; return 0; fi
    else
      [ "$ln_st" -eq 0 ] && parity_mismatch=1
      # Failure-vs-success (the OCaml reference succeeded, checked above):
      # a Lean panic under LEAN_ABORT_ON_PANIC=1 (the runtime's "PANIC at"
      # line, then abort: exit 134) is a real parity disagreement too. Any
      # other non-zero exit (a kill, a crash without a panic) is not.
      if [ "$ln_st" -eq 134 ] && grep -q '^PANIC at ' "$OUT/lean/$name.out"; then parity_mismatch=1; fi
      echo "  FAIL: PARITY DIFF (< OCaml reference, > Lean; lean exit $ln_st):"; head -40 "$OUT/$name.diff"; return 1
    fi
  fi
  return 1
}
for name in "$@"; do
  echo "=== $name ==="
  xreason=$(grep "^$name," "$XF" | head -1 | cut -d, -f2-)
  lpin="$HERE/expected/$name.lean.out"
  if run_one "$name"; then
    if [ -n "$xreason" ]; then echo "  FAIL: EXPECTED FAILURE NOW PASSES ($xreason) — remove it from expected_failures.txt (and its Lean pin)"; status=1; n_fail=$((n_fail+1))
    else n_ok=$((n_ok+1)); fi
  else
    if [ -n "$xreason" ] && [ "$parity_mismatch" -eq 1 ]; then
      if [ "${REBASELINE_XFAIL:-0}" = 1 ]; then write_pin "$OUT/lean/$name.xfail" "$lpin"; echo "  REBASELINED Lean pin $lpin"; fi
      if [ ! -f "$lpin" ]; then
        echo "  FAIL: registered probe has no Lean pin $lpin (not XFAIL)"; status=1; n_fail=$((n_fail+1))
      elif cmp -s "$lpin" "$OUT/lean/$name.xfail"; then
        echo "  XFAIL (expected, registered; Lean side matches its pin): $xreason"; n_xfail=$((n_xfail+1))
      else
        echo "  FAIL: registered probe's disagreement CHANGED — the Lean side differs from its pin (< pin, > this run; not XFAIL):"
        diff "$lpin" "$OUT/lean/$name.xfail" | head -20; status=1; n_fail=$((n_fail+1))
      fi
    else
      [ -z "$xreason" ] || echo "  FAIL: registered probe did not reach its expected parity disagreement (not XFAIL)"
      status=1; n_fail=$((n_fail+1))
    fi
  fi
done
echo "parity: $# probes: $n_ok OK, $n_xfail XFAIL (registered, Lean side pinned), $n_fail FAIL"
if [ "${REBASELINE:-0}" = 1 ] || [ "${REBASELINE_XFAIL:-0}" = 1 ]; then
  echo "parity: REBASELINE run — $n_rebased pin(s) REWRITTEN ($n_rebased_changed changed); not a gate: review and commit the diff, then run again without REBASELINE/REBASELINE_XFAIL"
  exit 1
fi
exit $status
