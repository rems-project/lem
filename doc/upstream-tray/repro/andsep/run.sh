#!/usr/bin/env bash
# Draft 23: comments before `and` in a `let rec ... and ...` group, and
# clause order, on the four backends. Needs LEM (upstream lem binary).
# Writes only under ./out*.
set -uo pipefail
: "${LEM:?set LEM to the upstream lem binary}"
cd "$(dirname "$0")" || exit 9
gen () { echo "\$ lem -wl ign $*"; "$LEM" -wl ign "$@"; echo "[exit $?]"; }
for f in test_and test_nomatch test_order test_sorted; do
  mkdir -p out_$f
  for t in ocaml coq hol isa; do gen -$t -outdir out_$f $f.lem; done
  mkdir -p out_$f/holrm
  gen -hol -hol_remove_matches -outdir out_$f/holrm $f.lem
done
for f in test_and test_nomatch test_order test_sorted; do
  echo "=== $f: OCaml"; grep -n 'before\|^let rec\|^and ' out_$f/$f.ml
  echo "=== $f: Coq";   grep -n 'before\|Fixpoint\|^with ' out_$f/$f.v
  echo "=== $f: HOL4";  sed -n '/^(\* before/,/_defn;$/p' out_$f/${f}Script.sml
  echo "=== $f: HOL4 -hol_remove_matches"; sed -n '/^(\* before/,/_defn;$/p' out_$f/holrm/${f}Script.sml
  T=$(echo "${f:0:1}" | tr a-z A-Z)${f:1}
  echo "=== $f: Isabelle"; sed -n '/before/,/^by pat_completeness/p' out_$f/$T.thy
done
