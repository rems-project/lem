#!/usr/bin/env bash
# run.sh NAME [extra .ml files...]
# In directory NAME: lem -ocaml NAME.lem, compile NAME.ml plus the extra
# files against the upstream OCaml library, run the executable.
# Needs LEM (an upstream lem binary) and LEM_OCAMLLIB (an upstream ocaml-lib
# directory compiled in place, containing extract.cmxa); see README.md.
set -uo pipefail
: "${LEM:?set LEM to the upstream lem binary}"
: "${LEM_OCAMLLIB:?set LEM_OCAMLLIB to the compiled upstream ocaml-lib directory}"
n=$1; shift
cd "$(dirname "$0")/$n" || exit 9
echo "\$ lem -wl ign -ocaml $n.lem"
"$LEM" -wl ign -ocaml "$n.lem"; echo "[lem exit $?]"
echo "\$ ocamlfind ocamlopt -package zarith -linkpkg -I <upstream ocaml-lib> extract.cmxa $n.ml $* -o $n.exe"
ocamlfind ocamlopt -package zarith -linkpkg -I "$LEM_OCAMLLIB" -I "$LEM_OCAMLLIB/num_impl_zarith" \
  "$LEM_OCAMLLIB/extract.cmxa" "$n.ml" "$@" -o "$n.exe"; echo "[ocamlopt exit $?]"
if [ -x "$n.exe" ]; then echo "\$ ./$n.exe"; "./$n.exe"; echo "[run exit $?]"; fi
