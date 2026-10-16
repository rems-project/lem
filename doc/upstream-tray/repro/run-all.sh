#!/usr/bin/env bash
# run-all.sh WORKDIR
# Copies this directory to WORKDIR (which must not exist) and runs every
# reproducer there, writing WORKDIR/<case>/transcript.txt. Needs:
#   LEM       an upstream lem binary (the drafts used 3802cb0)
#   LEMSRC    the upstream checkout it was built from (for library/)
#   LEM_OCAMLLIB  that checkout's ocaml-lib, compiled (extract.cmxa); README.md
# and ocamlfind with zarith on PATH. Nothing outside WORKDIR is written.
set -uo pipefail
: "${LEM:?}"; : "${LEMSRC:?}"; : "${LEM_OCAMLLIB:?}"
W=${1:?usage: run-all.sh WORKDIR}
[ -e "$W" ] && { echo "run-all.sh: $W exists" >&2; exit 2; }
cp -r "$(dirname "$0")" "$W"
cd "$W" || exit 9
echo "lem -v: $("$LEM" -v)"; ocamlfind ocamlopt -version; ocamlfind list 2>&1 | grep '^zarith '

# OCaml-side reproducers (drafts 04-14, 16, 18-22)
for c in x1 failarg nat63 the divmod bitwise mword libdefs genlist; do
  if [ -f "$c/main.ml" ]; then ./run.sh "$c" main.ml; else ./run.sh "$c"; fi > "$c/transcript.txt" 2>&1
done

# draft 14, comparison: a val with no definition
( cd the && echo '$ lem -ocaml norep.lem' && "$LEM" -ocaml norep.lem; echo "[exit $?]" ) > the/transcript-norep.txt 2>&1

# draft 17: replicate under a bounded stack, control, default limit
( ./run.sh replicate main.ml
  cd replicate
  for n in 1000000 10000000; do
    echo "\$ OCAMLRUNPARAM=l=1M ./replicate.exe $n"; OCAMLRUNPARAM=l=1M ./replicate.exe $n; echo "[exit $?]"; done
  echo '$ OCAMLRUNPARAM=b,l=1M ./replicate.exe 1000000 | head -8'
  OCAMLRUNPARAM=b,l=1M ./replicate.exe 1000000 2>&1 | head -8
  ocamlfind ocamlopt -package zarith control.ml -o control.exe
  echo '$ OCAMLRUNPARAM=l=1M ./control.exe 1000000'; OCAMLRUNPARAM=l=1M ./control.exe 1000000; echo "[exit $?]"
  echo "\$ /usr/bin/time -f '%e s %M kB' ./replicate.exe 10000000"
  /usr/bin/time -f '%e s %M kB' ./replicate.exe 10000000; echo "[exit $?]"
) > replicate/transcript.txt 2>&1

# draft 03: reserved-name list missing (default warnings)
( cd b10
  rsync -a --exclude 'ocaml-build-dir*' --exclude ocaml_constants "$LEMSRC/library/" lib-no-constants/
  mkdir -p with without
  echo '$ lem -ocaml -outdir with kw.lem'; "$LEM" -ocaml -outdir with kw.lem; echo "[exit $?]"; cat with/kw.ml
  echo '$ LEMLIB=lib-no-constants lem -ocaml -outdir without kw.lem'
  LEMLIB=$PWD/lib-no-constants "$LEM" -ocaml -outdir without kw.lem; echo "[exit $?]"; cat without/kw.ml
  echo '$ ocamlfind ocamlopt -c with/kw.ml'; (cd with && ocamlfind ocamlopt -I "$LEM_OCAMLLIB" -c kw.ml; echo "[exit $?]")
  echo '$ ocamlfind ocamlopt -c without/kw.ml'; (cd without && ocamlfind ocamlopt -I "$LEM_OCAMLLIB" -c kw.ml; echo "[exit $?]")
) > b10/transcript.txt 2>&1

# drafts 01 and 02: non-ASCII text, four backends
for c in sect blk; do
  ( cd $c; mkdir -p out
    for t in ocaml hol isa coq; do echo "\$ lem -wl ign -$t -outdir out $c.lem"; "$LEM" -wl ign -$t -outdir out $c.lem; echo "[exit $?]"; done
    echo "\$ grep -n '§\|Â\|zero\|succ' out/*"; grep -n '§\|Â\|zero\|succ' out/*
  ) > $c/transcript.txt 2>&1
done
( cd sect && echo '$ sed -n 2p out/sect.ml | xxd' && sed -n 2p out/sect.ml | xxd ) >> sect/transcript.txt 2>&1
( cd blk && echo '$ sed -n 5p out/blk.ml | xxd' && sed -n 5p out/blk.ml | xxd
  cp out/blk.ml blk.ml
  echo '$ ocamlfind ocamlopt ... blk.ml main.ml -o blk.exe && ./blk.exe'
  ocamlfind ocamlopt -package zarith -linkpkg -I "$LEM_OCAMLLIB" -I "$LEM_OCAMLLIB/num_impl_zarith" "$LEM_OCAMLLIB/extract.cmxa" blk.ml main.ml -o blk.exe && ./blk.exe
  echo "[exit $?]" ) >> blk/transcript.txt 2>&1

# draft 15: transform.lem
( echo '$ (cd $LEMSRC/library && lem -lem -outdir <scratch> transform.lem)'
  mkdir -p transform/out
  (cd "$LEMSRC/library" && "$LEM" -lem -outdir "$W/transform/out" transform.lem); echo "[exit $?]"
  echo '$ lem -lem -outdir out user.lem'
  (cd transform && "$LEM" -lem -outdir out user.lem); echo "[exit $?]"
) > transform/transcript.txt 2>&1
# draft 23: comments before `and`, clause order (generation only)
./andsep/run.sh > andsep/transcript.txt 2>&1
echo "run-all.sh: done"
