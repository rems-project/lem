#!/usr/bin/env bash
# Upstream drift check: does this fork generate byte-identical NON-LEAN
# output to pristine upstream Lem? (nonlean-regress compares against the
# fork's own goldens; this compares against upstream itself.)
#
# Generates, with EACH lem (each with its own library via LEMLIB):
#   lib/<target>      Lem's library (each Lem's own library/, the LIBS of its
#                     library/Makefile), the 8 directory emitters + tex_all
#   backends/<t>/<f>  UPSTREAM's tests/backends/*.lem (the same inputs for
#                     both), 8 directory emitters + tex_all
#   linksem-ocaml     a linksem checkout's src/ -> OCaml, as its lem.mk does
#   cerberus-ocaml    a Cerberus checkout -> OCaml, as its Makefile does
# records stdout/stderr/exit code of every run, normalises absolute paths,
# and diffs the two trees file by file. For each differing OCaml/HOL/
# Isabelle/Coq library file it also reports whether only comments and
# whitespace differ. Exit 1 if anything differs, 2 on a usage error.
#
# Usage (from the repo root, after `make`):
#   UPSTREAM_LEM=/path/to/pristine/lem  LINKSEM=/path/to/linksem \
#   CERBERUS=/path/to/cerberus  tests/upstream-drift/run.sh OUTDIR
# UPSTREAM_LEM: an upstream Lem checkout (e.g. rems-project/lem at this
#   fork's merge-base), built (`make`). LINKSEM / CERBERUS: pristine client
#   checkouts; each is REQUIRED unless explicitly skipped with NO_LINKSEM=1 /
#   NO_CERBERUS=1 (a skipped client is named in the summary, never silent).
set -uo pipefail
FORK="$(cd "$(dirname "$0")/../.." && pwd)"
OUT="${1:?usage: UPSTREAM_LEM=... LINKSEM=... CERBERUS=... tests/upstream-drift/run.sh OUTDIR}"
UP="${UPSTREAM_LEM:?set UPSTREAM_LEM to a built upstream Lem checkout}"
UP="$(cd "$UP" && pwd)" || exit 2
die() { echo "upstream-drift: $*" >&2; exit 2; }
for l in "$UP/lem" "$FORK/lem"; do [ -x "$l" ] || die "$l not built (run make)"; done
CLIENTS=""
if [ "${NO_LINKSEM:-}" = 1 ]; then echo "upstream-drift: linksem NOT compared (NO_LINKSEM=1)"
else [ -d "${LINKSEM:-}/src" ] || die "set LINKSEM to a linksem checkout (or NO_LINKSEM=1)"; CLIENTS="$CLIENTS linksem"; fi
if [ "${NO_CERBERUS:-}" = 1 ]; then echo "upstream-drift: cerberus NOT compared (NO_CERBERUS=1)"
else [ -d "${CERBERUS:-}/frontend" ] || die "set CERBERUS to a Cerberus checkout (or NO_CERBERUS=1)"; CLIENTS="$CLIENTS cerberus"; fi
if [ -e "$OUT" ] && [ -n "$(ls -A "$OUT")" ]; then die "$OUT not empty"; fi
mkdir -p "$OUT"; OUT="$(cd "$OUT" && pwd)"

# a variable of a makefile, evaluated by make itself
mkvar() { # dir makefile var
  (cd "$1" && make -s -f "$2" -f <(printf 'upstream_drift_print:\n\t@echo $(%s)\n' "$3") upstream_drift_print 2>/dev/null)
}
TARGETS="ocaml hol isa coq html tex lem ident"
BACKENDS=$(cd "$UP/tests/backends" && ls *.lem)
[ -n "$BACKENDS" ] || die "no tests/backends/*.lem in $UP"
case "$CLIENTS" in *linksem*) LINKSEM_SRC=$(mkvar "$LINKSEM/src" lem.mk ALL_LEM_SRC); [ -n "$LINKSEM_SRC" ] || die "empty linksem source list";; esac
case "$CLIENTS" in *cerberus*) CERB_SRC=$(mkvar "$CERBERUS" Makefile LEM_SRC); [ -n "$CERB_SRC" ] || die "empty Cerberus source list";; esac

gen() { # side lemroot
  local side=$1; local root=$2; local L=$2/lem; local S="$OUT/$1"; local f t out libs
  export LEMLIB="$root/library"
  mkdir -p "$S"; : > "$S/exitcodes"
  rec() { printf '%s %s\n' "$1" "$2" >> "$S/exitcodes"; }
  libs=$(mkvar "$root/library" Makefile LIBS)
  [ -n "$libs" ] || die "empty LIBS in $root/library/Makefile"
  for t in $TARGETS; do
    out="$S/lib/$t"; mkdir -p "$out"
    local extra=""; [ "$t" = hol ] && extra="-hol_remove_matches"
    (cd "$root/library" && "$L" -"$t" $extra -outdir "$out" -wl ign -wl_auto_import err $libs -auxiliary_level none > "$out.stdout" 2> "$out.stderr"); rec "lib/$t" $?
  done
  mkdir -p "$S/lib/tex_all"
  (cd "$root/library" && "$L" -tex_all "$S/lib/tex_all/lem-libs.tex" -wl ign -wl_auto_import err $libs > "$S/lib/tex_all.stdout" 2> "$S/lib/tex_all.stderr"); rec "lib/tex_all" $?
  for f in $BACKENDS; do
    local base=${f%.lem}
    for t in $TARGETS; do
      out="$S/backends/$t/$base"; mkdir -p "$out"
      (cd "$UP/tests/backends" && "$L" -"$t" -outdir "$out" -wl ign "$f" > "$out.stdout" 2> "$out.stderr"); rec "backends/$t/$base" $?
    done
    out="$S/backends/tex_all/$base"; mkdir -p "$out"
    (cd "$UP/tests/backends" && "$L" -tex_all "$out/$base.tex" -wl ign "$f" > "$out.stdout" 2> "$out.stderr"); rec "backends/tex_all/$base" $?
  done
  case "$CLIENTS" in *linksem*)
    # a copy of src/ (lem.mk copies the native byte-sequence implementation first)
    local ls="$S/.linksem-src"; cp -r "$LINKSEM/src" "$ls"; cp "$ls/byte_sequence_ocaml.lem" "$ls/byte_sequence_impl.lem"
    out="$S/linksem-ocaml"; mkdir -p "$out"
    (cd "$ls" && "$L" -ocaml -outdir "$out" $LINKSEM_SRC byte_sequence_impl.lem > "$out.stdout" 2> "$out.stderr"); rec "linksem-ocaml" $?
    rm -rf "$ls";;
  esac
  case "$CLIENTS" in *cerberus*)
    # read-only: lem writes only to -outdir
    out="$S/cerberus-ocaml"; mkdir -p "$out"
    (cd "$CERBERUS" && "$L" -wl ign -wl_rename warn -wl_pat_red err -wl_pat_exh warn -outdir "$out" -cerberus_pp -ocaml $CERB_SRC > "$out.stdout" 2> "$out.stderr"); rec "cerberus-ocaml" $?;;
  esac
  find "$S" -type f -exec sed -i -e "s|$root|LEMROOT|g" -e "s|$S|OUTDIR|g" -e "s|$UP|UPSTREAMLEM|g" {} +
  LC_ALL=C sort -o "$S/exitcodes" "$S/exitcodes"
}
gen upstream "$UP"; gen fork "$FORK"

nfiles=$(find "$OUT/upstream" -type f | wc -l)
[ "$nfiles" -gt 400 ] || die "only $nfiles files generated (vacuous?)"
diff -rq "$OUT/upstream" "$OUT/fork" > "$OUT/differences.txt"; st=$?

# comments/whitespace-only classification of differing library code files
python3 - "$OUT" > "$OUT/classification.txt" <<'PY'
import re, sys, os
out = sys.argv[1]
def strip(s, isa):
    res = []; i = 0; n = len(s)
    while i < n:
        if isa and s.startswith('\\<comment>', i):
            i += len('\\<comment>')
            while i < n and s[i] in ' \t\n': i += 1
            d = 0
            while i < n:
                if s.startswith('\\<open>', i): d += 1; i += 7; continue
                if s.startswith('\\<close>', i):
                    d -= 1; i += 8
                    if d == 0: break
                    continue
                i += 1
            continue
        if s[i] == '"' and not isa:
            j = i + 1
            while j < n and s[j] != '"':
                j += 2 if s[j] == '\\' else 1
            res.append(s[i:j + 1]); i = j + 1; continue
        if s.startswith('(*', i):
            d = 0
            while i < n:
                if s.startswith('(*', i): d += 1; i += 2; continue
                if s.startswith('*)', i):
                    d -= 1; i += 2
                    if d == 0: break
                    continue
                i += 1
            continue
        res.append(s[i]); i += 1
    return re.sub(r'\s+', '', ''.join(res))
for line in open(os.path.join(out, 'differences.txt')):
    p = line.split()
    if p[0] != 'Files': continue
    rel = p[1].split('/upstream/', 1)[1]
    parts = rel.split('/')
    if parts[0] != 'lib' or parts[1] not in ('ocaml', 'hol', 'isa', 'coq'): continue
    a = open(p[1], errors='replace').read(); b = open(p[3], errors='replace').read()
    same = strip(a, parts[1] == 'isa') == strip(b, parts[1] == 'isa')
    print(('comments/whitespace only  ' if same else 'CODE DIFFERS              ') + rel)
PY
cst=$?
# fail-closed: a crashed classifier must not read as "no code differences"
[ "$cst" -eq 0 ] || die "the comments/whitespace classifier failed (exit $cst); classification.txt is not trustworthy"

echo "upstream-drift: upstream $(cd "$UP" && git describe --always --dirty 2>/dev/null), fork $(cd "$FORK" && git describe --always --dirty 2>/dev/null); clients compared:${CLIENTS:- none}"
echo "upstream-drift: $nfiles upstream files; $(wc -l < "$OUT/differences.txt") differ (list: $OUT/differences.txt)"
grep -o "$OUT/upstream/[^ ]*" "$OUT/differences.txt" | sed "s|$OUT/upstream/||" | cut -d/ -f1-2 | sort | uniq -c
if [ -s "$OUT/classification.txt" ]; then
  echo "library code files (OCaml/HOL/Isabelle/Coq):"; sort "$OUT/classification.txt" | sed 's/^/  /'
fi
exit $st
