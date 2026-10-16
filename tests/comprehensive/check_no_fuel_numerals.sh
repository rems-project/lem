#!/bin/sh
# Gate: no fuel numeral in LemLib or in generated code (fuel-parameter
# arc, 2026-09-04; [USER 2026-09-03]: every hardcoded magic value that
# cannot be quantified over is by definition a bug).
#
# Scanned (the code a consumer reasons against):
#   lean-lib/LemLib.lean, lean-lib/LemLib/*.lean (the generated library),
#   lean-lib/LemLibTheorems.lean, and every generated module in this suite
#   (Test_*.lean, *_auxiliary.lean here; P_*.lean under parity/lean-test).
# NOT scanned, by design: test harnesses and pins (lean-lib/LemLibTest.lean,
# lean-test/Test*.lean hand-written files, parity Run_*/main drivers) — a
# test suite may choose its fuel ("Defaults that are chosen eg. in test
# suites are fine", same ruling).
#
# Forbidden shapes (each a hardcoded fuel no context could quantify over):
#   F1  lemDefaultFuel                      the deleted library default
#   F2  instance … : LemFuel                a global instance = a hidden default
#   F3  <worker>_lemFuel <positive numeral> a worker run at a literal fuel
#                                           (`_lemFuel 0` is the exhaustion
#                                           lemma's statement, permitted;
#                                           the numeral must be the WHOLE
#                                           counter argument — `_lemFuel 5`,
#                                           `_lemFuel (5)`: a measured
#                                           wrapper's `_lemFuel (1 + n)` is a
#                                           data measure with an offset,
#                                           certified by its sufficiency
#                                           theorem, fuel-measure slice)
#   F4  LemFuel := ⟨…⟩ / LemFuel.mk         an instance built from a literal
#   F5  ⟨<numeral>⟩                        an anonymous-constructor literal
#                                           (the entry-point idiom `@f ⟨n⟩`
#                                           pasted into library/generated
#                                           code; `⟨n⟩` with a variable is
#                                           legal) — pre-merge audit M4
# Vacuity guards: the scan must see at least MIN_FILES files and at least
# one fuel worker (`_lemFuel`), or it is not scanning real generated code.
# Plant test (run by hand, quoted in the arc record §8.4/§10 and the
# fuel-measure record): the seven shapes — `spin_lemFuel 5 3`,
# `spin_lemFuel (5) 3` (F3; and `mlen_lemFuel (1 + List.length l)` stays green);
# `instance : LemFuel := ⟨N⟩`, `instance : LemFuel where fuel := 5`,
# `instance : LemFuel := LemFuel.mk k` (F2); `def i : LemFuel := LemFuel.mk 5`
# + attribute [instance] (F4); `lemDefaultFuel` (F1); `@spin ⟨5⟩ 3` (F5) —
# each red, reverted green.
set -u
HERE=$(cd "$(dirname "$0")" && pwd)
ROOT=$(cd "$HERE/../.." && pwd)
MIN_FILES=40
files=$(ls "$ROOT"/lean-lib/LemLib.lean "$ROOT"/lean-lib/LemLibTheorems.lean "$ROOT"/lean-lib/LemLib/*.lean \
           "$HERE"/Test_*.lean "$HERE"/*_auxiliary.lean 2>/dev/null; ls "$HERE"/parity/lean-test/P_*.lean 2>/dev/null)
n=$(echo "$files" | grep -c .)
if [ "$n" -lt "$MIN_FILES" ]; then echo "  FAIL (vacuous): only $n files to scan (< $MIN_FILES) — generate the suite first"; exit 1; fi
if ! echo "$files" | xargs grep -l '_lemFuel' > /dev/null 2>&1; then echo "  FAIL (vacuous): no fuel worker (_lemFuel) in the scanned files"; exit 1; fi
# Comments are not code: strip `-- …` line comments and `/- … -/` block
# comments (non-nested) before matching, so a HISTORY note may name the
# deleted constant while a code token of that name still fails. Each
# scanned file is reduced to "<path>:<line>: <code>" rows first.
strip_comments() { # file -> rows "<file>:<lineno>: <code-without-comments>"
  perl -e '
    my $f = shift; open(my $fh, "<", $f) or die; local $/; my $t = <$fh>;
    $t =~ s{/-.*?-/}{ join("", map { "\n" } 1..(() = $& =~ /\n/g)) }gse;   # keep line count
    my $n = 0; for my $l (split /\n/, $t, -1) { $n++; $l =~ s/--.*$//; print "$f:$n: $l\n" if $l =~ /\S/; }
  ' "$1"
}
rows=$(for f in $files; do strip_comments "$f"; done)
status=0
report() { # label pattern
  hits=$(echo "$rows" | grep -E "$2")
  if [ -n "$hits" ]; then echo "  FAIL ($1): fuel numeral shape found:"; echo "$hits" | head -20; status=1; fi
}
report F1 'lemDefaultFuel'
report F2 ':[[:space:]]*(@\[[^]]*\][[:space:]]*)?(scoped |local )?instance[^:]*:[[:space:]]*LemFuel\b'
report F3 '_lemFuel[[:space:]]+[1-9][0-9]*([^0-9A-Za-z_.'"'"']|$)|_lemFuel[[:space:]]*\([[:space:]]*[1-9][0-9]*[[:space:]]*\)'
report F4 'LemFuel[[:space:]]*:=[[:space:]]*⟨|LemFuel\.mk[[:space:]]+[0-9]'
report F5 '⟨[[:space:]]*[1-9][0-9]*[[:space:]]*⟩'
if [ $status -eq 0 ]; then echo "  OK: $n files scanned; no lemDefaultFuel, no LemFuel instance, no literal fuel (F1-F5)"; fi
exit $status
