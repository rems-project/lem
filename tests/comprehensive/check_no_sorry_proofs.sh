#!/bin/sh
# Gate: no proof-evading token in a hand-written fuel_measure PROOFS module
# (pre-merge audit M2, 2026-09-04). The generated obligation
# `f_measure_sufficient := <Module>_lemMeasureProofs.f_measure_sufficient …`
# makes the build fail when the proofs module, the theorem, or a theorem
# of the stated type is missing — but a `sorry`'d (or axiom-backed) theorem
# of the right type builds. This scan closes that: any of the tokens below
# in a proofs module fails the phase. Comments are stripped first (a
# comment may name the token); the scan is vacuity-guarded (at least one
# proofs module must be found, and at least one must contain a
# `_measure_sufficient` theorem). Downstream, cerberus's own sorry/axiom
# gates cover its seams, where its proofs modules live.
#   scanned: lean-test/*_lemMeasureProofs.lean, parity/probes/*.proofs.lean
#   tokens:  sorry admit axiom native_decide bv_decide ofReduceBool ofReduceNat
# Plant test (by hand, quoted in the fuel-measure record's audit-response
# section): `sorry` for one proof body — red; restored — green.
set -u
HERE=$(cd "$(dirname "$0")" && pwd)
files=$(ls "$HERE"/lean-test/*_lemMeasureProofs.lean "$HERE"/parity/probes/*.proofs.lean 2>/dev/null)
n=$(echo "$files" | grep -c .)
if [ "$n" -lt 1 ]; then echo "  FAIL (vacuous): no fuel_measure proofs module found"; exit 1; fi
if ! echo "$files" | xargs grep -l '_measure_sufficient' > /dev/null 2>&1; then echo "  FAIL (vacuous): no _measure_sufficient theorem in the proofs modules"; exit 1; fi
strip_comments() { # file -> rows "<file>:<lineno>: <code-without-comments>"
  perl -e '
    my $f = shift; open(my $fh, "<", $f) or die; local $/; my $t = <$fh>;
    $t =~ s{/-.*?-/}{ join("", map { "\n" } 1..(() = $& =~ /\n/g)) }gse;
    my $n = 0; for my $l (split /\n/, $t, -1) { $n++; $l =~ s/--.*$//; print "$f:$n: $l\n" if $l =~ /\S/; }
  ' "$1"
}
rows=$(for f in $files; do strip_comments "$f"; done)
hits=$(echo "$rows" | grep -E '(^|[^A-Za-z0-9_.])(sorry|admit|axiom|native_decide|bv_decide|ofReduceBool|ofReduceNat)([^A-Za-z0-9_]|$)')
if [ -n "$hits" ]; then echo "  FAIL: proof-evading token in a fuel_measure proofs module:"; echo "$hits" | head -20; exit 1; fi
echo "  OK: $n proofs modules scanned; no sorry/admit/axiom/native_decide/bv_decide token"
exit 0
