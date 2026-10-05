#!/bin/sh
# Gate: no INSTANCE of an instance-reader class anywhere in lem-lean's own
# Lean tree (instance-reader slice, review F6, 2026-10-05).
#
# The instance-implicit reader (`declare {lean} reader val r = instance
# `Cls.field``) is sound only if no instance of `Cls` is in scope by
# default: every generated definition that reads `r` binds `[Cls]`, and the
# value must come from the caller (`@f ⟨v⟩`, `letI`), never from a global
# instance — the [LemFuel] rule (record
# doc/lean-backend/2026-10-05_instance-reader-record.md §2 "No instance
# anywhere"). A global instance would silently become a hidden default.
#
# The classes are DERIVED, not hard-coded: every `declare {…} reader val
# … = instance `P`` in the repository's .lem files (tests/, library/)
# contributes the class `P` minus its last dotted component. A written
# class name matches if it is a dotted suffix of the full class name (with
# an optional `_root_.`), so `Sw`, `Impl.Sw` and `_root_.Impl.Sw` all match
# `Impl.Sw`.
#
# Scanned: every *.lean under tests/ and lean-lib/ (the hand-written test
# files, the generated test modules, the parity and backends test trees,
# LemLib), `.lake/` excluded. Comments are stripped first.
#
# Forbidden shapes (C = a derived class):
#   I1  instance … : C …           (any modifiers, attributes, name,
#                                   binders, priority; the class directly
#                                   after a `:` on the header line)
#   I2  @[… instance …] def/abbrev … : C …
#   I3  deriving instance … C … for …
#   I4  attribute [… instance …] …  (the class of the named constant is not
#                                   syntactically visible: ANY such line is
#                                   refused; none exists in the tree)
# Limitation: a header split so that the class is on a later line than
# `instance` is not seen (none exists; the shapes above are line-based).
#
# Vacuity guards: at least one class must be derived; at least MIN_FILES
# files must be scanned; and some scanned file must DEFINE a derived class
# (`class C`), or the scan is not reaching the tree the declarations target.
#
# Plant test (by hand, quoted in the record §4): each of I1-I4 planted in
# lean-test/TestInstanceReaderCheck.lean turns the gate red; reverted, green.
set -u
HERE=$(cd "$(dirname "$0")" && pwd)
ROOT=$(cd "$HERE/../.." && pwd)
MIN_FILES=100
exec perl -e '
use strict; use warnings;
my ($root, $min) = @ARGV;
sub find_files { my ($dir, $re) = @_; my @out;
  opendir(my $dh, $dir) or die "cannot open $dir: $!";
  for my $e (sort readdir $dh) { next if $e eq "." || $e eq ".." || $e eq ".lake";
    my $p = "$dir/$e";
    if (-d $p && ! -l $p) { push @out, find_files($p, $re) } elsif (-f $p && $e =~ $re) { push @out, $p } }
  closedir $dh; return @out }
sub slurp { my $f = shift; open(my $fh, "<", $f) or die "cannot read $f: $!"; local $/; my $t = <$fh>; return $t }
# 1. derive the classes from the .lem declarations
my %cls;
for my $f (find_files("$root/tests", qr/\.lem$/), find_files("$root/library", qr/\.lem$/)) {
  my $t = slurp($f);
  $t =~ s{\(\*.*?\*\)}{}gs;   # lem comments (non-nested suffices for declarations)
  while ($t =~ /declare\s*(?:\{[^}]*\})?\s*reader\s+val\s+[\w\x27]+\s*=\s*instance\s*`([^`]*)`/g) {
    my $p = $1; $p =~ s/^_root_\.//; my @c = split /\./, $p; next if @c < 2; pop @c; $cls{join(".", @c)} = $f } }
my @classes = sort keys %cls;
if (!@classes) { print "  FAIL (vacuous): no instance-reader declaration found in the .lem files\n"; exit 1 }
# every dotted suffix of every class, longest first
my %suf; for my $c (@classes) { my @c = split /\./, $c; for my $i (0..$#c) { $suf{join(".", @c[$i..$#c])} = 1 } }
my $alt = join("|", map { quotemeta } sort { length($b) <=> length($a) || $a cmp $b } keys %suf);
my $C = qr/(?:_root_\.)?(?:$alt)(?![\w\x27.])/;
my $shortalt = join("|", map { my @c = split /\./; quotemeta($c[-1]) } @classes);
# 2. scan
my @files = (find_files("$root/tests", qr/\.lean$/), find_files("$root/lean-lib", qr/\.lean$/));
if (@files < $min) { printf "  FAIL (vacuous): only %d Lean files to scan (< %d)\n", scalar(@files), $min; exit 1 }
my ($defines, @hits) = (0);
for my $f (@files) {
  my $t = slurp($f);
  $t =~ s{/-.*?-/}{ join("", map { "\n" } 1..(() = $& =~ /\n/g)) }gse;   # keep line numbers
  my $n = 0;
  for my $l (split /\n/, $t, -1) { $n++; $l =~ s/--.*$//; next unless $l =~ /\S/;
    $defines = 1 if $l =~ /^\s*class\s+(?:$shortalt)\b/;
    my $why;
    if ($l =~ /\bderiving\s+instance\b.*(?<![\w\x27.])$C.*\bfor\b/) { $why = "I3" }
    elsif ($l =~ /^\s*attribute\s*\[[^\]]*\binstance\b/) { $why = "I4" }
    elsif ($l =~ /\@\[[^\]]*\binstance\b[^\]]*\].*?:(?!=)\s*$C/) { $why = "I2" }
    elsif ($l =~ /(?:^|[\s\]])instance\b.*?:(?!=)\s*$C/) { $why = "I1" }
    push @hits, "  $why $f:$n: $l" if $why } }
if (!$defines) { print "  FAIL (vacuous): no scanned file defines a derived class (" . join(", ", @classes) . ")\n"; exit 1 }
if (@hits) { print "  FAIL: an instance of an instance-reader class (a hidden default):\n"; print "$_\n" for @hits[0..($#hits < 19 ? $#hits : 19)]; exit 1 }
printf "  OK: %d Lean files scanned; no instance of the %d instance-reader classes (%s)\n", scalar(@files), scalar(@classes), join(", ", @classes);
exit 0
' "$ROOT" "$MIN_FILES"
