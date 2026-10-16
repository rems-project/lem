LEM = ../../lem
# ABSOLUTE (linksem 2026-09-28, B12): if LEMLIB is set in the caller's
# environment, make exports THIS value to every recipe, and a relative path
# is wrong for the recipes that change directory (parity/run.sh). Before the
# B10 fix lem then silently ran with no reserved-name list.
LEMLIB = $(abspath ../../library)
LEMFLAGS = -wl ign -i $(LEMLIB)/pervasives.lem
# Every lake invocation runs through the cgroup cap (parity-fix audit
# response, 2026-09-03: "never run a Lean build uncapped"); the same
# variables the parity runner honours. Fail-noisy if the cap is absent.
export CAPPED ?= $(abspath ../../scripts/capped)
export CERB_MEM_MAX ?= 16G
LAKE = "$(CAPPED)" lake

TESTS = $(sort $(wildcard test_*.lem))

.PHONY: all lean lean-wide-patterns lean-outdir-refusal lean-comments lean-layout lean-text-fidelity lean-multiclause lean-constants-required lean-generate lean-compile lean-negative lean-panic lean-untaken-failure lean-parity lean-fuel-param lean-fuel-mutual-reader lean-reader-multi lean-instance-reader lean-no-sorry-proofs lean-no-ireader-instances lean-no-fuel-numerals lean-version lean-parity-admission check-capped clean

check-capped:
	@test -x "$(CAPPED)" || { echo "FAIL: capped Lean runner '$(CAPPED)' not found or not executable (set CAPPED=...)"; exit 1; }

all: lean

# === Lean Backend ===

lean: lean-version lean-constants-required lean-parity-admission lean-wide-patterns lean-outdir-refusal lean-generate lean-comments lean-layout lean-text-fidelity lean-multiclause lean-compile lean-panic lean-untaken-failure lean-tuple-once lean-supply-draws lean-reader-consumer lean-reader-multi lean-instance-reader lean-fuel-param lean-fuel-mutual-reader lean-negative lean-invariance lean-parity lean-no-sorry-proofs lean-no-ireader-instances lean-no-fuel-numerals

# The reserved-name list is required (linksem 2026-09-28, B10): with the
# library's lean_constants missing, lem must refuse to generate Lean (it used
# to silently disable the renaming pass: unescaped keywords, ambiguous
# constructors). Plant: a library copy without the file.
lean-constants-required:
	@echo "=== Reserved-name list required (missing lean_constants is fatal) ==="
	@d=$$(mktemp -d); cp -r $(LEMLIB) $$d/lib && rm $$d/lib/lean_constants; \
	out=$$(LEMLIB=$$d/lib $(LEM) -wl ign -lean -outdir $$d test_misc.lem 2>&1); st=$$?; \
	ok=$$(LEMLIB=$(abspath $(LEMLIB)) $(LEM) -wl ign -lean -outdir $$d test_misc.lem 2>&1); st2=$$?; rm -rf $$d; \
	if [ $$st -eq 0 ] || ! echo "$$out" | grep -q "reserved-name list for target lean is missing"; then \
		echo "  FAIL: generation without lean_constants was not refused: exit $$st: $$out"; exit 1; \
	elif [ $$st2 -ne 0 ]; then echo "  FAIL: generation with the intact library failed: $$ok"; exit 1; \
	else echo "  OK: missing lean_constants refused; intact library generates"; fi

lean-parity-admission:
	@bash parity/test_failure_admission.sh

# Wide patterns generate in bounded time (backend-hardening 2026-10-03,
# item 5): a 150-wide constructor pattern and 60-tuples. Before the layout
# printer memoized its candidates, generation was exponential in the number
# of sibling groups on an overflowing line (47 wildcards: over two minutes;
# 150: killed after eleven minutes); measured 1.6 s after. The bound is
# generous (a slow box, not a regression, must pass); a regression hangs
# every later phase, so this one runs first and fails loudly instead.
LEAN_WIDE_PATTERNS_SECONDS ?= 60
lean-wide-patterns:
	@echo "=== Wide patterns generate within $(LEAN_WIDE_PATTERNS_SECONDS) s (layout printer regression tripwire) ==="
	@d=$$(mktemp -d); start=$$(date +%s); \
	if timeout $(LEAN_WIDE_PATTERNS_SECONDS) $(LEM) $(LEMFLAGS) -lean -outdir $$d test_wide_patterns.lem > $$d/log 2>&1; then \
		end=$$(date +%s); echo "  OK: test_wide_patterns.lem generated in $$((end - start)) s"; rm -rf $$d; \
	else st=$$?; \
		if [ $$st -eq 124 ]; then echo "  FAIL: generation of test_wide_patterns.lem exceeded $(LEAN_WIDE_PATTERNS_SECONDS) s (the layout printer's exponential re-decision is back?)"; \
		else echo "  FAIL: generation of test_wide_patterns.lem failed (exit $$st):"; head -5 $$d/log; fi; rm -rf $$d; exit 1; fi

# A failing output-directory creation is a fatal error naming the directory
# (backend-hardening 2026-10-03, item 8; TODO item 37): the parent here is a
# FILE, so the directory cannot be created. Before the fix the ignored
# `mkdir -p` exit code let lem go on to fail on the temp-file rename.
lean-outdir-refusal:
	@echo "=== Output directory that cannot be created is refused loudly ==="
	@out=$$($(LEM) $(LEMFLAGS) -lean -outdir Makefile/sub test_misc.lem 2>&1); st=$$?; \
	if [ $$st -eq 0 ]; then echo "  FAIL: lem exited 0 with an uncreatable -outdir"; exit 1; \
	elif ! echo "$$out" | grep -q "cannot create the output directory"; then echo "  FAIL: wrong error for an uncreatable -outdir:"; echo "$$out" | head -3; exit 1; \
	else echo "  OK: refused: $$(echo "$$out" | grep -o 'cannot create the output directory.*' | head -1 | cut -c1-100)"; fi

lean-version:
	@bash ../../scripts/test_version.sh

# Two-target parity (parity-fix slice 2026-09-03; [USER] ruling: the OCaml
# target is the reference semantics of a lem program, the Lean target
# must compute the same thing, zero discrepancies). parity/run.sh builds
# an OCaml binary AND a Lean binary from each parity/probes/*.lem, runs
# both, diffs stdout byte-for-byte, and checks the OCaml output against
# its committed pin (parity/expected/). Failure probes (f_*) must fail on
# both targets. Needs the complete opam environment (opam exec --) — the OCaml
# leg is what makes this a parity test rather than a self-consistency
# check (the retired M2 scaffold compared hand-measured values).
lean-parity:
	@echo "=== Two-target parity (OCaml reference vs Lean, compiled) ==="
	@./parity/run.sh

# Fuel as a quantified parameter (fuel-parameter arc, 2026-09-04;
# [USER 2026-09-03]: fuel is an execution parameter whose value does
# not matter): compiled witnesses that two different sufficient fuels give
# identical results, that an insufficient fuel gives exactly the declared
# sentinel, that a fuel'd callee starts from the FULL ambient, that a
# fuel_consumer reads the same ambient, and (leg 2, under
# LEAN_ABORT_ON_PANIC=1) that a loud sentinel at an insufficient RUNTIME
# fuel fail-stops the process at the program point.
lean-fuel-param:
	@echo "=== Fuel as a quantified parameter (compiled): sufficient fuels agree; exhaustion is loud ==="
	@cd lean-test && $(LAKE) build test-fuel-param > /dev/null
	@out=$$(cd lean-test && ./.lake/build/bin/test-fuel-param 2>&1); st=$$?; \
	if [ $$st -ne 0 ]; then \
		echo "  FAIL (leg 1, exit $$st):"; echo "$$out"; exit 1; \
	elif ! echo "$$out" | grep -q "fuel param: OK"; then \
		echo "  FAIL (leg 1): no OK line"; echo "$$out"; exit 1; \
	else \
		echo "  OK (leg 1): two sufficient fuels agree; insufficient gives the declared sentinel; callee starts from the full ambient"; \
	fi
	@out=$$(cd lean-test && LEAN_ABORT_ON_PANIC=1 ./.lake/build/bin/test-fuel-param --exhaust 2>&1); st=$$?; \
	if [ $$st -eq 0 ]; then \
		echo "  FAIL (leg 2): exited 0 under LEAN_ABORT_ON_PANIC=1 (exhaustion did not fail-stop)"; \
		echo "$$out"; exit 1; \
	elif echo "$$out" | grep -q "survived:"; then \
		echo "  FAIL (leg 2): execution continued past the exhaustion under LEAN_ABORT_ON_PANIC=1"; \
		echo "$$out"; exit 1; \
	elif ! echo "$$out" | grep -q "fuel exhausted"; then \
		echo "  FAIL (leg 2): fail-stopped without the fuel-exhausted message"; \
		echo "$$out"; exit 1; \
	else \
		echo "  OK (leg 2): loud exhaustion at an insufficient runtime fuel fail-stops (exit $$st)"; \
	fi

# No proof-evading token in a hand-written fuel_measure proofs module
# (pre-merge audit M2, 2026-09-04): the generated obligation makes the
# build fail for a MISSING or MISTYPED theorem, not for a `sorry`'d one;
# check_no_sorry_proofs.sh scans lean-test/*_lemMeasureProofs.lean and
# parity/probes/*.proofs.lean (comments stripped, vacuity-guarded,
# plant-tested). Runs after parity (its proofs files are in scope) and
# before the no-numerals gate, which stays last.
lean-no-sorry-proofs:
	@echo "=== No sorry/admit/axiom/native_decide in fuel_measure proofs modules (gate) ==="
	@./check_no_sorry_proofs.sh

# No instance of an instance-reader class anywhere in lem-lean's Lean tree
# (instance-reader slice, review F6, 2026-10-05): the classes are derived
# from the .lem `reader val ... = instance` declarations; a global instance
# would be a hidden default (the [LemFuel] rule). Plant-tested, see
# check_no_ireader_instances.sh. Runs after generation and parity, so the
# generated modules are under the scan.
lean-no-ireader-instances:
	@echo "=== No instance of an instance-reader class in the Lean tree (gate) ==="
	@./check_no_ireader_instances.sh

# No fuel numeral anywhere it could be magic (fuel-parameter arc gate;
# plant-tested, see check_no_fuel_numerals.sh): LemLib, the generated
# library, every generated test module — no `lemDefaultFuel`, no
# `instance … : LemFuel`, no worker applied to a positive numeral, no
# `LemFuel := ⟨N⟩`. The only permitted shape of a fuel is a caller's
# parameter; test harnesses (hand-written *Exec/*Check/Run_* drivers)
# choose theirs and are outside the scan by design. Runs LAST in the
# suite so that everything generated — including the parity runner's
# P_*.lean modules — is under the scan (pre-merge audit M3).
# Comments survive translation and the generated layout is sound
# (output-niceness S1, 2026-10-03): every comment of test_comments.lem is in
# Test_comments.lean exactly once (registered losses tagged KNOWN-LOST must
# stay absent), no code follows a multi-line comment on its last line, no
# whitespace-only lines or blank-line runs. Plants in the check's header.
lean-comments: lean-generate
	@echo "=== Comments and layout (gate) ==="
	@python3 check_comments.py test_comments.lem Test_comments.lean

# The layout pass (src/lean_layout.ml, output-niceness S3-A): in the
# generated Test_layout.lean every `|` starts its line, a let's body starts
# a new line, lines without a string or comment fit the width, no code
# follows a multi-line comment, and the file is not vacuous (L1-L5; plants
# recorded in doc/lean-backend/2026-10-03_output-niceness-arc-plan.md §11).
lean-layout: lean-generate
	@echo "=== Layout (gate) ==="
	@python3 check_layout.py Test_layout.lean

# Text that must come through the spacing and layout passes byte for byte
# (pre-merge audit of output-niceness, 2026-10-03): `×'`, `(p).1`, `'×'`,
# `«a b»`, `#eval do` blocks, all reached through target_rep text
# (test_text_fidelity.lem; rules T1-T6 in check_text_fidelity.py).
lean-text-fidelity: lean-generate
	@echo "=== Target_rep text fidelity (gate) ==="
	@python3 check_text_fidelity.py Test_text_fidelity.lean Test_text_fidelity_auxiliary.lean

# Multi-clause definitions render as Lean equations (TODO item 39): the
# generated Test_multiclause.lean must carry the equation form for the
# literal- and cons-pattern groups and a single `match` for the constructor
# pattern group; the asserts in the auxiliary file pin the behaviour.
lean-multiclause: lean-generate
	@echo "=== Multi-clause definitions render as Lean equations (TODO item 39 pin) ==="
	@f=Test_multiclause.lean; fail=0; \
	for pat in '^def f : Nat → Nat$$' '^  | (0 : Nat) => 1$$' '^  | (n : Nat) => n$$' \
	           '^partial def len2 : List Nat → Nat$$' '^  | (\[\] : List Nat) => 0$$' '^  | (x :: xs) => 1 + len2 xs$$' \
	           '^def g (m : Option Nat) : Nat :=$$' '^  match m with$$'; do \
		if ! grep -q -- "$$pat" $$f; then echo "  FAIL: $$f lacks the line /$$pat/"; fail=1; fi; \
	done; \
	if grep -q '^def g : Option Nat' $$f; then echo "  FAIL: the constructor-pattern group rendered as equations"; fail=1; fi; \
	test $$fail -eq 0 && echo "  OK: equation form for f and len2, match form for g"

lean-no-fuel-numerals:
	@echo "=== No fuel numerals in LemLib or generated code (gate) ==="
	@./check_no_fuel_numerals.sh

# reader_consumer compiled behavioral test (effect-retirement L1,
# charter §4.2): consumer call sites must receive the reader value in
# compiled code — lifted-caller injection, HOF partial application,
# and the reader_seed override (elaborator pins live in
# TestReaderConsumerCheck.lean).
lean-reader-consumer:
	@echo "=== reader_consumer injection pin (compiled) ==="
	@cd lean-test && $(LAKE) build test-reader-consumer > /dev/null
	@out=$$(cd lean-test && ./.lake/build/bin/test-reader-consumer 2>&1); st=$$?; \
	if [ $$st -ne 0 ]; then \
		echo "  FAIL (exit $$st):"; echo "$$out"; exit 1; \
	elif ! echo "$$out" | grep -q "reader_consumer: OK"; then \
		echo "  FAIL: no OK line"; echo "$$out"; exit 1; \
	else \
		echo "  OK: compiled consumer injection holds"; \
	fi

# N-ary reader_seed compiled pin (program-data-parameters S0.5,
# 2026-09-19): with three declared readers the seed def's first three
# arguments seed the readers positionally in the global sorted order
# (alpha, beta, gamma — not the declaration order); the compiled binary
# re-asserts the value pins a positional swap of the two same-typed
# readers would break, the pickup through the consumer and through
# lifted callees, and the supply composition (elaborator pins live in
# TestReaderMultiCheck.lean).
lean-reader-multi:
	@echo "=== N-ary reader_seed injection pin (compiled) ==="
	@cd lean-test && $(LAKE) build test-reader-multi > /dev/null
	@out=$$(cd lean-test && ./.lake/build/bin/test-reader-multi 2>&1); st=$$?; \
	if [ $$st -ne 0 ]; then \
		echo "  FAIL (exit $$st):"; echo "$$out"; exit 1; \
	elif ! echo "$$out" | grep -q "reader_multi: OK"; then \
		echo "  FAIL: no OK line"; echo "$$out"; exit 1; \
	else \
		echo "  OK: compiled N-ary seed injection holds"; \
	fi

# Instance-implicit readers (instance-reader slice, 2026-10-05;
# doc/lean-backend/2026-10-05_instance-reader-record.md): the compiled
# binary chooses the [Sw] instance at RUNTIME (from its argument count) and
# re-asserts that it reaches every lifted definition — the transitive
# callee, the consumer, the seed def, the fuel'd mutual block, the
# coexistence def and the measured def (signature and kernel pins live in
# TestInstanceReaderCheck.lean). Leg 2 runs it with one argument, so a
# value folded at compile time from one instance would fail one leg.
lean-instance-reader:
	@echo "=== Instance-implicit readers (compiled): the entry point's instance reaches every lifted definition ==="
	@cd lean-test && $(LAKE) build test-instance-reader > /dev/null
	@for a in "" "x"; do \
		out=$$(cd lean-test && ./.lake/build/bin/test-instance-reader $$a 2>&1); st=$$?; \
		if [ $$st -ne 0 ]; then \
			echo "  FAIL (args '$$a', exit $$st):"; echo "$$out"; exit 1; \
		elif ! echo "$$out" | grep -q "instance reader: OK"; then \
			echo "  FAIL (args '$$a'): no OK line"; echo "$$out"; exit 1; \
		fi; \
	done; echo "  OK: compiled instance-reader lifting holds at two runtime instances"

# fuel x reader x truly-mutual blocks (program-data-parameters S1.5,
# 2026-09-20): a fuel'd truly-mutual block whose members are reader-lifted
# now generates (arc 3 B2's guard is gone); the compiled binary re-asserts
# that the reader value reaches every member (both-read and one-read
# blocks), that sibling hops pass the decremented counter (the sentinel of
# the member hitting 0), that a fuel'd callee reached from a member starts
# from the FULL ambient, and that the measured pair's fuel-free wrappers
# follow the reader (kernel pins in TestFuelMutualReaderCheck.lean; the
# measured pair's obligations proved in
# Test_fuel_mutual_reader_lemMeasureProofs.lean).
lean-fuel-mutual-reader:
	@echo "=== fuel x reader x mutual (compiled): readers reach every member of a fuel'd mutual block ==="
	@cd lean-test && $(LAKE) build test-fuel-mutual-reader > /dev/null
	@out=$$(cd lean-test && ./.lake/build/bin/test-fuel-mutual-reader 2>&1); st=$$?; \
	if [ $$st -ne 0 ]; then \
		echo "  FAIL (exit $$st):"; echo "$$out"; exit 1; \
	elif ! echo "$$out" | grep -q "fuel mutual reader: OK"; then \
		echo "  FAIL: no OK line"; echo "$$out"; exit 1; \
	else \
		echo "  OK: compiled fuel x reader x mutual composition holds"; \
	fi

# Supply-lifting compiled behavioral test (effect-retirement L1): the
# threaded supply's draw sequences — strict-order numbering, single
# evaluation of destructuring RHSes, fuel/reader/multi-supply
# composition — re-asserted in a real binary (elaborator pins live in
# TestSupplyCheck.lean; compiled-code divergence is exactly the class
# the 2026-08-31 review found untested for effectful).
lean-supply-draws:
	@echo "=== Supply draw-sequence pin (compiled) ==="
	@cd lean-test && $(LAKE) build test-supply-draws > /dev/null
	@out=$$(cd lean-test && ./.lake/build/bin/test-supply-draws 2>&1); st=$$?; \
	if [ $$st -ne 0 ]; then \
		echo "  FAIL (exit $$st):"; echo "$$out"; exit 1; \
	elif ! echo "$$out" | grep -q "supply draws: OK"; then \
		echo "  FAIL: no OK line"; echo "$$out"; exit 1; \
	else \
		echo "  OK: compiled draw sequences hold"; \
	fi

# Non-Lean invariance (effect-retirement charter §6.1/§6.3): the
# '{lean}'-scoped declares in invariance/inv_*.lem must be exact
# no-ops for the semantic emitters — generate each module with and
# without them and byte-compare. Vacuity-guarded: the strip must
# actually remove lines and outputs must exist. (The echoing/human
# targets — lem, ident, tex, html — deliberately re-render declare
# lines; they are covered by the nonlean-regress golden net.) Known
# false-positive SHAPE (D2-enablers audit NOTE-6): stripping a declare
# line shifts the source LINE of everything after it, and the OCaml
# auxiliary records an assert's location as a string (`run_test "x"
# "File …, line N …"`) — so a witness with an `assert` AFTER a declare
# would diff on that string alone. Keep asserts before the declares (or
# out of the witnesses; none of the current six has one).
lean-invariance:
	@echo "=== Non-Lean invariance ({lean} declares are no-ops for ocaml/hol/isa/coq) ==="
	@fail=0; \
	for src in invariance/inv_*.lem; do \
		name=$$(basename $$src); \
		rm -rf invariance/_out; \
		mkdir -p invariance/_out/decl invariance/_out/strip; \
		cp $$src invariance/_out/decl/$$name; \
		grep -v '^declare {lean}' $$src > invariance/_out/strip/$$name; \
		if cmp -s invariance/_out/decl/$$name invariance/_out/strip/$$name; then \
			echo "  FAIL (vacuous): $$name contains no 'declare {lean}' lines"; fail=1; continue; \
		fi; \
		for tgt in ocaml hol isa coq; do \
			(cd invariance/_out/decl && $(CURDIR)/../../lem -wl ign -i $(CURDIR)/../../library/pervasives.lem -$$tgt $$name > /dev/null 2>&1) \
				|| { echo "  FAIL: $$name -$$tgt (declared variant did not generate)"; fail=1; }; \
			(cd invariance/_out/strip && $(CURDIR)/../../lem -wl ign -i $(CURDIR)/../../library/pervasives.lem -$$tgt $$name > /dev/null 2>&1) \
				|| { echo "  FAIL: $$name -$$tgt (stripped variant did not generate)"; fail=1; }; \
		done; \
		rm -f invariance/_out/decl/$$name invariance/_out/strip/$$name; \
		if [ $$(ls invariance/_out/decl | wc -l) -eq 0 ]; then \
			echo "  FAIL (vacuous): $$name produced no non-Lean outputs"; fail=1; continue; \
		fi; \
		if diff -r invariance/_out/decl invariance/_out/strip > /dev/null; then \
			echo "  OK: $$name ($$(ls invariance/_out/decl | wc -l) artifacts byte-identical across ocaml/hol/isa/coq)"; \
		else \
			echo "  FAIL: $$name non-Lean output changed by {lean} declares:"; \
			diff -r invariance/_out/decl invariance/_out/strip | head -10; fail=1; \
		fi; \
	done; \
	rm -rf invariance/_out; exit $$fail

# m7 single-evaluation pin (2026-08-31 backend quality review): a
# multi-name destructuring let's RHS must run ONCE in compiled code —
# the historical per-binding RHS duplication ran effects once per bound
# name (and would silently fork a threaded supply). Compiled-binary
# check: the two counter draws bound by one tuple let must be {1, 2}.
lean-tuple-once:
	@echo "=== m7 single-evaluation pin (tuple-let RHS runs once) ==="
	@cd lean-test && $(LAKE) build test-tuple-let-once > /dev/null
	@out=$$(cd lean-test && ./.lake/build/bin/test-tuple-let-once 2>&1); st=$$?; \
	if [ $$st -ne 0 ]; then \
		echo "  FAIL (exit $$st): $$out"; exit 1; \
	elif ! echo "$$out" | grep -q "single-evaluation: OK"; then \
		echo "  FAIL: no OK line"; echo "$$out"; exit 1; \
	else \
		echo "  OK: $$out"; \
	fi

# Panic-path pin (arc-8 audit fix, auditor A F1): head_undef's
# incomplete-match arm must be a failwithI RAISE carrying the
# Incomplete Pattern message (mirroring OCaml's `failwith m`), never a
# silent default. Two legs (see TestFailwithThreadingPanic.lean):
#  1. library-call semantics (no env var): the panic PRINTS the
#     Incomplete Pattern message, then CONTINUES with the Inhabited
#     default (`survived:` line). Pre-fix this run printed NOTHING —
#     the message line is the pin of the fix.
#  2. harness discipline (LEAN_ABORT_ON_PANIC=1, cerberus
#     scripts/common.sh): the run must fail-stop (nonzero exit). The
#     abort used to fire at module INIT (closed-term extraction lifted
#     LemLib's failwithI applications to initialisation constants,
#     messages disabled there); the parity-fix slice (2026-09-03) made
#     failwithI/fuelExhaustedWith and their implementations
#     `never_extract`, so the abort now fires at the program point —
#     the message is still asserted on leg 1.
lean-panic:
	@echo "=== Panic-path pin (failwithI raise at the L_undefined arm) ==="
	@cd lean-test && $(LAKE) build test-failwith-panic > /dev/null
	@out=$$(cd lean-test && env -u LEAN_ABORT_ON_PANIC ./.lake/build/bin/test-failwith-panic 2>&1); st=$$?; \
	if [ $$st -ne 0 ]; then \
		echo "  FAIL (leg 1): nonzero exit $$st without LEAN_ABORT_ON_PANIC"; \
		echo "$$out"; exit 1; \
	elif ! echo "$$out" | grep -q "PANIC"; then \
		echo "  FAIL (leg 1): no PANIC line — the arm degraded to a silent default"; \
		echo "$$out"; exit 1; \
	elif ! echo "$$out" | grep -q "Incomplete Pattern"; then \
		echo "  FAIL (leg 1): panic without the Incomplete Pattern message"; \
		echo "$$out"; exit 1; \
	elif ! echo "$$out" | grep -q "survived:"; then \
		echo "  FAIL (leg 1): no post-panic default (library-call semantics changed)"; \
		echo "$$out"; exit 1; \
	else \
		echo "  OK (leg 1): panic prints the Incomplete Pattern message, then continues with default"; \
	fi
	@out=$$(cd lean-test && LEAN_ABORT_ON_PANIC=1 ./.lake/build/bin/test-failwith-panic 2>&1); st=$$?; \
	if [ $$st -eq 0 ]; then \
		echo "  FAIL (leg 2): exited 0 under LEAN_ABORT_ON_PANIC=1 (no fail-stop)"; \
		echo "$$out"; exit 1; \
	elif echo "$$out" | grep -q "survived:"; then \
		echo "  FAIL (leg 2): execution continued past the panic under LEAN_ABORT_ON_PANIC=1"; \
		echo "$$out"; exit 1; \
	else \
		echo "  OK (leg 2): fail-stops (exit $$st) under LEAN_ABORT_ON_PANIC=1"; \
	fi

# Untaken failure branches (linksem 2026-09-28, B8/B9): a closed call to a
# partial function in an UNTAKEN branch must not run at module init. Lean
# 4.28 initialised hoisted closed terms eagerly at load (silent SIGABRT under
# LEAN_ABORT_ON_PANIC=1: panic messages are off during init); 4.32 does it
# lazily, so since the 4.32.2 move this target is the GUARD of that toolchain
# property (the per-module `extract_closed false` workaround is retired).
# Leg 1 no longer discriminates B8 (`never_extract` on nullary polymorphic
# definitions) on 4.32.2; leg 4 does: without the attribute the lazily
# initialised closed term is cached and a second reached failure is silent.
# Leg 3 pins LemLib's lemRequireAbortOnPanic (D1(b) [USER 2026-09-30]).
lean-untaken-failure:
	@echo "=== Untaken failure branches are not evaluated at module init ==="
	@cd lean-test && $(LAKE) build test-untaken-failure > /dev/null
	@out=$$(cd lean-test && LEAN_ABORT_ON_PANIC=1 ./.lake/build/bin/test-untaken-failure 2>&1); st=$$?; \
	if [ $$st -ne 0 ] || [ "$$out" != "untaken: 0 z" ]; then \
		echo "  FAIL (leg 1): exit $$st, output '$$out' (expected 'untaken: 0 z', exit 0)"; exit 1; \
	else echo "  OK (leg 1): untaken branches not evaluated"; fi
	@out=$$(cd lean-test && LEAN_ABORT_ON_PANIC=1 ./.lake/build/bin/test-untaken-failure take 2>&1); st=$$?; \
	if [ $$st -eq 0 ] || ! echo "$$out" | grep -q "must_be_small: too big"; then \
		echo "  FAIL (leg 2): exit $$st without the failure message: $$out"; exit 1; \
	else echo "  OK (leg 2): the taken branch fail-stops with its message"; fi
	@out=$$(cd lean-test && env -u LEAN_ABORT_ON_PANIC ./.lake/build/bin/test-untaken-failure failstop 2>&1); st=$$?; \
	if [ $$st -eq 0 ] || ! echo "$$out" | grep -q "lemRequireAbortOnPanic: refused" || echo "$$out" | grep -q "untaken:\|must_be_small"; then \
		echo "  FAIL (leg 3a): lemRequireAbortOnPanic with LEAN_ABORT_ON_PANIC unset did not refuse before running: exit $$st: $$out"; exit 1; \
	else echo "  OK (leg 3a): lemRequireAbortOnPanic refuses with LEAN_ABORT_ON_PANIC unset (exit $$st)"; fi
	@out=$$(cd lean-test && LEAN_ABORT_ON_PANIC=0 ./.lake/build/bin/test-untaken-failure failstop 2>&1); st=$$?; \
	if [ $$st -eq 0 ] || ! echo "$$out" | grep -q "lemRequireAbortOnPanic: refused" || echo "$$out" | grep -q "untaken:\|must_be_small"; then \
		echo "  FAIL (leg 3b): lemRequireAbortOnPanic with LEAN_ABORT_ON_PANIC=0 did not refuse: exit $$st: $$out"; exit 1; \
	else echo "  OK (leg 3b): lemRequireAbortOnPanic refuses LEAN_ABORT_ON_PANIC=0 (exit $$st)"; fi
	@out=$$(cd lean-test && LEAN_ABORT_ON_PANIC=1 ./.lake/build/bin/test-untaken-failure failstop 2>&1); st=$$?; \
	if [ $$st -eq 0 ] || ! echo "$$out" | grep -q "must_be_small: too big" || echo "$$out" | grep -q "untaken:\|refused"; then \
		echo "  FAIL (leg 3c): with LEAN_ABORT_ON_PANIC=1 the check did not pass through to a fail-stop: exit $$st: $$out"; exit 1; \
	else echo "  OK (leg 3c): with LEAN_ABORT_ON_PANIC=1 the check passes and the failure fail-stops (exit $$st)"; fi
	@out=$$(cd lean-test && env -u LEAN_ABORT_ON_PANIC ./.lake/build/bin/test-untaken-failure twice 2>&1); st=$$?; \
	n=$$(echo "$$out" | grep -c "^PANIC at .*: fail$$"); \
	if [ $$st -ne 0 ] || [ "$$n" -ne 2 ] || ! echo "$$out" | grep -q "twice-2"; then \
		echo "  FAIL (leg 4): expected 2 PANIC lines (one per reached Assert_extra.fail, B8 never_extract), got $$n, exit $$st: $$out"; exit 1; \
	else echo "  OK (leg 4): each reached Assert_extra.fail panics (2 of 2; B8 never_extract)"; fi

# Negative probes: each negative/neg_*.lem MUST be rejected, and with the
# error fragment declared in its first-line "(* EXPECT: ... *)" header —
# a rejection for the wrong reason (e.g. a type error) is a FAIL.
lean-negative:
	@echo "=== Negative probes (must be rejected with the declared error) ==="
	@fail=0; \
	for f in negative/neg_*.lem; do \
		exp=$$(sed -n 's/^(\* EXPECT: \(.*\) \*)$$/\1/p' $$f | head -1); \
		out=$$($(LEM) $(LEMFLAGS) -lean $$f 2>&1); \
		if [ $$? -eq 0 ]; then \
			echo "  FAIL (accepted): $$f"; fail=1; \
		elif ! echo "$$out" | grep -qF "$$exp"; then \
			echo "  FAIL (rejected for the wrong reason): $$f"; \
			echo "$$out" | head -3; fail=1; \
		else \
			echo "  OK (rejected as declared): $$f"; \
		fi; \
	done; exit $$fail

# Generate all .lean files from .lem sources
lean-generate: $(TESTS)
	@echo "=== Generating Lean files ==="
	@pass=0; fail=0; skip=0; \
	for f in $(TESTS); do \
		base=$$(basename $$f .lem); \
		if grep -q "^$$f,lean," expected_failures.txt 2>/dev/null; then \
			echo "  SKIP (expected failure): $$f"; \
			skip=$$((skip + 1)); \
		else \
			if $(LEM) $(LEMFLAGS) -lean $$f > /dev/null 2>&1; then \
				echo "  OK: $$f"; \
				pass=$$((pass + 1)); \
			else \
				echo "  FAIL: $$f"; \
				$(LEM) $(LEMFLAGS) -lean $$f 2>&1 | head -5; \
				fail=$$((fail + 1)); \
			fi; \
		fi; \
	done; \
	echo "=== Generation: $$pass passed, $$fail failed, $$skip skipped ==="; \
	test "$$fail" -eq 0
	@# Multi-file tests: files that must be compiled together (like Cerberus)
	@# so that lean_mutual_records accumulates across files.
	@if $(LEM) $(LEMFLAGS) -lean test_cross_recup_base.lem test_cross_recup_import.lem > /dev/null 2>&1; then \
		echo "  OK: test_cross_recup_base.lem + test_cross_recup_import.lem (joint)"; \
	else \
		echo "  FAIL: test_cross_recup_base.lem + test_cross_recup_import.lem (joint)"; exit 1; \
	fi
	@if $(LEM) $(LEMFLAGS) -lean test_cross_field_access.lem test_cross_field_access_import.lem > /dev/null 2>&1; then \
		echo "  OK: test_cross_field_access.lem + test_cross_field_access_import.lem (joint)"; \
	else \
		echo "  FAIL: test_cross_field_access.lem + test_cross_field_access_import.lem (joint)"; exit 1; \
	fi

# Symlink generated files into lean-test/ and compile with Lake
lean-compile: check-capped
	@echo "=== Compiling Lean files ==="
	@for f in Test_*.lean *_auxiliary.lean; do \
		if [ -f "$$f" ] && [ ! -e "lean-test/$$f" ]; then \
			ln -sf "../$$f" "lean-test/$$f"; \
		fi; \
	done
	@cd lean-test && $(LAKE) build

clean:
	rm -f *.lean *_ok
	@# generated files are SYMLINKED into lean-test/ (lean-compile); remove only
	@# symlinks — a hand-written module whose name follows a generated one
	@# (Test_<x>_lemMeasureProofs.lean, fuel-measure slice) must survive clean
	find lean-test -maxdepth 1 -type l \( -name "Test_*.lean" -o -name "*_auxiliary.lean" \) -delete
	rm -rf lean-test/.lake lean-test/build
