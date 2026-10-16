# The Lean backend for Lem

Last reconciled with the source at `131b922` (2026-10-03, the
output-niceness arc with its audit fixes); what was checked when is in
[RECORDS.md](RECORDS.md#when-the-front-documents-were-checked).
This is an early experimental backend, not a general correctness proof.

This fork adds a **Lean 4 backend** to [Lem](https://github.com/rems-project/lem):
`lem -lean` compiles Lem definitions to Lean 4 source that builds
against the [LemLib runtime](../../lean-lib/). It was built to port
the [Cerberus](https://github.com/rems-project/cerberus) C semantics
to Lean — the same Lem model that generates Cerberus's OCaml
implementation now also generates a Lean implementation — but it is a
general Lem backend, exercised by its own test suite independently of
Cerberus.

**Provenance.** The Lean backend was developed primarily by AI agents
(Claude, Anthropic) operating under the direction and review of a
human operator (Mike Dodds). Upstream Lem is by its own authors (see
the [top-level README](../../README.md)); the dated records indexed in
[RECORDS.md](RECORDS.md) are the working history of the backend.

Who this is for:

- You have a Lem specification and want an **executable Lean 4
  version** of it.
- You want the generated code to be **reasoned about in Lean** —
  the backend's design choices (below) exist to keep generated code
  proof-friendly.
- You want to understand **how the backend works** — see
  [DESIGN.md](DESIGN.md).

## Quickstart

Use this fork explicitly: the upstream opam release does not contain the
Lean backend. The measured platform is Linux x86_64; other platforms are
unverified. Prerequisites are Git, Bash, GNU make/coreutils/diffutils,
a C toolchain, opam 2, and elan with the toolchain in `lean-lib/lean-toolchain` installed
(Lean 4.32.2, the toolchain Cerberus uses; record:
[linksem findings](2026-09-28_linksem-findings.md), "Toolchain move to
Lean 4.32.2"). Package constraints are in `opam`. Public repository/ref
availability and a fresh dependency download remain operator checks in
the cleanup evidence; offline tests used preinstalled dependencies.

If opam has not been initialized, run `opam init --bare --no-setup` once
before the following commands.

```bash
git clone --branch mdd/lean-backend https://github.com/OathTech/lem-lean.git
cd lem-lean
opam switch create . ocaml-base-compiler.5.4.0 --no-switch --no-install
opam pin add --switch=. lem . --yes
opam exec --switch=. -- make
opam exec --switch=. -- make lean-libs

# Generate, compile, and evaluate a small client against this same LemLib.
mkdir demo-lean
cp lean-lib/lean-toolchain demo-lean/lean-toolchain
cat > demo-lean/demo.lem <<'EOF'
open import Pervasives
let double (x : nat) : nat = x * 2
EOF
./lem -wl ign -i library/pervasives.lem -lean demo-lean/demo.lem
cat > demo-lean/lakefile.lean <<'EOF'
import Lake
open Lake DSL
package Demo
require LemLib from "../lean-lib"
lean_lib Demo
@[default_target]
lean_lib Check where
  roots := #[`Check]
EOF
cat > demo-lean/Check.lean <<'EOF'
import Demo
example : double 21 = 42 := rfl
#eval double 21
EOF
(cd demo-lean && ../scripts/capped lake build)
# Check compiles, the equation is kernel checked, and #eval prints 42.

opam exec --switch=. -- make -C tests/comprehensive lean
opam exec --switch=. -- make nonlean-regress
```

`scripts/capped` is repository-local; the comprehensive suite uses it by
default. `CAPPED=/path/to/wrapper` overrides the suite runner. The wrapper
uses Linux cgroup v2, then a systemd user service. Direct invocations
default to 64G; the comprehensive/parity harness defaults to 16G.
`CERB_MEM_MAX=none` is an explicit, loudly reported uncapped opt-out.
`CERB_JOB_CGROUP=/delegated/path` requests a caller-owned cgroup subtree;
setup failure in that mode is fatal. These mechanisms require Linux cgroup
v2 delegation or a working systemd user service to enforce a cap. If direct cgroup setup
fails and `systemd-run` is absent, it warns and runs uncapped. If
`systemd-run` exists but its user service is unavailable, the command fails. `CERB_MEM_MAX=32G` sets
the cap on a suitably provisioned machine; it is an upper limit, not a
minimum RAM requirement. Run native clients with
`LEAN_ABORT_ON_PANIC=1` (without it a reached Lean panic CONTINUES with a
default value), and call LemLib's `lemRequireAbortOnPanic` first thing in
their `main`: it refuses to run unless the variable is exactly `1`. (It
replaces `lemFailStop`, removed on 2026-09-30: an API break for existing
drivers; migration in `2026-09-28_linksem-findings.md`, "Migration note".) This does not prevent Lean
from eliminating an unused pure failure (see the limitations below).

The [manual](../manual/backend_lean.md) describes the language and a
reusable Lake setup. Issues about the fork's Lean backend belong in
[OathTech/lem-lean issues](https://github.com/OathTech/lem-lean/issues);
include the commit, toolchain, minimal `.lem` source and exact command.

## Validation levels

1. **Newcomer smoke:** the quickstart builds Lem, generates LemLib and a
   small client, and compiles/evaluates `double 21`. This checks installation
   and integration, not comprehensive language support.
2. **Backend regression:** `make -C tests/comprehensive lean` checks generated
   Lean, comment preservation and layout, negative refusals, invariance and
   OCaml/Lean parity with panic-abort enabled for native probes; ten
   registered parity expected failures remain (see Known limits). A build/setup failure is a failure even on a registered
   XFAIL probe. `make nonlean-regress` compares the nine other
   emitters' outputs and exit statuses with committed goldens.
   `make upstream-drift DRIFT_OUT=<empty dir>` compares the fork's non-Lean
   output (library, `tests/backends`, and linksem's and Cerberus's OCaml)
   with a pristine upstream Lem build (`tests/upstream-drift/run.sh` gives
   the required checkouts).
   `bash scripts/test_version.sh` checks the version recipe using isolated
   scratch tags. `make lean-tests` is an older, broader aggregate including
   historical examples; its existence is not a claim that all examples pass.
3. **Consumer/release validation:** Cerberus has its own toolchain, fork-drift
   prerequisites, lanes and release evidence. A Lem test pass does not certify
   that consumer or its full release ladder. Neither fork currently has a
   GitHub Actions Lean certification workflow; the dated manual gate records
   are the evidence for these claims.

`lem -v` includes a Git hash even at an exact annotated tag
(`tag-0-g<hash>`, optionally `-dirty`). An archive without Git metadata falls
back to `LEMRELEASE`; it cannot attest a commit, and a consumer requiring a
hash must reject that fallback.

## What you can rely on about the output

- **One model, two implementations.** The same Lem source generates
  both the OCaml and the Lean code, so differences can be investigated against shared source. Known
  differences and deliberate numeric exceptions are listed below. (Further differential
  evidence lives downstream: the cerberus-lean project runs its generated-Lean
  semantics differentially against the OCaml implementation across
  thousands-of-programs corpora — see that repository's
  `lean_frontend/VALIDATION.md` for what is compared, against what,
  and what its gates guarantee, and its `lean_frontend/DESIGN.md`.)
- **No inserted live proof holes or unsafe casts.** Bare `sorry` target
  representations are refused at generation time, including unused
  declarations and parameterized representations. Unsupported constructs
  are rejected or receive an explicit `failwithI` failure. Raw Lean
  snippets and hand-written implementations remain trusted inputs:
  generation is not a Lean parser or an axiom audit of arbitrary text.
  Compile and audit the actual downstream dependency cone.
- **Totality on demand; the fuel is yours.** By default, recursive
  Lem functions emit as Lean `partial def` (executable, but opaque to
  the kernel). A recursion that is structural on its data is marked
  `declare {lean} structural val f` and emits an ordinary `def` with
  `termination_by structural <param>` — Lean proves termination, the
  well-founded fallback is forbidden, and the kernel computes through
  it (`decide`/`rfl` on closed terms). Anything else is marked
  ``declare {lean} fuel val f = `sentinel` ``, which emits a total worker
  that recurses structurally on an
  explicit fuel counter, plus a wrapper `f [LemFuel] := f_lemFuel
  LemFuel.fuel` that starts the counter from the AMBIENT fuel — a
  parameter of the generated code (an instance-implicit `[LemFuel]`
  binder on `f` and on everything that reaches it), never a numeral:
  no default exists in the library or the output; the entry point
  chooses (`@f ⟨n⟩ …`), a theorem quantifies (`∀ [LemFuel]`), and
  `f_lemFuel_zero` states the exhaustion case by `rfl`. The backtick
  payload is the expression returned when the counter runs out; write
  it as `fuelExhausted <witness>` to make exhaustion a loud panic. A
  fuel'd function whose recursion is bounded by its data (but not in the
  structural checker's shape) adds ``declare {lean} fuel_measure val f =
  `List.length xs + 1` ``: the wrapper starts the counter from that
  computable measure of the arguments (`def f (xs : …) := f_lemFuel
  (<measure>) xs`), so `f` is fuel-free for its callers and the kernel
  computes through it; the backend emits the per-function sufficiency
  obligation (`f_measure_sufficient`: worker = wrapper at every fuel at
  or above the measure) whose proof you write in
  `<Module>_lemMeasureProofs.lean` — a missing or mistyped theorem fails
  the build, and a `sorry` fails the suite's token gate. When the measure
  is sufficient only on well-formed inputs (an acyclic tag environment, a
  basis `2 ≤ b`), add ``assuming `H` `` — a Lean Prop over the same
  parameters: the wrapper is unchanged, the obligation gains `H` as the
  binder `lemHyp` right before `lemFuel` (`H → μ ≤ fuel → worker =
  wrapper`), and outside `H` the wrapper may exhaust — loudly. The measure may
  be the backend-DERIVED structural size of an argument's type (`lemSize
  x`): every recursive block of generated inductives gets a computable
  `t.lemSize : t → Nat` in its own module, so a function recursing on a
  type defined beside it (an `Eq` instance's equality, say) is measurable
  without any hand-written Lean. A definition whose head binds fewer
  parameters than its type has arrows (a trailing lambda in the clause
  body — typically a trailing `function`: `let rec f acc = function | []
  -> … | x :: xs -> f … xs`, whose recursion argument is the anonymous
  scrutinee) is NOT rewritten in the `.lem`: when it carries
  `fuel_measure` or `structural`, the Lean emission alone hoists EVERY
  trailing variable-binder lambda of the clause body into the head — a
  `function`'s scrutinee as the deterministic binder `lemTail` (name it
  in the measure: ``fuel_measure val f = `List.length lemTail + 1` ``), a
  user-written `fun k ->` under the user's name `k` (with or without a
  `function` beneath it), through the single-arm match lem's pattern
  compiler makes for a destructuring parameter — so the measure and the
  structural analysis see named parameters, and the generated `f` takes
  them as explicit arguments; the fuel sentinel, written at the head's
  original function-typed codomain, is applied to the hoisted binders.
  Refused if `lemTail` (or a hoisted user binder) would shadow a
  parameter or be captured, and if any constant the body references
  renders on Lean as a reserved synthesized name (`lemFuel`,
  `lemMeasureLe`, `LemFuel`, `lemTail`, `_lemReader_*`, `_lemSupply*` —
  a Lean `target_rep` spelled that way would be captured silently; the
  same check runs for every fuel'd/reader/supply definition). The OCaml
  output is untouched. An inductive relation whose premise
  reaches the fuel takes `[LemFuel]` as an inductive parameter.
  Cerberus applies fuel declares across its whole execution path and
  checks that this part is total in its own build.
- **Zero axioms; effects are explicit state.** The shipped runtime declares no axioms, and the backend adds no
  axiom declarations. A downstream proof still requires an axiom audit
  of its hand-written imports and target representations. Ambient counters are
  threaded as explicit state ("supply lifting": a definition marked
  ``declare {lean} supply val`` takes and returns the counter; draws
  are `LemLib.supplySplit`, a plain def), and ambient configuration
  is threaded as an explicit parameter ("reader lifting"). An earlier
  design had a library axiom (`declare {lean} effectful`) projecting
  `BaseIO` externs into pure types; it is gone, and the backend now
  rejects that annotation at generation time, naming supply lifting
  as the replacement (the note at the top of `lean-lib/LemLib.lean`
  records the change).
- **Derived instances are real and OCaml-compatible.** `BEq`/`Ord`
  are derived structurally per mutual block with OCaml polymorphic
  compare parity; `Inhabited` is derived fail-closed (bounded,
  per-constructor); instance priorities come from one normative
  table so resolution is deliberate, not declaration-order luck.
- **Unsupported forms are rejected, not approximated.** Set
  comprehensions with `IN`-bounded binders
  (`{ e | forall (e IN s) | P e }`) are macro-expanded to folds and
  compile like any other code; the forms that survive expansion — the
  unbounded `{ x | condition }`, and binder shapes the expansion
  cannot handle — are a generation-time error with rewrite
  suggestions, never a silent stub. The other unsupported corners
  follow the same pattern — see the negative suite in
  `tests/comprehensive/negative/`.

## Known limits

The parity suite has ten registered expected failures
(`tests/comprehensive/parity/expected_failures.txt`; the runner pins the
exact Lean output of each):
- awaiting a planned fix: `p_str_bytes` and `p_str_escapes`, OCaml byte
  strings versus Lean Unicode strings (TODO item 31);
- ruled OCaml-target deviations, where Lean follows Lem's own semantics:
  `f_int_of_big_num`, `f_int32_overflow`, `p_mword_width`,
  `p_word_bitwise_wide`, `p_word_bitwise_wide_mul` (see DESIGN.md);
- open discrepancies awaiting an operator decision: `f_let_float_branch`
  and `f_let_float_closure` (Lean's compiler moves a `let` whose value
  fails into a branch or closure that never runs, so the failure is lost;
  TODO item 24), and `p_fn_compare_same_closure` (OCaml's `compare` on one
  closure object returns 0, Lean fails; TODO item 32).

Failure tests compare reached
failures under `LEAN_ABORT_ON_PANIC=1`; unused pure failures can be erased.
Finite tests and local Pset/Pmap laws are not a general OCaml–Lean
correspondence theorem. The runtime translations retain their source
notices and license terms: [NOTICE](../../lean-lib/NOTICE.md).

Lem theorems and lemmas are not translated: each leaves a
`/- lem: theorem NAME not translated -/` marker, without its statement
(TODO item 29); Lem assertions become build-time evaluation checks.
Comments before `and` in a recursive function group are lost (TODO item
26). A comparison demanded at a function type is a Lean build error,
where OCaml compiles and raises only if a closure is reached
([linksem findings](2026-09-28_linksem-findings.md), "Comparison at a
function type").

General fuel-completion monotonicity and propagation are **not proved by
the backend** (TODO item 13). A per-function `fuel_measure` obligation
proves stability above the measure, optionally under a stated hypothesis;
it does not by itself prove that execution avoids the exhaustion result.
Default recursion remains `partial`. Reader seeding affects call sites
inside the seed definition; it cannot re-seed a closure built outside that
extent. Seed arguments are positional in globally sorted reader order;
same-typed swaps need value tests (see DESIGN).

## How you check it

- `cd tests/comprehensive && make lean` — generation over the test
  corpus, compilation of everything generated against LemLib, a
  pinned panic-path check (a reached panic aborts under
  `LEAN_ABORT_ON_PANIC=1`; the suite also checks default-return behavior without it), and a negative suite (programs the
  backend must *reject*, rejected for the declared reason).
- `cd lean-lib && ../scripts/capped lake build` — the runtime plus `LemLibTest.lean`
  (property tests for the set/map layers, including adversarial-key
  comparator coherence).
- `grep -rn "^axiom " lean-lib/ --include="*.lean"` — zero hits;
  `#print axioms` on any downstream theorem shows what its proof
  actually rests on.
- Downstream, cerberus-lean's differential lanes are this backend's
  largest consumer test.

## Status

The backend generates Cerberus's selected Lean model, linksem's model
(96 modules) and the comprehensive suite. The consumer Cerberus has a
declared sequential execution profile, concurrency stubs, native
boundaries and explicit exclusions; this is not support for every Cerberus
model or C program.

Open work is registered in [TODO.md](TODO.md). The larger items are: the
failure-monad translation, which would make strictness and evaluation
order part of the generated semantics and remove the temporary
`lemSeqImpl` native seam (item 24); strings as bytes (item 31);
consolidating the Lean-only declares before a stable release (item 18);
and general fuel monotonicity (item 13). Emission uses one module-level
mutable state (`St` in `src/lean_backend.ml`) with per-lifetime reset
hooks (item 6).

Upstreaming intent: every extension is written to be plausibly
acceptable to rems-project/lem (no fork-only hacks in the core). Draft
reports of upstream Lem defects found along the way, each with a
reproducer run on pristine upstream `3802cb0`, are in
[`doc/upstream-tray/`](../upstream-tray/) (start with its README); nothing
has been filed (TODO item 30). Cerberus and linksem keep their own earlier
Lem drafts in their `upstream-tray/lem/` directories.

Pointers:
- [DESIGN.md](DESIGN.md): how the backend works and why.
- [TODO.md](TODO.md): the open-work register.
- [RECORDS.md](RECORDS.md): index of the dated records (history, rulings,
  measurements).
- [`doc/manual/backend_lean.md`](../manual/backend_lean.md): the
  upstream-facing manual chapter.
- `src/lean_backend.ml`: the backend; `lean-lib/`: the runtime.

Defects in this backend are recorded as dated records in
`doc/lean-backend/`, with reproducers in `tests/comprehensive/`.
