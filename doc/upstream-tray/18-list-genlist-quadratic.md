# 18 — OCaml: `List.genlist` takes time quadratic in the length (it is built with `snoc`)

Target: `rems-project/lem`, `library/list.lem` (the OCaml library module
`Lem_list` is generated from it). State: **Draft**, not filed. Drafted
2026-10-03.

## Affected code (upstream `3802cb0`)

`library/list.lem:566-575`:

```lem
(* [genlist f n] generates the list [f 1; ... (f (n-1))] *)
val genlist : forall 'a. (nat -> 'a) -> nat -> list 'a


let rec genlist f (n : nat) =
  match (n : nat) with
    | (0:nat) -> []
    | n' + 1 -> snoc (f n') (genlist f n')
  end
declare termination_argument genlist = automatic
```

`snoc e l = l ++ [e]` (`:206-207`), so building a list of length `n` costs
O(n^2). HOL4 and Isabelle have target representations (`:584-585`, `GENLIST`
and `genlist`); OCaml and Coq use the definition. (The comment's
`[f 1; …]` is also off by one: the asserts at `:577-580` give
`genlist (fun n -> n) 3 = [0;1;2]`.) lem-lean's `list.lem` has the same
definition at lines 584-593 (its OCaml side is unchanged).

## Classification

**TRUE BUG** (performance). The result is correct; the cost is quadratic
where a linear implementation is standard (`List.init`).

## Reproducer

```lem
open import Pervasives

let gl (n : nat) : nat = length (genlist (fun i -> i) n)
```

Driver (`repro/genlist/main.ml`) times `gl n` with `Sys.time` for `n` =
5000, 10000, 20000, 40000.

## Verbatim output

Captured 2026-10-03, upstream Lem `3802cb0` (`lem -v`: `Lem 3802cb0`),
upstream `ocaml-lib` compiled from the same checkout, OCaml 5.4.0;
conventions in README §4. Full transcript
(`repro/genlist/transcript-2026-10-03.txt`):

```
$ lem -wl ign -ocaml genlist.lem
[lem exit 0]
$ ocamlfind ocamlopt -package zarith -linkpkg -I <upstream ocaml-lib> extract.cmxa genlist.ml main.ml -o genlist.exe
[ocamlopt exit 0]
$ ./genlist.exe
genlist n=  5000  length=  5000  cpu=0.05s
genlist n= 10000  length= 10000  cpu=0.25s
genlist n= 20000  length= 20000  cpu=1.77s
genlist n= 40000  length= 40000  cpu=12.95s
[run exit 0]
```

## Observed vs expected

Observed: each doubling of `n` multiplies the CPU time by 5 to 7.3
(derived from the four lines above; a quadratic algorithm gives 4, and the
extra factor is plausibly allocation and GC from copying the list on every
step). Expected: roughly linear, as `List.init`.

## Impact

`genlist` is unusable on OCaml beyond some tens of thousands of elements
(40 000 elements took 12.95 s of CPU here). The lem-lean noodle probes recorded that
a 300 000-element `genlist` did not finish in 10 s.

## Proposed remedy

``declare ocaml target_rep function genlist f n = `List.init` n f`` (the
argument order of `List.init` is length first), keeping the definition
for the provers; or build the list in reverse and reverse once. Also fix
the comment to `[f 0; ... f (n-1)]`.

## Origin

lem-lean `doc/lean-backend/TODO.md` item 7 ("Quadratic library functions
(performance only, no behavioural divergence)": "`List.genlist` on the
OCaml target is the lem definition `snoc (f n') (genlist f n')` …
quadratic … a 300 000-element `genlist` did not finish in 10 s on OCaml in
the noodle bisect … give OCaml `genlist` a `List.init` rep (upstream lem,
non-Lean change)"); `doc/lean-backend/2026-09-03_parity-fix-record.md`
§F9; the noodle record `2026-09-03_noodle-backend.md` (lem-lean commit
`a02cb6f`, not on mainline). These are [AGENT] records; the tray scope is
the [USER 2026-10-03] ruling (all 16 findings, re-verified).

## Provenance

Found and analysed by AI agents (Claude, Anthropic) working under the
direction and review of a human operator. Any filed issue must say so
(INDEX.md, "Provenance labelling").
