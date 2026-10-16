# 23 — Comments before `and` in a `let rec … and …` group are dropped by the Coq backend, and by Isabelle (and HOL4 with `-hol_remove_matches`) when clauses are regrouped; regrouping also reorders the clauses

Target: `rems-project/lem`, `src/coq_backend.ml` and `src/patterns.ml`
(`remove_toplevel_match`). State: **Draft**, not filed. Drafted
2026-10-03.

## Affected code (upstream `3802cb0`)

Two independent mechanisms; the reproducers separate them.

1. **Coq, always.** `src/coq_backend.ml:582-607`, the `Fun_def` arm:
   `let funcls = Seplist.to_list funcl_skips_seplist in` (`:601`) drops
   the separators (the `and` tokens with their preceding whitespace and
   comments), and the bodies are rejoined with
   `concat_str "\nwith" bodies` (`:603`). Every comment between clauses is
   lost, whatever the clause bodies are.
2. **Isabelle always, HOL4 under `-hol_remove_matches`, only when a
   clause body is a top-level `match` that gets lifted into equations.**
   `Patterns.remove_toplevel_match` (`src/patterns.ml:1912-1950`; enabled
   for Isabelle at `src/target_trans.ml:270`, for HOL4 at `:161-163` only
   if `hol_remove_matches` is set) regroups the clauses with
   `Typed_ast.funcl_aux_seplist_group` (`src/typed_ast.ml:2557-2578`),
   which pairs each clause with the separator that follows it and, when
   the clause names are not already in sorted order, re-sorts them by name
   (`List.stable_sort`, `:2564`). The rebuilt list takes fresh separators:
   `new_line` between the equations made from one clause (`:1935`) and
   `space` between groups (`Seplist.flatten space sll'`, `:1941`). The
   original separators, which hold the comments, are not used.

OCaml, and HOL4 without the flag, print the original separators and keep
every comment. The cited code is identical in lem-lean: `src/coq_backend.ml` is
unchanged, and its diffs to `src/patterns.ml` and `src/typed_ast.ml` only
add Lean-specific functions.

## Classification

**TRUE BUG** (output fidelity, minor). Comments are user text that every
other construct carries into every backend; here they disappear on some
backends and not others, without a warning. The reordering under (2) is
**cosmetic** for the prover output we checked (clauses of one function
keep their relative order; the order between different functions of a
`function`/`Hol_multi_defns` group does not change their meaning), but it
moves clauses away from their source position.

## Reproducers

`test_and.lem` (from the orchestrator's report; names not in sorted
order, bodies are top-level matches):

```lem
open import Pervasives
type t = A | B of nat
(* before f *)
let rec f (x : t) : nat = match x with A -> 0 | B n -> g n end
(* before g *)
and g (n : nat) : nat = match n with 0 -> 1 | _ -> f (B (n - 1)) end
(* before a *)
and a (x : t) : nat = match x with A -> 1 | B n -> f (B n) end
```

Three variants (in `repro/andsep/`): `test_nomatch.lem` (same names, `if`
bodies, so nothing is lifted), `test_order.lem` (`zeta`, `mid`, `beta`:
reverse alphabetical source order, all matches) and `test_sorted.lem`
(`alpha`, `beta`, `gamma`: sorted source order, all matches).

## Verbatim output

Captured 2026-10-03, upstream Lem `3802cb0` (`lem -v`: `Lem 3802cb0`);
conventions in README §4. Each file was generated with `-ocaml`, `-coq`,
`-hol`, `-isa` and `-hol -hol_remove_matches` (all exit 0). Excerpts of
`repro/andsep/transcript-2026-10-03.txt` follow.

`test_and`, OCaml (all three comments):

```
=== test_and: OCaml
4:(* before f *)
5:let rec f (x : t) : int=  ((match x with A -> 0 | B n -> g n ))
6:(* before g *)
7:and g (n : int) : int=  ((match n with 0 -> 1 | _ -> f (B ( Nat_num.nat_monus n 1)) ))
8:(* before a *)
9:and a (x : t) : int=  ((match x with A -> 1 | B n -> f (B n) ))
```

`test_and`, Coq (only the comment before `let rec`):

```
=== test_and: Coq
19:(* before f *)
20:Program Fixpoint f   (x : t )   :  nat :=  match ( x) with  A => 0%nat | B n => g n end
21:with g   (n : nat )   :  nat :=  match ( n) with  0%nat => 1%nat | _ => f (B ( Coq.Init.Peano.minus n( 1%nat))) end
22:with a   (x : t )   :  nat :=  match ( x) with  A => 1%nat | B n => f (B n) end.
```

`test_and`, HOL4 default (all three) and with `-hol_remove_matches` (one,
and the clauses in the order `g`, `f`, `a`):

```
=== test_and: HOL4
(* before f *)
 val f_defn = Defn.Hol_multi_defns `
 ((f:t -> num) (x : t) : num=  ((case x of A =>( 0 : num) | B n => g n )))
(* before g *)
/\ ((g:num -> num) (n : num) : num=  ((case n of 0 =>( 1 : num) | _ => f (B (n -( 1 : num))) )))
(* before a *)
/\ ((a:t -> num) (x : t) : num=  ((case x of A =>( 1 : num) | B n => f (B n) )))`;

val _ = Lib.with_flag (computeLib.auto_import_definitions, false) (List.map Defn.save_defn) f_defn;
=== test_and: HOL4 -hol_remove_matches
(* before f *)
 val g_defn = Defn.Hol_multi_defns `
 ((g:num -> num) (n : num) : num=  ((case n of 0 =>( 1 : num) | _ => f (B (n -( 1 : num))) ))) /\ ((f:t -> num) (A : t) : num= (( 0 : num)))
/\ ((f:t -> num) ((B n) : t) : num=  (g n)) /\ ((a:t -> num) (A : t) : num= (( 1 : num)))
/\ ((a:t -> num) ((B n) : t) : num=  (f (B n)))`;
```

`test_and`, Isabelle (one comment; equations in the order `g`, `f`, `a`):

```
=== test_and: Isabelle
\<comment> \<open>\<open> before f \<close>\<close>
function (sequential,domintros)  a  :: \<open> t \<Rightarrow> nat \<close>  
                   and f  :: \<open> t \<Rightarrow> nat \<close>  
                   and g  :: \<open> nat \<Rightarrow> nat \<close>  where 
     \<open> g (n :: nat) = ( (case  n of 0 =>( 1 :: nat) | _ => f (B (n -( 1 :: nat))) ))\<close> 
  for  "n"  :: " nat " |\<open> f (A :: t) = (( 0 :: nat))\<close>
|\<open> f ((B n) :: t) = ( g n )\<close> 
  for  "n"  :: " nat " |\<open> a (A :: t) = (( 1 :: nat))\<close>
|\<open> a ((B n) :: t) = ( f (B n))\<close> 
  for  "n"  :: " nat " 
by pat_completeness auto
```

`test_nomatch` (nothing lifted): Isabelle keeps all three comments, Coq
still keeps only the first:

```
=== test_nomatch: Coq
17:(* before f *)
18:Program Fixpoint f   (x : nat )   :  nat :=  if beq_nat x( 0%nat) then 0%nat else g ( Coq.Init.Peano.minus x( 1%nat))
19:with g   (n : nat )   :  nat :=  if beq_nat n( 0%nat) then 1%nat else f ( Coq.Init.Peano.minus n( 1%nat))
20:with a   (x : nat )   :  nat :=  if beq_nat x( 0%nat) then 1%nat else f x.
```

```
=== test_nomatch: Isabelle
\<comment> \<open>\<open> before f \<close>\<close>
function (sequential,domintros)  a  :: \<open> nat \<Rightarrow> nat \<close>  
                   and g  :: \<open> nat \<Rightarrow> nat \<close>  
                   and f  :: \<open> nat \<Rightarrow> nat \<close>  where 
     \<open> f (x :: nat) = ( if x =( 0 :: nat) then( 0 :: nat) else g (x -( 1 :: nat)))\<close> 
  for  "x"  :: " nat "
\<comment> \<open>\<open> before g \<close>\<close>
|\<open> g (n :: nat) = ( if n =( 0 :: nat) then( 1 :: nat) else f (n -( 1 :: nat)))\<close> 
  for  "n"  :: " nat "
\<comment> \<open>\<open> before a \<close>\<close>
|\<open> a (x :: nat) = ( if x =( 0 :: nat) then( 1 :: nat) else f x )\<close> 
  for  "x"  :: " nat " 
by pat_completeness auto
```

Clause order when everything is lifted. Source `zeta`, `mid`, `beta`
(`test_order`) and source `alpha`, `beta`, `gamma` (`test_sorted`), both
Isabelle:

```
=== test_order: Isabelle
\<comment> \<open>\<open> before zeta \<close>\<close>
function (sequential,domintros)  beta  :: \<open> t \<Rightarrow> nat \<close>  
                   and mid  :: \<open> t \<Rightarrow> nat \<close>  
                   and zeta  :: \<open> t \<Rightarrow> nat \<close>  where 
     \<open> zeta (A :: t) = (( 0 :: nat))\<close>
|\<open> zeta ((B n) :: t) = ( mid (B n))\<close> 
  for  "n"  :: " nat " |\<open> mid (A :: t) = (( 1 :: nat))\<close>
|\<open> mid ((B n) :: t) = ( beta (B n))\<close> 
  for  "n"  :: " nat " |\<open> beta (A :: t) = (( 2 :: nat))\<close>
|\<open> beta ((B n) :: t) = ( zeta A )\<close> 
  for  "n"  :: " nat " 
by pat_completeness auto
```

```
=== test_sorted: Isabelle
\<comment> \<open>\<open> before alpha \<close>\<close>
function (sequential,domintros)  gamma  :: \<open> t \<Rightarrow> nat \<close>  
                   and beta  :: \<open> t \<Rightarrow> nat \<close>  
                   and alpha  :: \<open> t \<Rightarrow> nat \<close>  where 
     \<open> alpha (A :: t) = (( 0 :: nat))\<close>
|\<open> alpha ((B n) :: t) = ( beta (B n))\<close> 
  for  "n"  :: " nat " |\<open> beta (A :: t) = (( 1 :: nat))\<close>
|\<open> beta ((B n) :: t) = ( gamma (B n))\<close> 
  for  "n"  :: " nat " |\<open> gamma (A :: t) = (( 2 :: nat))\<close>
|\<open> gamma ((B n) :: t) = ( alpha A )\<close> 
  for  "n"  :: " nat " 
by pat_completeness auto
```

HOL4 with `-hol_remove_matches` gives the same orders (`zeta`, `mid`,
`beta` and `alpha`, `beta`, `gamma`; full transcript).

## Observed vs expected

| Input | OCaml | HOL4 | HOL4 `-hol_remove_matches` | Isabelle | Coq |
|---|---|---|---|---|---|
| `test_and` (matches) | 3 of 3 comments | 3 | 1; order g, f, a | 1; order g, f, a | 1 |
| `test_nomatch` (no lifting) | 3 | 3 | 3 | 3 | 1 |
| `test_order` (zeta, mid, beta) | 3 | 3 | 1; order kept | 1; order kept | 1 |
| `test_sorted` (alpha, beta, gamma) | 3 | 3 | 1; order kept | 1; order kept | 1 |

Expected: all comments on every backend, clauses in source order.

On order (derived from the three lifted cases): when the source names are
already sorted the order is kept; when they are not, the output is in
descending name order (`g, f, a` for source `f, g, a`; `zeta, mid, beta`
for source `zeta, mid, beta`, which happens to be descending already).
Where exactly the descending order comes from after
`funcl_aux_seplist_group`'s ascending sort was not traced. Only the
"comments dropped" part reproduces the orchestrator's report; its
attribution of the Coq loss to `remove_toplevel_match` does not hold
(that pass is not in the Coq pipeline, and Coq drops the comments without
it, `test_nomatch`).

## Impact

Documentation written next to mutually recursive definitions (often the
most important definitions in a model) is silently missing from Coq
output, and from Isabelle output whenever Lem lifts a match into
equations. Equation order changes make generated Isabelle/HOL4 harder to
compare with the source.

## Proposed remedy

1. Coq: print with the separators, e.g. `Seplist.to_sep_list` (as the
   type-definition printer does at `src/coq_backend.ml:1261`), emitting
   each separator's skips followed by `with`.
2. `remove_toplevel_match`: keep the separator that preceded each original
   clause and use it in front of the first equation generated from that
   clause (only the separators *between* equations of one clause need to
   be fresh), instead of `space`/`new_line`. `funcl_aux_seplist_group`
   already has each clause's separator in hand (`Seplist.to_pair_list`).
3. Regrouping: if the sort is needed for grouping clauses of the same
   name, restore source order of the groups afterwards (order of first
   occurrence) instead of emitting them sorted.

## Origin

Found by the lem-lean orchestrator on 2026-10-03 while working on the
fork's output-readability arc (comments lost in generated Lean output);
reported to this slice with the `test_and.lem` reproducer, the
`remove_toplevel_match` mechanism and the request to check HOL4,
Isabelle and clause order. The fork-side consequence (its Lean pipeline
also shares the rebuilt separators) is not part of this upstream report.
The Coq mechanism, the `test_nomatch`/`test_order`/`test_sorted` variants
and the `-hol_remove_matches` runs are this tray's [AGENT] additions.

## Provenance

Found and analysed by AI agents (Claude, Anthropic) working under the
direction and review of a human operator. Any filed issue must say so
(INDEX.md, "Provenance labelling").
