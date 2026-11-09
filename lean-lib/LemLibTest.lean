import LemLib
import Lean
/-!
# LemLibTest — property tests for the `Pset`/`Pmap` ports

Under the [USER 2026-09-03] zero-discrepancy ruling the set and map
representations are Lean translations of lem's OCaml runtime AVL trees
(ocaml-lib/pset.ml, pmap.ml; see the LemLib.lean section header), whose
specification is the OCaml code itself. The load-bearing evidence is
therefore the TWO-TARGET parity suite (tests/comprehensive/parity/,
probes p_set_ops / p_map_ops / p_map_beq / p_cmp_order / p_show: an
OCaml binary and a Lean binary built from the same lem source, outputs
byte-identical). This file keeps the Lean-internal sanity net that a
parity run cannot express: the AVL representation invariants after
bounded-exhaustive operation sequences (with adversarial keys whose
derived BEq is finer than the comparator), and a handful of
kernel-checked examples of the OCaml-specific observables the port
exists to reproduce. Building it IS running it: every `#guard` is
evaluated at elaboration time and a false one fails the build.
-/

namespace LemLibTest

/-! ## Adversarial key: derived BEq finer than the comparator -/

structure K2 where
  a : Nat
  b : Nat
  deriving DecidableEq, Repr, Inhabited

/-- Comparator on the first component only: `⟨0,0⟩ ~ ⟨0,1⟩`. -/
def cK2 : K2 → K2 → LemOrdering := fun x y => defaultCompare x.a y.a
def cNat : Nat → Nat → LemOrdering := defaultCompare

/-! ## Representation invariants (pset.ml's documented ones) -/

/-- Heights consistent and AVL-balanced (children differ by at most 2,
    as the OCaml comment states). -/
def Pset.wellFormed : Pset α → Bool
  | .Empty => true
  | .Node l _ r h =>
    let hl := Pset.height l
    let hr := Pset.height r
    h == (if hl >= hr then hl + 1 else hr + 1) && (hl + 2 >= hr) && (hr + 2 >= hl) &&
    Pset.wellFormed l && Pset.wellFormed r

/-- Strictly ascending in-order traversal (no comparator-EQ duplicates). -/
def strictlyAscending (cmp : α → α → LemOrdering) : List α → Bool
  | [] | [_] => true
  | x :: y :: rest => (match cmp x y with | .LT => true | _ => false) && strictlyAscending cmp (y :: rest)

def Pmap.wellFormed : Pmap α β → Bool
  | .Empty => true
  | .Node l _ _ r h =>
    let hl := Pmap.height l
    let hr := Pmap.height r
    h == (if hl >= hr then hl + 1 else hr + 1) && (hl + 2 >= hr) && (hr + 2 >= hl) &&
    Pmap.wellFormed l && Pmap.wellFormed r

/-! ## Bounded-exhaustive operation sequences -/

inductive SOp (α : Type) where
  | add (x : α)
  | remove (x : α)
  | unionWith (l : List α)
  | interWith (l : List α)
  | diffWith (l : List α)
  | filterEven

def applySOp (cmp : K2 → K2 → LemOrdering) (s : Pset K2) : SOp K2 → Pset K2
  | .add x => Pset.add cmp x s
  | .remove x => Pset.remove cmp x s
  | .unionWith l => Pset.union cmp s (Pset.fromList cmp l)
  | .interWith l => Pset.inter cmp s (Pset.fromList cmp l)
  | .diffWith l => Pset.diff cmp s (Pset.fromList cmp l)
  | .filterEven => Pset.filter cmp (fun k => k.a % 2 == 0) s

def pool : List K2 := [⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨2, 0⟩, ⟨3, 1⟩, ⟨4, 0⟩, ⟨5, 0⟩, ⟨6, 1⟩]

def opChoices : List (SOp K2) :=
  (pool.map SOp.add) ++ (pool.map SOp.remove) ++
  [SOp.unionWith [⟨1, 1⟩, ⟨7, 0⟩, ⟨0, 1⟩], SOp.interWith [⟨0, 1⟩, ⟨2, 1⟩, ⟨5, 5⟩],
   SOp.diffWith [⟨1, 0⟩, ⟨4, 4⟩], SOp.filterEven]

/-- All sequences of exactly `n` ops (|opChoices|^n of them). -/
def seqs : Nat → List (List (SOp K2))
  | 0 => [[]]
  | n + 1 => (seqs n).flatMap fun s => opChoices.map fun o => o :: s

def runSeq (s : List (SOp K2)) : Pset K2 := s.foldl (applySOp cK2) .Empty

/-- Invariant check over every sequence: well-formed, strictly ascending
    elements, cardinal = length of elements, membership agrees with the
    element list, and equality with itself. -/
def setInvariantsHold (s : Pset K2) : Bool :=
  let es := Pset.elements s
  Pset.wellFormed s && strictlyAscending cK2 es && Pset.cardinal s == es.length &&
  pool.all (fun k => Pset.mem cK2 k s == es.any (fun e => match cK2 e k with | .EQ => true | _ => false)) &&
  Pset.equal cK2 s s && Pset.subset cK2 s s

#guard (seqs 3).all (fun ops => setInvariantsHold (runSeq ops))   -- 20^3 = 8000 sequences

/-! ## Map invariants over op sequences -/

inductive MOp where
  | add (k : K2) (v : Nat)
  | remove (k : K2)
  | unionWith (l : List (K2 × Nat))

def applyMOp (m : Pmap K2 Nat) : MOp → Pmap K2 Nat
  | .add k v => Pmap.add cK2 k v m
  | .remove k => Pmap.remove cK2 k m
  | .unionWith l => Pmap.union cK2 m (l.foldl (fun acc (k, v) => Pmap.add cK2 k v acc) .Empty)

def mopChoices : List MOp :=
  (pool.map fun k => MOp.add k k.b) ++ (pool.map MOp.remove) ++
  [MOp.unionWith [(⟨1, 1⟩, 9), (⟨7, 0⟩, 8)], MOp.unionWith [(⟨0, 1⟩, 7)]]

def mseqs : Nat → List (List MOp)
  | 0 => [[]]
  | n + 1 => (mseqs n).flatMap fun s => mopChoices.map fun o => o :: s

def mapInvariantsHold (m : Pmap K2 Nat) : Bool :=
  let bs := Pmap.bindings m
  Pmap.wellFormed m && strictlyAscending cK2 (bs.map Prod.fst) && Pmap.cardinal m == bs.length &&
  pool.all (fun k => (Pmap.find? cK2 k m).isSome == bs.any (fun (k', _) => match cK2 k' k with | .EQ => true | _ => false)) &&
  Pmap.equal cK2 (fun a b => a == b) m m

#guard (mseqs 3).all (fun ops => mapInvariantsHold (ops.foldl applyMOp .Empty))   -- 18^3 = 5832 sequences

/-! ## Kernel-checked examples of the OCaml observables the port reproduces -/

/-- Pmap.add REPLACES a comparator-equal binding — new key and new value
    (pmap.ml:67-73; the parity probe p_map_beq shape). -/
example : Pmap.bindings (Pmap.add cK2 ⟨1, 0⟩ 1 (Pmap.add cK2 ⟨1, 1⟩ 2 .Empty)) = [(⟨1, 0⟩, 1)] := by decide

/-- Pset.add keeps the FIRST comparator-equal element (pset.ml:76-80). -/
example : Pset.elements (Pset.add cK2 ⟨1, 0⟩ (Pset.add cK2 ⟨1, 1⟩ .Empty)) = [⟨1, 1⟩] := by decide

/-- Iteration is ascending by the comparator, whatever the insertion order. -/
example : Pset.elements (Pset.fromList cNat [3, 1, 2]) = [1, 2, 3] := by decide
example : Pmap.bindings ((Pmap.add cNat 3 "c" (Pmap.add cNat 1 "a" (Pmap.add cNat 2 "b" .Empty)))) =
    [(1, "a"), (2, "b"), (3, "c")] := by decide

/-- `fold` is ascending (pset.ml:254): folding cons yields the reversed list. -/
example : Pset.fold (fun x acc => x :: acc) (Pset.fromList cNat [2, 3, 1]) [] = [3, 2, 1] := by decide

/-- Pmap.equal compares keys with the map's comparator and IGNORES lem's
    key equality (pmap.ml:253-261, 296). -/
example : fmapEqualBy (fun (a b : K2) => a == b) (fun a b => a == b)
    (fmapAddBy cK2 ⟨1, 0⟩ 1 fmapEmpty) (fmapAddBy cK2 ⟨1, 1⟩ 1 fmapEmpty) = true := by decide

/-- set_case sees a singleton by its exact shape (pset.ml:360). -/
example : Pset.setCase (Pset.fromList cNat [5]) "e" (fun _ => "s") "m" = "s" := by decide
example : Pset.setCase (Pset.fromList cNat [5, 6]) "e" (fun _ => "s") "m" = "m" := by decide

/-! ## Kernel computability through `join`
    `Pset.join`/`Pmap.join` are height-indexed structural recursions (they
    were well-founded, which the kernel cannot unfold — the consumer
    measured 17 closed-term `rfl` proofs blocked at `join`). Every closed
    term below reaches `join` (`union` → `unionGo` → `join`; `concat`;
    `Pmap.merge`/`union`; `remove` reaches `bal`/`merge`) and is decided by
    the KERNEL (`decide`), not by evaluation. -/
example : Pset.elements (Pset.union cNat (Pset.fromList cNat [1, 2, 3, 9]) (Pset.fromList cNat [3, 4, 5, 6, 7, 8])) =
    [1, 2, 3, 4, 5, 6, 7, 8, 9] := by decide
example : Pset.elements (Pset.inter cNat (Pset.fromList cNat [1, 2, 3, 4, 5]) (Pset.fromList cNat [4, 5, 6, 7])) =
    [4, 5] := by decide
example : Pset.elements (Pset.diff cNat (Pset.fromList cNat [1, 2, 3, 4, 5]) (Pset.fromList cNat [2, 4])) =
    [1, 3, 5] := by decide
example : Pset.elements (Pset.remove cNat 3 (Pset.fromList cNat [1, 2, 3, 4, 5, 6, 7])) = [1, 2, 4, 5, 6, 7] := by decide
example : Pset.heightsOk (Pset.union cNat (Pset.fromList cNat [1, 2, 3, 9]) (Pset.fromList cNat [3, 4, 5, 6, 7, 8])) = true := by decide
def pmapOf (l : List (Nat × String)) : Pmap Nat String := l.foldl (fun m (k, v) => Pmap.add cNat k v m) .Empty
example : Pmap.bindings (Pmap.union cNat (pmapOf [(1, "a"), (2, "b"), (5, "e")]) (pmapOf [(2, "B"), (3, "c"), (4, "d")])) =
    [(1, "a"), (2, "B"), (3, "c"), (4, "d"), (5, "e")] := by decide
example : Pmap.bindings (Pmap.remove cNat 2 (pmapOf [(1, "a"), (2, "b"), (3, "c"), (4, "d")])) =
    [(1, "a"), (3, "c"), (4, "d")] := by decide
example : fmapElements (fmapUnionBy cNat (fmapAddBy cNat 1 10 (fmapAddBy cNat 3 30 fmapEmpty))
    (fmapAddBy cNat 2 20 (fmapAddBy cNat 4 40 fmapEmpty))) = [(1, 10), (2, 20), (3, 30), (4, 40)] := by decide
example : fmapElements (fmapDeleteBy cNat 3 (fmapAddBy cNat 1 10 (fmapAddBy cNat 3 30 (fmapAddBy cNat 5 50 fmapEmpty)))) =
    [(1, 10), (5, 50)] := by decide

/-- `lean_box(0)` ABI: the empty set / map is the first nullary constructor. -/
example : (setEmpty : Pset Nat) = Pset.Empty := rfl
example : (fmapEmpty : Fmap Nat Nat) = Fmap.empty := rfl

/-- `Ord LemOrdering` is the OCaml int order LT(-1) < EQ(0) < GT(1), and
    a set of orderings built from it behaves as a set. -/
example : compare LemOrdering.LT LemOrdering.EQ = .lt := by decide
example : compare LemOrdering.GT LemOrdering.EQ = .gt := by decide
example : compare LemOrdering.EQ LemOrdering.EQ = .eq := by decide
example : Pset.elements (Pset.fromList (fun a b => defaultCompare a b)
    [LemOrdering.GT, .LT, .EQ, .LT]) = [.LT, .EQ, .GT] := by decide
example : Pset.mem (fun a b => defaultCompare a b) LemOrdering.EQ
    (Pset.fromList (fun a b => defaultCompare a b) [LemOrdering.LT, .EQ]) = true := by decide

/-- `lem_if` elaborates to the SAME kernel term as Lean's `if` on a
    Bool, nested and in both branches; so proofs about generated code see no
    difference. Checked on the elaborated definitions, not just by `rfl`. -/
def lemIfRef (b : Bool) (n : Nat) : Nat := if b then n + 1 else if !b then 7 else n
def lemIfNew (b : Bool) (n : Nat) : Nat := lem_if b then n + 1 else lem_if !b then 7 else n
open Lean Elab Command in
#eval show CommandElabM Unit from do
  let env ← getEnv
  unless (env.find? ``LemLibTest.lemIfRef).get!.value! == (env.find? ``LemLibTest.lemIfNew).get!.value! do
    throwError "lem_if does not elaborate to the builtin Bool `if` term"
example : lemIfNew true 3 = 4 := rfl
example : lemIfNew false 3 = 7 := rfl

/-- A ruled OCaml-target deviation ([USER 2026-09-30]): the unbounded Int
    bitwise reps agree with two's complement (the OCaml `land`/`lor`/`lxor`
    values), in every sign combination; bit lists are MSB-first;
    word_extract masks by hi. -/
example : lemIntLand (-6) 3 = 2 ∧ lemIntLand 6 (-3) = 4 ∧ lemIntLand (-6) (-3) = -8 ∧ lemIntLand 12 10 = 8 := by decide
example : lemIntLor (-6) 3 = -5 ∧ lemIntLor 6 (-3) = -1 ∧ lemIntLor (-6) (-3) = -1 ∧ lemIntLor 12 10 = 14 := by decide
example : lemIntLxor (-6) 3 = -7 ∧ lemIntLxor 6 (-3) = -5 ∧ lemIntLxor (-6) (-3) = 7 ∧ lemIntLxor 12 10 = 6 := by decide
example : lemIntLsl (-3) 4 = -48 ∧ lemIntAsr (-7) 1 = -4 ∧ lemIntAsr 7 1 = 3 := by decide
example : (mwordFromBitlist [false, false, true, false] : BitVec 4) = 2#4 := by decide
example : mwordToBitlist (2#4) = [false, false, true, false] := by decide
example : (mwordExtract 0 3 (0xAB#8) : BitVec 8) = 0xB#8 := by decide

end LemLibTest
