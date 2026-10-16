import LemLib
/-!
# LemLibPmapLaws — lookup-after-insert laws for the `Pmap` port

`Pmap` is the Lean translation of lem's `ocaml-lib/pmap.ml` AVL tree
(`LemLib.lean`, "Finite maps"). A consumer reasoning about a generated
environment (`Fmap sym value` = `Fmap.mk cmp (m : Pmap …)`) needs, for a
comparator that is a strict total order, that a lookup after an insert
finds the inserted value and leaves every other key's lookup unchanged.
Both are proved here against the port's own `add`/`find?`/`bal`/`create`,
once, for every consumer.

## Statements

    Pmap.find?_add_same  : CmpLaws cmp → WF cmp m → find? cmp k (add cmp k v m) = some v
    Pmap.find?_add_other : CmpLaws cmp → WF cmp m → cmp k k' ≠ .EQ →
                           find? cmp k (add cmp k' v m) = find? cmp k m
    Pmap.WF_Empty, Pmap.WF_add (the invariant `Empty` has and `add` preserves)

and the `Fmap` corollaries `fmapLookupBy_fmapAddBy_same` / `_other` under
`Fmap.WF cmp` (the captured comparator IS `cmp`, and the tree is `WF cmp`).

## The hypotheses — the minimal honest ones

`Pmap.WF cmp m` is the binary-search-tree ORDER invariant: the in-order
bindings `toList m` are strictly ascending under `cmp` (`List.Pairwise`).
The AVL heights play no role in these laws (rebalancing is a permutation-
free rewrite of the in-order list — `toList_bal`), so the invariant does
not mention them; `heightsOk` (LemLibTheorems, the `join` equality) is a
separate, independent invariant.

`Pmap.CmpLaws cmp` is a STRICT WEAK ORDER stated on the three-valued
comparator: `refl` (`cmp a a = EQ`), `flip` (`cmp b a` is the opposite of
`cmp a b`), `lt_trans`, and `eq_congr` (`cmp a b = EQ → cmp a c = cmp b c`:
comparator-equal keys compare alike against everything). This is weaker
than "`EQ` iff `=`": `Pmap.add` REPLACES a comparator-EQ binding storing
the new key (pmap.ml:67), so the laws hold — and are stated — up to the
comparator, not up to Lean equality, exactly as in OCaml's `Map` with a
total-preorder `compare`. Every law of a strict total order with
decidable equality (e.g. `defaultCompare` on `Nat`, `cmpLaws_defaultCompare_nat`
below) is an instance. `eq_congr` is independent of the other three (with
`refl`+`flip`+`lt_trans` alone, two `EQ` keys could still compare
differently against a third) and is what `find?` needs to skip a subtree.

Cones: every theorem here is closed under `propext`, `Classical.choice`
and `Quot.sound` at most — no `sorry`, no `native_decide`, no
`ofReduce*`; `#print axioms` at the end. Unit pins (`decide`/`rfl`
through `add`/`find?` on closed maps) close the file.
-/

namespace Pmap
variable {α β : Type}

/-- The strict-weak-order laws of a comparator, on its three values. -/
structure CmpLaws (cmp : α → α → LemOrdering) : Prop where
  refl : ∀ a, cmp a a = .EQ
  flip : ∀ a b, cmp b a = (match cmp a b with | .LT => .GT | .EQ => .EQ | .GT => .LT)
  lt_trans : ∀ a b c, cmp a b = .LT → cmp b c = .LT → cmp a c = .LT
  eq_congr : ∀ a b c, cmp a b = .EQ → cmp a c = cmp b c

namespace CmpLaws
variable {cmp : α → α → LemOrdering}

theorem lt_gt (h : CmpLaws cmp) {a b : α} (hab : cmp a b = .LT) : cmp b a = .GT := by
  rw [h.flip a b, hab]
theorem gt_lt (h : CmpLaws cmp) {a b : α} (hab : cmp a b = .GT) : cmp b a = .LT := by
  rw [h.flip a b, hab]
theorem eq_symm (h : CmpLaws cmp) {a b : α} (hab : cmp a b = .EQ) : cmp b a = .EQ := by
  rw [h.flip a b, hab]
theorem eq_congr_right (h : CmpLaws cmp) {a b c : α} (hab : cmp a b = .EQ) : cmp c a = cmp c b := by
  rw [h.flip a c, h.flip b c, h.eq_congr a b c hab]
theorem gt_trans (h : CmpLaws cmp) {a b c : α} (hab : cmp a b = .GT) (hbc : cmp b c = .GT) : cmp a c = .GT :=
  h.lt_gt (h.lt_trans c b a (h.gt_lt hbc) (h.gt_lt hab))
theorem lt_of_lt_of_eq (h : CmpLaws cmp) {a b c : α} (hab : cmp a b = .LT) (hbc : cmp b c = .EQ) : cmp a c = .LT := by
  rw [← h.eq_congr_right hbc]; exact hab
theorem lt_of_eq_of_lt (h : CmpLaws cmp) {a b c : α} (hab : cmp a b = .EQ) (hbc : cmp b c = .LT) : cmp a c = .LT := by
  rw [h.eq_congr a b c hab]; exact hbc
theorem gt_of_eq_of_gt (h : CmpLaws cmp) {a b c : α} (hab : cmp a b = .EQ) (hbc : cmp b c = .GT) : cmp a c = .GT := by
  rw [h.eq_congr a b c hab]; exact hbc
theorem gt_of_gt_of_eq (h : CmpLaws cmp) {a b c : α} (hab : cmp a b = .GT) (hbc : cmp b c = .EQ) : cmp a c = .GT := by
  rw [h.eq_congr_right (h.eq_symm hbc)]; exact hab
end CmpLaws

/-! ## In-order bindings, and the list-level spec of `find?` / `add` -/

/-- In-order bindings (the same list as `bindings`, without its accumulator). -/
def toList : Pmap α β → List (α × β)
  | .Empty => []
  | .Node l v d r _ => toList l ++ (v, d) :: toList r

/-- The first binding whose key is comparator-EQ to `k`. -/
def lookupList (cmp : α → α → LemOrdering) (k : α) : List (α × β) → Option β
  | [] => none
  | (k', v) :: rest => if cmp k k' = .EQ then some v else lookupList cmp k rest

/-- Sorted insert-or-replace (the in-order effect of `add`). -/
def insertList (cmp : α → α → LemOrdering) (k : α) (v : β) : List (α × β) → List (α × β)
  | [] => [(k, v)]
  | (k', v') :: rest => match cmp k k' with
    | .EQ => (k, v) :: rest
    | .LT => (k, v) :: (k', v') :: rest
    | .GT => (k', v') :: insertList cmp k v rest

/-- The order invariant: in-order keys strictly ascending under `cmp`. -/
def WF (cmp : α → α → LemOrdering) (m : Pmap α β) : Prop :=
  (toList m).Pairwise (fun a b => cmp a.1 b.1 = .LT)

instance (cmp : α → α → LemOrdering) (m : Pmap α β) : Decidable (WF cmp m) := by
  unfold WF; infer_instance

theorem WF_Empty (cmp : α → α → LemOrdering) : WF cmp (.Empty : Pmap α β) := by
  simp [WF, toList]

/-! ## `create` and `bal` are in-order-preserving (no hypothesis: the
    `failwithI "Map.bal"` arms sit under height tests that exclude them) -/

theorem toList_create (l : Pmap α β) (x : α) (d : β) (r : Pmap α β) :
    toList (create l x d r) = toList l ++ (x, d) :: toList r := by
  simp [create, toList]

theorem toList_bal (l : Pmap α β) (x : α) (d : β) (r : Pmap α β) :
    toList (bal l x d r) = toList l ++ (x, d) :: toList r := by
  unfold bal
  repeat' split
  all_goals (try simp only [height] at *)
  all_goals (repeat' split)
  all_goals first
    | (simp [toList_create, toList, List.append_assoc]; done)
    | (exfalso; omega)

/-! ## List lemmas -/

theorem lookupList_append_of_none (cmp : α → α → LemOrdering) (k : α) (xs ys : List (α × β))
    (h : lookupList cmp k xs = none) :
    lookupList cmp k (xs ++ ys) = lookupList cmp k ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    obtain ⟨k', v⟩ := x
    by_cases hc : cmp k k' = .EQ
    · simp [lookupList, hc] at h
    · simp only [lookupList, List.cons_append, hc, if_false] at h ⊢
      exact ih h

theorem lookupList_append_of_some (cmp : α → α → LemOrdering) (k : α) (xs ys : List (α × β)) (w : β)
    (h : lookupList cmp k xs = some w) :
    lookupList cmp k (xs ++ ys) = some w := by
  induction xs with
  | nil => simp [lookupList] at h
  | cons x xs ih =>
    obtain ⟨k', v⟩ := x
    by_cases hc : cmp k k' = .EQ
    · simp only [lookupList, List.cons_append, hc, if_true] at h ⊢; exact h
    · simp only [lookupList, List.cons_append, hc, if_false] at h ⊢
      exact ih h

theorem lookupList_eq_none (cmp : α → α → LemOrdering) (k : α) (xs : List (α × β))
    (h : ∀ x ∈ xs, cmp k x.1 ≠ .EQ) : lookupList cmp k xs = none := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    obtain ⟨k', v⟩ := x
    have hx : cmp k k' ≠ .EQ := h (k', v) (by simp)
    simp only [lookupList, hx, if_false]
    exact ih (fun y hy => h y (by simp [hy]))

theorem insertList_append_lt (cmp : α → α → LemOrdering) (k : α) (v : β) (xs : List (α × β))
    (y : α × β) (ys : List (α × β)) (hy : cmp k y.1 = .LT) :
    insertList cmp k v (xs ++ y :: ys) = insertList cmp k v xs ++ y :: ys := by
  induction xs with
  | nil => obtain ⟨ky, vy⟩ := y; simp [insertList, hy]
  | cons x xs ih =>
    obtain ⟨k', v'⟩ := x
    cases hc : cmp k k' <;> simp [insertList, hc, ih]

theorem insertList_append_gt (cmp : α → α → LemOrdering) (k : α) (v : β) (xs ys : List (α × β))
    (hxs : ∀ x ∈ xs, cmp k x.1 = .GT) :
    insertList cmp k v (xs ++ ys) = xs ++ insertList cmp k v ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    obtain ⟨k', v'⟩ := x
    have hx : cmp k k' = .GT := hxs (k', v') (by simp)
    simp [insertList, hx, ih (fun y hy => hxs y (by simp [hy]))]

theorem mem_insertList (cmp : α → α → LemOrdering) (k : α) (v : β) (xs : List (α × β))
    (z : α × β) (hz : z ∈ insertList cmp k v xs) : z = (k, v) ∨ z ∈ xs := by
  induction xs with
  | nil => simp only [insertList, List.mem_singleton] at hz; exact Or.inl hz
  | cons x xs ih =>
    obtain ⟨k', v'⟩ := x
    cases hc : cmp k k' with
    | EQ =>
      simp only [insertList, hc, List.mem_cons] at hz
      rcases hz with hz | hz
      · exact Or.inl hz
      · exact Or.inr (List.mem_cons_of_mem _ hz)
    | LT =>
      simp only [insertList, hc, List.mem_cons] at hz
      rcases hz with hz | hz | hz
      · exact Or.inl hz
      · exact Or.inr (List.mem_cons.mpr (Or.inl hz))
      · exact Or.inr (List.mem_cons_of_mem _ hz)
    | GT =>
      simp only [insertList, hc, List.mem_cons] at hz
      rcases hz with hz | hz
      · exact Or.inr (List.mem_cons.mpr (Or.inl hz))
      · rcases ih hz with h' | h'
        · exact Or.inl h'
        · exact Or.inr (List.mem_cons_of_mem _ h')

theorem lookupList_insertList_same {cmp : α → α → LemOrdering} (h : CmpLaws cmp) (k : α) (v : β)
    (xs : List (α × β)) : lookupList cmp k (insertList cmp k v xs) = some v := by
  induction xs with
  | nil => simp [insertList, lookupList, h.refl]
  | cons x xs ih =>
    obtain ⟨k', v'⟩ := x
    cases hc : cmp k k' with
    | EQ => simp [insertList, lookupList, hc, h.refl]
    | LT => simp [insertList, lookupList, hc, h.refl]
    | GT =>
      have hne : cmp k k' ≠ .EQ := by rw [hc]; decide
      simp only [insertList, hc, lookupList]
      exact ih

theorem lookupList_insertList_other {cmp : α → α → LemOrdering} (h : CmpLaws cmp) (k k' : α) (v : β)
    (xs : List (α × β)) (hne : cmp k k' ≠ .EQ) :
    lookupList cmp k (insertList cmp k' v xs) = lookupList cmp k xs := by
  induction xs with
  | nil => simp [insertList, lookupList, hne]
  | cons x xs ih =>
    obtain ⟨kx, vx⟩ := x
    cases hc : cmp k' kx with
    | EQ =>
      -- the binding at kx is replaced by (k', v); k is EQ to neither
      have hkx : cmp k kx ≠ .EQ := by rw [← h.eq_congr_right hc]; exact hne
      simp [insertList, lookupList, hc, hne, hkx]
    | LT => simp [insertList, lookupList, hc, hne]
    | GT =>
      by_cases hk : cmp k kx = .EQ
      · simp [insertList, lookupList, hc, hk]
      · simp only [insertList, hc, lookupList, hk, if_false]
        exact ih

theorem insertList_pairwise {cmp : α → α → LemOrdering} (h : CmpLaws cmp) (k : α) (v : β)
    (xs : List (α × β)) (hxs : xs.Pairwise (fun a b => cmp a.1 b.1 = .LT)) :
    (insertList cmp k v xs).Pairwise (fun a b => cmp a.1 b.1 = .LT) := by
  induction xs with
  | nil => simp [insertList]
  | cons x xs ih =>
    obtain ⟨kx, vx⟩ := x
    rw [List.pairwise_cons] at hxs
    obtain ⟨hx, hxs⟩ := hxs
    cases hc : cmp k kx with
    | EQ =>
      simp only [insertList, hc]
      rw [List.pairwise_cons]
      exact ⟨fun z hz => h.lt_of_eq_of_lt hc (hx z hz), hxs⟩
    | LT =>
      simp only [insertList, hc]
      rw [List.pairwise_cons]
      refine ⟨fun z hz => ?_, List.pairwise_cons.mpr ⟨hx, hxs⟩⟩
      rcases List.mem_cons.mp hz with hz | hz
      · rw [hz]; exact hc
      · exact h.lt_trans _ _ _ hc (hx z hz)
    | GT =>
      simp only [insertList, hc]
      rw [List.pairwise_cons]
      refine ⟨fun z hz => ?_, ih hxs⟩
      rcases mem_insertList cmp k v xs z hz with hz | hz
      · rw [hz]; exact h.gt_lt hc
      · exact hx z hz

/-! ## `find?` and `add` through the in-order list -/

theorem WF_node {cmp : α → α → LemOrdering} {l : Pmap α β} {v : α} {d : β} {r : Pmap α β} {h : Nat}
    (hw : WF cmp (.Node l v d r h)) :
    WF cmp l ∧ WF cmp r ∧ (∀ x ∈ toList l, cmp x.1 v = .LT) ∧ (∀ x ∈ toList r, cmp v x.1 = .LT) := by
  simp only [WF, toList, List.pairwise_append, List.pairwise_cons] at hw
  obtain ⟨hl, ⟨hv, hr⟩, hlr⟩ := hw
  exact ⟨hl, hr, fun x hx => hlr x hx (v, d) (by simp), fun x hx => hv x hx⟩

theorem find?_eq_lookupList {cmp : α → α → LemOrdering} (h : CmpLaws cmp) (k : α) (m : Pmap α β)
    (hw : WF cmp m) : find? cmp k m = lookupList cmp k (toList m) := by
  induction m with
  | Empty => rfl
  | Node l v d r _ ihl ihr =>
    obtain ⟨hl, hr, hlv, hvr⟩ := WF_node hw
    simp only [find?, toList]
    cases hkv : cmp k v with
    | EQ =>
      -- nothing in l is EQ to k: such an x would give cmp k v = cmp x.1 v = LT
      rw [lookupList_append_of_none]
      · simp [lookupList, hkv]
      · apply lookupList_eq_none
        intro x hx hkx
        have h1 := h.eq_congr k x.1 v hkx
        rw [hkv, hlv x hx] at h1; exact absurd h1 (by decide)
    | LT =>
      -- the answer is in l; nothing in (v, d) :: r is EQ to k
      rw [ihl hl]
      cases hres : lookupList cmp k (toList l) with
      | some w => exact (lookupList_append_of_some cmp k _ _ w hres).symm
      | none =>
        rw [lookupList_append_of_none _ _ _ _ hres]
        have hne : cmp k v ≠ .EQ := by rw [hkv]; decide
        simp only [lookupList, hne, if_false]
        symm; apply lookupList_eq_none
        intro x hx hkx
        -- cmp v k = GT (flip of LT) but also cmp v k = cmp v x.1 = LT
        have h1 : cmp v k = .GT := h.lt_gt hkv
        have h2 : cmp v k = cmp v x.1 := h.eq_congr_right hkx
        rw [h1, hvr x hx] at h2; exact absurd h2 (by decide)
    | GT =>
      -- nothing in l or (v, d) is EQ to k
      rw [lookupList_append_of_none]
      · have hne : cmp k v ≠ .EQ := by rw [hkv]; decide
        simp only [lookupList, hne, if_false]; exact ihr hr
      · apply lookupList_eq_none
        intro x hx hkx
        have h1 := h.eq_congr k x.1 v hkx
        rw [hkv, hlv x hx] at h1; exact absurd h1 (by decide)

theorem toList_add {cmp : α → α → LemOrdering} (h : CmpLaws cmp) (k : α) (v : β) (m : Pmap α β)
    (hw : WF cmp m) : toList (add cmp k v m) = insertList cmp k v (toList m) := by
  induction m with
  | Empty => rfl
  | Node l x d r hh ihl ihr =>
    obtain ⟨hl, hr, hlx, hxr⟩ := WF_node hw
    simp only [add, toList]
    split
    · -- k EQ x: replace at x — everything in l is passed (k GT each), then the EQ step
      rename_i hkx
      simp only [toList]
      rw [insertList_append_gt]
      · simp [insertList, hkx]
      · intro y hy
        exact h.gt_of_eq_of_gt hkx (h.lt_gt (hlx y hy))
    · -- k LT x: insert in l
      rename_i hkx
      rw [toList_bal, ihl hl, insertList_append_lt _ _ _ _ _ _ hkx]
    · -- k GT x: insert in r
      rename_i hkx
      rw [toList_bal, ihr hr, insertList_append_gt]
      · simp [insertList, hkx]
      · intro y hy
        exact h.gt_trans hkx (h.lt_gt (hlx y hy))

theorem WF_add {cmp : α → α → LemOrdering} (h : CmpLaws cmp) (k : α) (v : β) (m : Pmap α β)
    (hw : WF cmp m) : WF cmp (add cmp k v m) := by
  unfold WF
  rw [toList_add h k v m hw]
  exact insertList_pairwise h k v (toList m) hw

/-! ## The laws -/

theorem find?_add_same {cmp : α → α → LemOrdering} (h : CmpLaws cmp) (k : α) (v : β) (m : Pmap α β)
    (hw : WF cmp m) : find? cmp k (add cmp k v m) = some v := by
  rw [find?_eq_lookupList h k _ (WF_add h k v m hw), toList_add h k v m hw]
  exact lookupList_insertList_same h k v (toList m)

theorem find?_add_other {cmp : α → α → LemOrdering} (h : CmpLaws cmp) (k k' : α) (v : β)
    (m : Pmap α β) (hw : WF cmp m) (hne : cmp k k' ≠ .EQ) :
    find? cmp k (add cmp k' v m) = find? cmp k m := by
  rw [find?_eq_lookupList h k _ (WF_add h k' v m hw), toList_add h k' v m hw,
      lookupList_insertList_other h k k' v (toList m) hne, find?_eq_lookupList h k m hw]

end Pmap

/-! ## `Fmap` corollaries (the generated `map` type: a captured comparator
    over a `Pmap`; `fmapLookupBy` ignores its comparator argument and uses
    the captured one, as pmap.ml's wrapper does) -/

namespace Fmap
variable {α β : Type}

/-- The captured comparator is `cmp` and the tree is order-invariant under it. -/
def WF (cmp : α → α → LemOrdering) : Fmap α β → Prop
  | .empty => True
  | .mk c m => c = cmp ∧ Pmap.WF cmp m

theorem WF_empty (cmp : α → α → LemOrdering) : WF cmp (.empty : Fmap α β) := trivial

theorem WF_fmapAddBy {cmp : α → α → LemOrdering} (h : Pmap.CmpLaws cmp) (k : α) (v : β)
    (m : Fmap α β) (hw : WF cmp m) : WF cmp (fmapAddBy cmp k v m) := by
  cases m with
  | empty => exact ⟨rfl, Pmap.WF_add h k v _ (Pmap.WF_Empty cmp)⟩
  | mk c m =>
    obtain ⟨hc, hm⟩ := hw
    subst hc
    exact ⟨rfl, Pmap.WF_add h k v m hm⟩

theorem fmapLookupBy_fmapAddBy_same {cmp : α → α → LemOrdering} (h : Pmap.CmpLaws cmp)
    (c' : α → α → LemOrdering) (k : α) (v : β) (m : Fmap α β) (hw : WF cmp m) :
    fmapLookupBy c' k (fmapAddBy cmp k v m) = some v := by
  cases m with
  | empty => exact Pmap.find?_add_same h k v _ (Pmap.WF_Empty cmp)
  | mk c m =>
    obtain ⟨hc, hm⟩ := hw
    subst hc
    exact Pmap.find?_add_same h k v m hm

theorem fmapLookupBy_fmapAddBy_other {cmp : α → α → LemOrdering} (h : Pmap.CmpLaws cmp)
    (c' : α → α → LemOrdering) (k k' : α) (v : β) (m : Fmap α β) (hw : WF cmp m)
    (hne : cmp k k' ≠ .EQ) :
    fmapLookupBy c' k (fmapAddBy cmp k' v m) = fmapLookupBy c' k m := by
  cases m with
  | empty =>
    show Pmap.find? cmp k (Pmap.add cmp k' v .Empty) = none
    rw [Pmap.find?_add_other h k k' v _ (Pmap.WF_Empty cmp) hne]; rfl
  | mk c m =>
    obtain ⟨hc, hm⟩ := hw
    subst hc
    exact Pmap.find?_add_other h k k' v m hm hne

end Fmap

/-! ## An instance of the hypothesis: `defaultCompare` on `Nat` -/

theorem defaultCompare_nat (a b : Nat) :
    defaultCompare a b = (if a < b then .LT else if b < a then .GT else .EQ) := by
  simp only [defaultCompare, Nat.compare_eq_ite_lt]
  by_cases h1 : a < b
  · simp [h1]
  · by_cases h2 : b < a
    · simp [h1, h2]
    · simp [h1, h2]

theorem lt_of_defaultCompare_nat {a b : Nat} (h : defaultCompare a b = .LT) : a < b := by
  rw [defaultCompare_nat] at h
  by_cases h1 : a < b
  · exact h1
  · by_cases h2 : b < a <;> simp [h1, h2] at h

theorem eq_of_defaultCompare_nat {a b : Nat} (h : defaultCompare a b = .EQ) : a = b := by
  rw [defaultCompare_nat] at h
  by_cases h1 : a < b
  · simp [h1] at h
  · by_cases h2 : b < a
    · simp [h1, h2] at h
    · omega

theorem Pmap.cmpLaws_defaultCompare_nat : Pmap.CmpLaws (defaultCompare : Nat → Nat → LemOrdering) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a; simp [defaultCompare_nat]
  · intro a b
    rw [defaultCompare_nat, defaultCompare_nat]
    rcases Nat.lt_trichotomy a b with h | h | h
    · simp [h, Nat.lt_asymm h]
    · subst h; simp
    · simp [h, Nat.lt_asymm h]
  · intro a b c hab hbc
    have := Nat.lt_trans (lt_of_defaultCompare_nat hab) (lt_of_defaultCompare_nat hbc)
    rw [defaultCompare_nat]; simp [this]
  · intro a b c hab
    rw [eq_of_defaultCompare_nat hab]

/-! ## The generic bridge: any lawful `Ord`

`defaultCompare [Ord α] x y` is `compare x y` read into `LemOrdering`
(`LemLib.lean`), so `CmpLaws (defaultCompare)` follows from Lean core's
`Std.TransOrd α` — `Std.TransCmp (compare : α → α → Ordering)`, the class
that packages exactly the strict-weak-order laws of a comparator:
`OrientedCmp.eq_swap` (gives `flip`, and reflexivity through the
`OrientedCmp → ReflCmp` instance), `TransCmp.lt_trans`, and
`TransCmp.congr_left` (comparator-equal keys compare alike — our
`eq_congr`). `Std.TransOrd` is in Lean core (`Init/Data/Order/Ord.lean`)
in the toolchain this library is built with (4.32.2, `lean-toolchain`)
with instances for `Nat`, `Int`, `String`, `Char`,
`Bool`, the fixed-width integers, `Fin n`, `Option`, and lexicographic
products — so `Nat`/`Int`/`String` keys are covered by one theorem and
`cmpLaws_defaultCompare_nat` becomes an independent hand witness. A
comparator that is NOT `defaultCompare` of a `TransOrd` instance (the
consumer's `Ord sym` — digest compare, then `nat`, written by hand in
cerberus) is provable through the bridge once its `Ord` carries a
`Std.TransOrd` instance (a lexicographic pair of `String`/`Nat` compares,
both `TransOrd` — the instance is an `⟨eq_swap, isLE_trans⟩` pair over
`compareLex`, or by hand), else by proving `CmpLaws` directly as the `Nat`
witness does. -/

theorem defaultCompare_eq_LT_iff {α : Type} [Ord α] (a b : α) :
    defaultCompare a b = .LT ↔ compare a b = .lt := by
  unfold defaultCompare; cases compare a b <;> simp

theorem defaultCompare_eq_EQ_iff {α : Type} [Ord α] (a b : α) :
    defaultCompare a b = .EQ ↔ compare a b = .eq := by
  unfold defaultCompare; cases compare a b <;> simp

theorem Pmap.cmpLaws_of_transOrd {α : Type} [Ord α] [Std.TransOrd α] :
    Pmap.CmpLaws (defaultCompare : α → α → LemOrdering) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a
    unfold defaultCompare
    rw [Std.ReflCmp.compare_self (cmp := (Ord.compare : α → α → Ordering))]
  · intro a b
    unfold defaultCompare
    rw [Std.OrientedCmp.eq_swap (cmp := (Ord.compare : α → α → Ordering)) (a := b) (b := a)]
    cases Ord.compare a b <;> rfl
  · intro a b c hab hbc
    rw [defaultCompare_eq_LT_iff] at hab hbc ⊢
    exact Std.TransCmp.lt_trans hab hbc
  · intro a b c hab
    rw [defaultCompare_eq_EQ_iff] at hab
    unfold defaultCompare
    rw [Std.TransCmp.congr_left (cmp := (Ord.compare : α → α → Ordering)) hab]

/-- The bridge at the three key types a consumer meets first. -/
theorem Pmap.cmpLaws_defaultCompare_nat' : Pmap.CmpLaws (defaultCompare : Nat → Nat → LemOrdering) :=
  Pmap.cmpLaws_of_transOrd
theorem Pmap.cmpLaws_defaultCompare_int : Pmap.CmpLaws (defaultCompare : Int → Int → LemOrdering) :=
  Pmap.cmpLaws_of_transOrd
theorem Pmap.cmpLaws_defaultCompare_string : Pmap.CmpLaws (defaultCompare : String → String → LemOrdering) :=
  Pmap.cmpLaws_of_transOrd

/-! ## Unit pins: the kernel computes both laws on closed maps -/
section Pins
def cNat : Nat → Nat → LemOrdering := defaultCompare
def m0 : Pmap Nat String :=
  Pmap.add cNat 5 "five" (Pmap.add cNat 2 "two" (Pmap.add cNat 9 "nine" (Pmap.add cNat 1 "one" .Empty)))
example : Pmap.find? cNat 3 (Pmap.add cNat 3 "three" m0) = some "three" := by decide
example : Pmap.find? cNat 5 (Pmap.add cNat 5 "FIVE" m0) = some "FIVE" := by decide
example : Pmap.find? cNat 2 (Pmap.add cNat 3 "three" m0) = Pmap.find? cNat 2 m0 := by decide
example : Pmap.find? cNat 7 (Pmap.add cNat 3 "three" m0) = Pmap.find? cNat 7 m0 := by decide
example : Pmap.find? cNat 9 (Pmap.add cNat 3 "three" m0) = some "nine" := rfl
example : Pmap.toList m0 = [(1, "one"), (2, "two"), (5, "five"), (9, "nine")] := by decide
example : Pmap.WF cNat m0 := by decide
example : fmapLookupBy cNat 4 (fmapAddBy cNat 4 "four" (fmapAddBy cNat 1 "one" fmapEmpty)) = some "four" := by decide
/-- `Int` and `String` keys through the bridge's comparator. -/
def cInt : Int → Int → LemOrdering := defaultCompare
def cStr : String → String → LemOrdering := defaultCompare
def mI : Pmap Int Nat := Pmap.add cInt (-3) 1 (Pmap.add cInt 7 2 (Pmap.add cInt 0 3 .Empty))
example : Pmap.find? cInt (-3) (Pmap.add cInt (-3) 9 mI) = some 9 := by decide
example : Pmap.find? cInt 7 (Pmap.add cInt 5 9 mI) = Pmap.find? cInt 7 mI := by decide
example : Pmap.WF cInt mI := by decide
example (k : Int) (v : Nat) (m : Pmap Int Nat) (hw : Pmap.WF cInt m) :
    Pmap.find? cInt k (Pmap.add cInt k v m) = some v :=
  Pmap.find?_add_same Pmap.cmpLaws_of_transOrd k v m hw
def mS : Pmap String Nat := Pmap.add cStr "b" 1 (Pmap.add cStr "a" 2 (Pmap.add cStr "c" 3 .Empty))
example : Pmap.find? cStr "a" (Pmap.add cStr "a" 9 mS) = some 9 := by decide
example : Pmap.find? cStr "c" (Pmap.add cStr "bb" 9 mS) = Pmap.find? cStr "c" mS := by decide
example (k k' : String) (v : Nat) (m : Pmap String Nat) (hw : Pmap.WF cStr m) (hne : cStr k k' ≠ .EQ) :
    Pmap.find? cStr k (Pmap.add cStr k' v m) = Pmap.find? cStr k m :=
  Pmap.find?_add_other Pmap.cmpLaws_of_transOrd k k' v m hw hne
end Pins

#print axioms Pmap.find?_add_same
#print axioms Pmap.find?_add_other
#print axioms Pmap.WF_add
#print axioms Fmap.fmapLookupBy_fmapAddBy_same
#print axioms Fmap.fmapLookupBy_fmapAddBy_other
#print axioms Pmap.cmpLaws_defaultCompare_nat
#print axioms Pmap.cmpLaws_of_transOrd
#print axioms Pmap.cmpLaws_defaultCompare_int
#print axioms Pmap.cmpLaws_defaultCompare_string
