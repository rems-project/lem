/- Hand-written proofs of the fuel_measure obligations of test_lem_size.lem
   (D2-enablers slice, 2026-09-04): measured recursions over generated
   inductives whose measure is the BACKEND-DERIVED structural size
   (`tm.lemSize`, `mtree.lemSize`, `sbox.lemSize`). The template is the
   fuel-measure slice's nested-inductive one (Test_fuel_measure_tree_
   lemMeasureProofs.lean): strong induction on the size, a child's size is
   strictly below its parent's (`*_child_lt`, over the derived list
   helpers), and a fold/all over children is congruent in the per-child
   function. `tm_eq` is the D2 shape — `List.all (fun …) (List.zip …)` AS
   WRITTEN — with `lemListZip_eq` (LemLibTheorems) bridging to `List.zip`.
   Kernel-only tactics, no `native_decide`, no option bump; `#print axioms`
   below. -/
import Test_lem_size
import LemLibTheorems

namespace Test_lem_size_lemMeasureProofs

/-! ### size facts over the derived helpers -/

theorem tm_child_lt (c : tm) (n : Nat) (xs : List (Nat × tm)) (h : (n, c) ∈ xs) :
    tm.lemSize c < tm.lemSize_aux1 xs := by
  induction xs with
  | nil => cases h
  | cons x xs ih =>
    obtain ⟨a, b⟩ := x
    cases h with
    | head => simp only [tm.lemSize_aux1]; omega
    | tail _ h' => have := ih h'; simp only [tm.lemSize_aux1]; omega

theorem mtree_child_lt (t : mtree) (ts : List mtree) (h : t ∈ ts) :
    mtree.lemSize t < mtree.lemSize_aux1 ts := by
  induction ts with
  | nil => cases h
  | cons x xs ih =>
    cases h with
    | head => simp only [mtree.lemSize_aux1]; omega
    | tail _ h' => have := ih h'; simp only [mtree.lemSize_aux1]; omega

theorem sbox_child_lt {a : Type} (k : sbox a) (ks : List (sbox a)) (h : k ∈ ks) :
    sbox.lemSize k < sbox.lemSize_aux1 ks := by
  induction ks with
  | nil => cases h
  | cons x xs ih =>
    cases h with
    | head => simp only [sbox.lemSize_aux1]; omega
    | tail _ h' => have := ih h'; simp only [sbox.lemSize_aux1]; omega

/-! ### congruence of the traversals in the per-child function -/

theorem foldl_congr {α : Type} (ts : List α) (acc : Nat) (F G : Nat → α → Nat)
    (h : ∀ t ∈ ts, ∀ acc, F acc t = G acc t) :
    List.foldl F acc ts = List.foldl G acc ts := by
  induction ts generalizing acc with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.foldl]
    rw [h x (List.mem_cons_self ..)]
    exact ih _ (fun t ht acc => h t (List.mem_cons_of_mem _ ht) acc)

theorem all_congr {α : Type} (l : List α) (F G : α → Bool)
    (h : ∀ p ∈ l, F p = G p) : l.all F = l.all G := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.all_cons]
    rw [h x (List.mem_cons_self ..), ih (fun p hp => h p (List.mem_cons_of_mem _ hp))]

/-! ### tm_sum : `List.foldl` over a list of pairs, then a maybe -/

theorem tm_sum_stable_aux (k : Nat) : ∀ (t : tm) (f g : Nat),
    tm.lemSize t ≤ k → tm.lemSize t ≤ f → tm.lemSize t ≤ g →
    tm_sum_lemFuel f t = tm_sum_lemFuel g t := by
  induction k with
  | zero => intro t _ _ hk; cases t <;> simp only [tm.lemSize] at hk <;> omega
  | succ k ih =>
    intro t f g hk hf hg
    cases f with
    | zero => cases t <;> simp only [tm.lemSize] at hf <;> omega
    | succ f =>
      cases g with
      | zero => cases t <;> simp only [tm.lemSize] at hg <;> omega
      | succ g =>
        cases t with
        | TLeaf n => simp [tm_sum_lemFuel]
        | TNode xs o =>
          simp only [tm_sum_lemFuel]
          simp only [tm.lemSize] at hk hf hg
          congr 1
          · apply foldl_congr
            intro p hp acc
            obtain ⟨n, c⟩ := p
            have hlt := tm_child_lt c n xs hp
            simp only [ih c f g (by omega) (by omega) (by omega)]
          · cases o with
            | none => rfl
            | some c =>
              simp only [tm.lemSize_aux2] at hk hf hg
              simp only [ih c f g (by omega) (by omega) (by omega)]

theorem tm_sum_measure_sufficient (t : tm) (lemFuel : Nat) (lemMeasureLe : tm.lemSize t ≤ lemFuel) :
    tm_sum_lemFuel lemFuel t = tm_sum t :=
  tm_sum_stable_aux (tm.lemSize t) t lemFuel (tm.lemSize t) (Nat.le_refl _) lemMeasureLe (Nat.le_refl _)

/-! ### tm_eq : the D2 shape — `List.all (fun …) (List.zip …)` as written;
    the measure is the FIRST argument's size (the recursion descends into
    both, but the zip is bounded by the first list) -/

theorem tm_eq_stable_aux (k : Nat) : ∀ (t1 t2 : tm) (f g : Nat),
    tm.lemSize t1 ≤ k → tm.lemSize t1 ≤ f → tm.lemSize t1 ≤ g →
    tm_eq_lemFuel f t1 t2 = tm_eq_lemFuel g t1 t2 := by
  induction k with
  | zero => intro t1 _ _ _ hk; cases t1 <;> simp only [tm.lemSize] at hk <;> omega
  | succ k ih =>
    intro t1 t2 f g hk hf hg
    cases f with
    | zero => cases t1 <;> simp only [tm.lemSize] at hf <;> omega
    | succ f =>
      cases g with
      | zero => cases t1 <;> simp only [tm.lemSize] at hg <;> omega
      | succ g =>
        cases t1 with
        | TLeaf n1 => cases t2 <;> simp [tm_eq_lemFuel]
        | TNode xs1 o1 =>
          cases t2 with
          | TLeaf n2 => simp [tm_eq_lemFuel]
          | TNode xs2 o2 =>
            simp only [tm_eq_lemFuel]
            simp only [tm.lemSize] at hk hf hg
            congr 1
            · rw [LemLibTheorems.lemListZip_eq]
              apply all_congr
              intro p hp
              obtain ⟨⟨n1, c1⟩, ⟨n2, c2⟩⟩ := p
              have hmem := (List.of_mem_zip hp).1
              have hlt := tm_child_lt c1 n1 xs1 hmem
              simp only [ih c1 c2 f g (by omega) (by omega) (by omega)]
            · cases o1 with
              | none => cases o2 <;> rfl
              | some a =>
                cases o2 with
                | none => rfl
                | some b =>
                  simp only [tm.lemSize_aux2] at hk hf hg
                  simp only [ih a b f g (by omega) (by omega) (by omega)]

theorem tm_eq_measure_sufficient (t1 : tm) (t2 : tm) (lemFuel : Nat) (lemMeasureLe : tm.lemSize t1 ≤ lemFuel) :
    tm_eq_lemFuel lemFuel t1 t2 = tm_eq t1 t2 :=
  tm_eq_stable_aux (tm.lemSize t1) t1 t2 lemFuel (tm.lemSize t1) (Nat.le_refl _) lemMeasureLe (Nat.le_refl _)

/-! ### mcount : a type from another module (mtree), its size imported -/

theorem mcount_stable_aux (k : Nat) : ∀ (t : mtree) (f g : Nat),
    mtree.lemSize t ≤ k → mtree.lemSize t ≤ f → mtree.lemSize t ≤ g →
    mcount_lemFuel f t = mcount_lemFuel g t := by
  induction k with
  | zero => intro t _ _ hk; cases t <;> simp only [mtree.lemSize] at hk <;> omega
  | succ k ih =>
    intro t f g hk hf hg
    cases f with
    | zero => cases t <;> simp only [mtree.lemSize] at hf <;> omega
    | succ f =>
      cases g with
      | zero => cases t <;> simp only [mtree.lemSize] at hg <;> omega
      | succ g =>
        cases t with
        | MLeaf n => simp [mcount_lemFuel]
        | MNode ts =>
          simp only [mcount_lemFuel]
          simp only [mtree.lemSize] at hk hf hg
          apply foldl_congr
          intro t' ht' acc
          have hlt := mtree_child_lt t' ts ht'
          simp only [ih t' f g (by omega) (by omega) (by omega)]

theorem mcount_measure_sufficient (t : mtree) (lemFuel : Nat) (lemMeasureLe : mtree.lemSize t ≤ lemFuel) :
    mcount_lemFuel lemFuel t = mcount t :=
  mcount_stable_aux (mtree.lemSize t) t lemFuel (mtree.lemSize t) (Nat.le_refl _) lemMeasureLe (Nat.le_refl _)

/-! ### sb_count : a parametric type, the explicit `sbox.lemSize s` form -/

theorem sb_count_stable_aux (k : Nat) : ∀ (s : sbox Nat) (f g : Nat),
    sbox.lemSize s ≤ k → sbox.lemSize s ≤ f → sbox.lemSize s ≤ g →
    sb_count_lemFuel f s = sb_count_lemFuel g s := by
  induction k with
  | zero => intro s _ _ hk; cases s <;> simp only [sbox.lemSize] at hk <;> omega
  | succ k ih =>
    intro s f g hk hf hg
    cases f with
    | zero => cases s <;> simp only [sbox.lemSize] at hf <;> omega
    | succ f =>
      cases g with
      | zero => cases s <;> simp only [sbox.lemSize] at hg <;> omega
      | succ g =>
        cases s with
        | SE => simp [sb_count_lemFuel]
        | SB x ks =>
          simp only [sb_count_lemFuel]
          simp only [sbox.lemSize] at hk hf hg
          congr 1
          apply foldl_congr
          intro k' hk' acc
          have hlt := sbox_child_lt k' ks hk'
          simp only [ih k' f g (by omega) (by omega) (by omega)]

theorem sb_count_measure_sufficient (s : sbox Nat) (lemFuel : Nat) (lemMeasureLe : sbox.lemSize s ≤ lemFuel) :
    sb_count_lemFuel lemFuel s = sb_count s :=
  sb_count_stable_aux (sbox.lemSize s) s lemFuel (sbox.lemSize s) (Nat.le_refl _) lemMeasureLe (Nat.le_refl _)

end Test_lem_size_lemMeasureProofs

#print axioms Test_lem_size_lemMeasureProofs.tm_sum_measure_sufficient
#print axioms Test_lem_size_lemMeasureProofs.tm_eq_measure_sufficient
#print axioms Test_lem_size_lemMeasureProofs.mcount_measure_sufficient
#print axioms Test_lem_size_lemMeasureProofs.sb_count_measure_sufficient
