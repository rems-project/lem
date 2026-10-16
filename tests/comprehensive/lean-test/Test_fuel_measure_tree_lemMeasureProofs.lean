/- Hand-written proofs of the fuel_measure obligations of
   test_fuel_measure_tree.lem (fuel-measure slice, 2026-09-04): measured
   recursions over the NESTED inductive `mtree`, one of them through a
   higher-order `List.foldl` AS WRITTEN in lem — the shape the structural
   declare refuses and a fuel measure handles without restructuring. The
   proofs go by strong induction on the measure (`treeSize`), so no
   nested-inductive induction principle is needed: a child's size is
   strictly below its parent's (`child_lt`), and a fold over children is
   congruent in the per-child function (`foldl_congr`). Kernel-only
   tactics, no `native_decide`, no option bump; `#print axioms` below. -/
import Test_fuel_measure_tree

namespace Test_fuel_measure_tree_lemMeasureProofs

open TestFuelMeasureImpl

theorem child_lt (t : mtree) (ts : List mtree) (h : t ∈ ts) : treeSize t < treesSize ts := by
  induction ts with
  | nil => cases h
  | cons x xs ih =>
    cases h with
    | head => simp only [treesSize]; omega
    | tail _ h' => have := ih h'; simp only [treesSize]; omega

theorem foldl_congr (ts : List mtree) (acc : Nat) (F G : mtree → Nat)
    (h : ∀ t ∈ ts, F t = G t) :
    List.foldl (fun acc t => acc + F t) acc ts = List.foldl (fun acc t => acc + G t) acc ts := by
  induction ts generalizing acc with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.foldl]
    rw [h x (List.mem_cons_self ..)]
    exact ih _ (fun t ht => h t (List.mem_cons_of_mem _ ht))

/-! ### mtsum : recursion through `List.foldl (fun acc t' => acc + mtsum t')` -/

theorem mtsum_stable_aux (k : Nat) : ∀ (t : mtree) (f g : Nat),
    treeSize t ≤ k → treeSize t ≤ f → treeSize t ≤ g →
    mtsum_lemFuel f t = mtsum_lemFuel g t := by
  induction k with
  | zero => intro t _ _ hk; cases t <;> simp [treeSize] at hk
  | succ k ih =>
    intro t f g hk hf hg
    cases f with
    | zero => cases t <;> simp [treeSize] at hf
    | succ f =>
      cases g with
      | zero => cases t <;> simp [treeSize] at hg
      | succ g =>
        cases t with
        | MLeaf n => simp [mtsum_lemFuel]
        | MNode ts =>
          simp only [mtsum_lemFuel]
          apply foldl_congr
          intro t' ht'
          have hlt := child_lt t' ts ht'
          simp only [treeSize] at hk hf hg
          exact ih t' f g (by omega) (by omega) (by omega)

theorem mtsum_measure_sufficient (t : mtree) (lemFuel : Nat) (lemMeasureLe : treeSize t ≤ lemFuel) :
    mtsum_lemFuel lemFuel t = mtsum t :=
  mtsum_stable_aux (treeSize t) t lemFuel (treeSize t) (Nat.le_refl _) lemMeasureLe (Nat.le_refl _)

/-! ### mdepth / mdepths : the mutual pair over the type and its list -/

theorem mdepth_stable_aux (k : Nat) :
    (∀ (t : mtree) (f g : Nat), treeSize t ≤ k → treeSize t ≤ f → treeSize t ≤ g →
        mdepth_lemFuel f t = mdepth_lemFuel g t) ∧
    (∀ (ts : List mtree) (f g : Nat), treesSize ts ≤ k → treesSize ts ≤ f → treesSize ts ≤ g →
        mdepths_lemFuel f ts = mdepths_lemFuel g ts) := by
  induction k with
  | zero =>
    constructor
    · intro t _ _ hk; cases t <;> simp [treeSize] at hk
    · intro ts _ _ hk; cases ts <;> simp [treesSize] at hk
  | succ k ih =>
    constructor
    · intro t f g hk hf hg
      cases f with
      | zero => cases t <;> simp [treeSize] at hf
      | succ f =>
        cases g with
        | zero => cases t <;> simp [treeSize] at hg
        | succ g =>
          cases t with
          | MLeaf n => simp [mdepth_lemFuel]
          | MNode ts =>
            simp only [mdepth_lemFuel, treeSize] at hk hf hg ⊢
            rw [ih.2 ts f g (by omega) (by omega) (by omega)]
    · intro ts f g hk hf hg
      cases f with
      | zero => cases ts <;> simp [treesSize] at hf
      | succ f =>
        cases g with
        | zero => cases ts <;> simp [treesSize] at hg
        | succ g =>
          cases ts with
          | nil => simp [mdepths_lemFuel]
          | cons t ts' =>
            simp only [mdepths_lemFuel, treesSize] at hk hf hg ⊢
            rw [ih.1 t f g (by omega) (by omega) (by omega),
                ih.2 ts' f g (by omega) (by omega) (by omega)]

theorem mdepth_measure_sufficient (t : mtree) (lemFuel : Nat) (lemMeasureLe : treeSize t ≤ lemFuel) :
    mdepth_lemFuel lemFuel t = mdepth t :=
  (mdepth_stable_aux (treeSize t)).1 t lemFuel (treeSize t) (Nat.le_refl _) lemMeasureLe (Nat.le_refl _)

theorem mdepths_measure_sufficient (ts : List mtree) (lemFuel : Nat) (lemMeasureLe : treesSize ts ≤ lemFuel) :
    mdepths_lemFuel lemFuel ts = mdepths ts :=
  (mdepth_stable_aux (treesSize ts)).2 ts lemFuel (treesSize ts) (Nat.le_refl _) lemMeasureLe (Nat.le_refl _)

end Test_fuel_measure_tree_lemMeasureProofs

#print axioms Test_fuel_measure_tree_lemMeasureProofs.mtsum_measure_sufficient
#print axioms Test_fuel_measure_tree_lemMeasureProofs.mdepth_measure_sufficient
