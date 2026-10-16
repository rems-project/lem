/- Proofs of the fuel_measure obligations of parity/probes/p_lem_size.lem
   (installed by parity/run.sh as P_lem_size_lemMeasureProofs.lean; the
   probe's auxiliary module imports it). `psum` is measured by the
   BACKEND-DERIVED size `ptree.lemSize` (D2-enablers slice): strong
   induction on the size, a child's size below its parent's over the
   derived list helper, `List.foldl` congruent in the per-child function
   (the template of lean-test/Test_lem_size_lemMeasureProofs.lean);
   `chain` is measured by `n + 1` (the nat template). -/
import P_lem_size

namespace P_lem_size_lemMeasureProofs

theorem ptree_child_lt (c : ptree) (w : Nat) (ts : List (Nat × ptree)) (h : (w, c) ∈ ts) :
    ptree.lemSize c < ptree.lemSize_aux1 ts := by
  induction ts with
  | nil => cases h
  | cons x xs ih =>
    obtain ⟨a, b⟩ := x
    cases h with
    | head => simp only [ptree.lemSize_aux1]; omega
    | tail _ h' => have := ih h'; simp only [ptree.lemSize_aux1]; omega

theorem foldl_congr {α : Type} (ts : List α) (acc : Nat) (F G : Nat → α → Nat)
    (h : ∀ t ∈ ts, ∀ acc, F acc t = G acc t) :
    List.foldl F acc ts = List.foldl G acc ts := by
  induction ts generalizing acc with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.foldl]
    rw [h x (List.mem_cons_self ..)]
    exact ih _ (fun t ht acc => h t (List.mem_cons_of_mem _ ht) acc)

theorem psum_stable_aux (k : Nat) : ∀ (t : ptree) (f g : Nat),
    ptree.lemSize t ≤ k → ptree.lemSize t ≤ f → ptree.lemSize t ≤ g →
    psum_lemFuel f t = psum_lemFuel g t := by
  induction k with
  | zero => intro t _ _ hk; cases t <;> simp only [ptree.lemSize] at hk <;> omega
  | succ k ih =>
    intro t f g hk hf hg
    cases f with
    | zero => cases t <;> simp only [ptree.lemSize] at hf <;> omega
    | succ f =>
      cases g with
      | zero => cases t <;> simp only [ptree.lemSize] at hg <;> omega
      | succ g =>
        cases t with
        | PL n => simp [psum_lemFuel]
        | PN ts =>
          simp only [psum_lemFuel]
          simp only [ptree.lemSize] at hk hf hg
          apply foldl_congr
          intro p hp acc
          obtain ⟨w, c⟩ := p
          have hlt := ptree_child_lt c w ts hp
          simp only [ih c f g (by omega) (by omega) (by omega)]

theorem psum_measure_sufficient (t : ptree) (lemFuel : Nat) (lemMeasureLe : ptree.lemSize t ≤ lemFuel) :
    psum_lemFuel lemFuel t = psum t :=
  psum_stable_aux (ptree.lemSize t) t lemFuel (ptree.lemSize t) (Nat.le_refl _) lemMeasureLe (Nat.le_refl _)

theorem chain_stable (n : Nat) (f g : Nat) (hf : n + 1 ≤ f) (hg : n + 1 ≤ g) :
    chain_lemFuel f n = chain_lemFuel g n := by
  induction n generalizing f g with
  | zero =>
    cases f with
    | zero => omega
    | succ f => cases g with
      | zero => omega
      | succ g => simp [chain_lemFuel]
  | succ n ih =>
    cases f with
    | zero => omega
    | succ f => cases g with
      | zero => omega
      | succ g =>
        simp only [chain_lemFuel, Nat.add_one_sub_one]
        simp only [show ((n + 1 == 0) = false) from by simp]
        simp only [Bool.false_eq_true, ↓reduceIte]
        rw [ih f g (by omega) (by omega)]

theorem chain_measure_sufficient (n : Nat) (lemFuel : Nat) (lemMeasureLe : n + 1 ≤ lemFuel) :
    chain_lemFuel lemFuel n = chain n :=
  chain_stable n lemFuel (n + 1) lemMeasureLe (Nat.le_refl _)

end P_lem_size_lemMeasureProofs
