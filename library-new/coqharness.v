Require Import ClassicalDescription.

Definition Prop_of_bool (P : Prop) : bool :=
   if excluded_middle_informative P then
     true
   else
     false.

Definition classical_boolean_equivalence {a : Type} (l r : a) : bool :=
  Prop_of_bool (l = r).

Fixpoint nat_power (base exp: nat): nat :=
  match exp with
    | O => 1
    | S exp' => base * nat_power base exp'
  end.

Axiom nat_div : nat -> nat -> nat.
Axiom nat_mod : nat -> nat -> nat.

Fixpoint nat_min (m n: nat): nat :=
  match m with
    | O => O
    | S m' =>
      match n with
        | O => S m'
        | S n' => S (nat_min m' n')
      end
  end.

Fixpoint nat_max (m n: nat): nat :=
  match m with
    | O => n
    | S m' =>
      match n with
        | O => S m'
        | S n' => S (nat_max m' n')
      end
  end.

Fixpoint nat_ltb (m n: nat): bool :=
  match m with
    | O =>
      match n with
        | O => false
        | _ => true
      end
    | S m' =>
      match n with
        | O => false
        | S n' => nat_ltb m' n'
      end
  end.

Definition nat_lteb (m n: nat): bool := nat_ltb (S m) n.

Definition nat_gtb (m n: nat): bool := nat_ltb n m.

Definition nat_gteb (m n: nat): bool := nat_lteb n m.