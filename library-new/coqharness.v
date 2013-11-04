Require Import Coq.ZArith.BinInt.
Require Import Coq.ZArith.Zorder.
Require Import ClassicalDescription.

Definition bool_of_Prop (P : Prop) : bool :=
   if excluded_middle_informative P then
     true
   else
     false.

Definition classical_boolean_equivalence {a : Type} (l r : a) : bool :=
  bool_of_Prop (l = r).

Notation " [] " := nil.
Notation " [ x ] " := (cons x nil).
Notation " [ x ; .. ; y ] " := (cons x .. (cons y nil) ..).

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

Definition int_ltb (i j: Z): bool :=
  bool_of_Prop (Zlt i j).
Definition int_gtb (i j: Z): bool :=
  bool_of_Prop (Zgt i j).
Definition int_lteb (i j: Z): bool :=
  bool_of_Prop (Zle i j).
Definition int_gteb (i j: Z): bool :=
  bool_of_Prop (Zge i j).