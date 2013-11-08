Require Import Coq.ZArith.BinInt.
Require Import Coq.ZArith.Zorder.
Require Import ClassicalDescription.

(* Logic *)

Definition bool_of_Prop (P : Prop) : bool :=
   if excluded_middle_informative P then
     true
   else
     false.

Definition classical_boolean_equivalence {a : Type} (l r : a) : bool :=
  bool_of_Prop (l = r).

(* Lists *)

Notation " [] " := nil.
Notation " [ x ] " := (cons x nil).
Notation " x '::' xs " := (cons x xs).
Notation " [ x ; .. ; y ] " := (cons x .. (cons y nil) ..).

(* Nats *)

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

(* Ints *)

Definition int_ltb (i j: Z): bool :=
  bool_of_Prop (Zlt i j).
Definition int_gtb (i j: Z): bool :=
  bool_of_Prop (Zgt i j).
Definition int_lteb (i j: Z): bool :=
  bool_of_Prop (Zle i j).
Definition int_gteb (i j: Z): bool :=
  bool_of_Prop (Zge i j).

(* Sets *)

Definition set := list.
Notation "X 'union' Y" := (app X Y) (at level 60, right associativity).

Definition set_empty {a : Type} : set a := [].

Definition set_is_empty
  {elt: Type} (s: set elt): bool :=
    match s with
      | [] => true
      | _  => false
    end.

Definition set_add
  {a : Type} (x : a) (s : set a) :=
    cons x s.

Definition set_choose {elt : Type} : set elt -> elt -> elt :=
  fun set => fun default =>
    match set with
      | [] => default
      | x::xs => x
    end.

Definition set_cardinal
  {elt: Type} (s: set elt): nat :=
    List.length s. 

Definition set_exists
  {elt : Type} (p : elt -> bool) (s : set elt) : bool :=
    List.existsb p s.

Definition set_member
  {elt : Type} (e : elt) (s : set elt) : bool :=
    set_exists (fun x => classical_boolean_equivalence e x) s.

Definition set_for_all
  {elt : Type} (p : elt -> bool) (s : set elt) : bool :=
    List.forallb p s.

Fixpoint set_inter
  {elt : Type} (eq : elt -> elt -> bool)
  (left : set elt) (right : set elt) : set elt :=
    match left with
      | []    => []
      | x::xs =>
        if set_exists (eq x) right then
          x::set_inter eq xs right
        else
          set_inter eq xs right
    end.

Definition set_union
  {elt : Type} (left : set elt) (right : set elt) :=
    List.app left right.

Fixpoint set_diff
  {elt : Type} (left : set elt) (right : set elt) : set elt :=
    match left with
      | []    => []
      | x::xs =>
          if set_member x right then
            set_diff xs right
          else
            x::set_diff xs right
     end.

Fixpoint set_fold
  {elt b : Type} (f : elt -> b -> b) (s : set elt) (e : b) : b :=
    match s with
      | []    => e
      | x::xs => set_fold f xs (f x e)
    end.

Fixpoint set_select_subset
  {elt : Type} (p : elt -> bool) (s : set elt) :=
    match s with
      | []    => []
      | x::xs =>
        if p x then
          x::set_select_subset p xs
        else
          set_select_subset p xs
    end.

Fixpoint set_subset
  {elt : Type} (eq : elt -> elt -> bool)
  (left : set elt) (right : set elt) :=
    match left with
      | []    => true
      | x::xs =>
        if set_exists (eq x) right then
          set_subset eq xs right
        else
          false
    end.

Definition set_from_list
  {elt: Type} (s: set elt): list elt := s.

Definition set_to_list
  {elt: Type} (l: list elt): set elt := l.

Definition set_sigma
  {elt elt': Type} (sa: set elt) (f: elt -> set elt'): set (elt * elt') :=
    List.fold_right (fun x xys => List.fold_right (fun y xys => set_add (x, y) xys) xys (f x)) set_empty sa.
    
Axiom set_tc :
  forall {elt : Type},
  forall eq : elt -> elt -> bool,
  forall s : set (elt * elt),
    set (elt * elt).