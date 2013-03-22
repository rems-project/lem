(*========================================================================*)
(*                        Lem                                             *)
(*                                                                        *)
(*          Dominic Mulligan, University of Cambridge                     *)
(*          Francesco Zappa Nardelli, INRIA Paris-Rocquencourt            *)
(*          Gabriel Kerneis, University of Cambridge                      *)
(*          Kathy Gray, University of Cambridge                           *)
(*          Peter Boehm, University of Cambridge (while working on Lem)   *)
(*          Peter Sewell, University of Cambridge                         *)
(*          Scott Owens, University of Kent                               *)
(*          Thomas Tuerk, University of Cambridge                         *)
(*                                                                        *)
(*  The Lem sources are copyright 2010-2013                               *)
(*  by the UK authors above and Institut National de Recherche en         *)
(*  Informatique et en Automatique (INRIA).                               *)
(*                                                                        *)
(*  All files except ocaml-lib/pmap.{ml,mli} and ocaml-libpset.{ml,mli}   *)
(*  are distributed under the license below.  The former are distributed  *)
(*  under the LGPLv2, as in the LICENSE file.                             *)
(*                                                                        *)
(*                                                                        *)
(*  Redistribution and use in source and binary forms, with or without    *)
(*  modification, are permitted provided that the following conditions    *)
(*  are met:                                                              *)
(*  1. Redistributions of source code must retain the above copyright     *)
(*  notice, this list of conditions and the following disclaimer.         *)
(*  2. Redistributions in binary form must reproduce the above copyright  *)
(*  notice, this list of conditions and the following disclaimer in the   *)
(*  documentation and/or other materials provided with the distribution.  *)
(*  3. The names of the authors may not be used to endorse or promote     *)
(*  products derived from this software without specific prior written    *)
(*  permission.                                                           *)
(*                                                                        *)
(*  THIS SOFTWARE IS PROVIDED BY THE AUTHORS ``AS IS'' AND ANY EXPRESS    *)
(*  OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED     *)
(*  WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE    *)
(*  ARE DISCLAIMED. IN NO EVENT SHALL THE AUTHORS BE LIABLE FOR ANY       *)
(*  DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL    *)
(*  DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE     *)
(*  GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS         *)
(*  INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER  *)
(*  IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR       *)
(*  OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN   *)
(*  IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.                         *)
(*========================================================================*)

Require Import Ascii.
Require Import ClassicalDescription.
Require Import String.
Require Import Program.Wf.

(* * Basic types and definitions required for Lem. *)

Definition num := nat.

Definition fst {a b : Type}: a * b -> a :=
  fun p =>
    let '(f, s) := p in
      f.

Definition snd {a b : Type}: a * b -> b :=
  fun p =>
    let '(f, s) := p in
      s.

(* * Collapsing Prop into bool, and related definitions. *)

Axiom DAEMON :
  forall {a : Type},
    a.

Definition bool_of_Prop (P : Prop) : bool :=
  if excluded_middle_informative P then
    true
  else
    false.

Definition eq {a : Type}: a -> a -> bool :=
  fun left right =>
    bool_of_Prop (left = right).

Notation "X == Y" := (eq X Y) (at level 20).

(* * Missing logical notions in bool. *)

Definition not_b (b : bool) :=
  match b with
    | true => false
    | false => true
  end.

Definition bool_beq
  (l r : bool) : bool :=
    match l with
      | true => r
      | false =>
        match r with
          | true => false
          | false => true
        end
    end.

Definition imp_b (b c: bool) :=
  match b with
    | true => c
    | false => true
  end.

Notation "X --> Y" := (imp_b X Y) (at level 40).

(* * Arithmetic definitions. *)

Fixpoint nat_eq_b
  (m n: num): bool :=
    match m with
      | 0 =>
        match n with
          | 0 => true
          | _ => false
        end
      | S m =>
        match n with
          | S n => nat_eq_b m n
          | _   => false
        end
    end.

Lemma nat_eq_b_reflexive:
  forall m,
    nat_eq_b m m = true.
  intro. elim m.
    trivial.
    intro. intro. simpl.
    assumption.
Qed.

Lemma nat_eq_b_symmetric:
  forall m n,
    nat_eq_b m n = true -> nat_eq_b n m = true.
  intro. elim m.
    intro. case n. simpl. auto.
    intro. simpl. intro. discriminate.
    intro. intro. intro. case n0.
      simpl. intro. discriminate.
      intro. simpl. intro. apply H. auto.
Qed.

Fixpoint lte_b (l r : num) : bool :=
  match l with
    | O => true
    | S l' =>
      match r with
        | O => false
        | S r' => lte_b l' r'
      end
  end.

Definition lt_b :=
  fun l r => lte_b (S l) r.

Lemma lte_b_reflexive:
  forall m,
    lte_b m m = true.
  intro. elim m.
    trivial.
    intro. intro. simpl. assumption.
Qed.

Lemma lt_b_true_to_lte_b_true:
  forall m n,
    lt_b m n = true -> lte_b m n = true.
  intro m. elim m.
    intro n. intro. trivial.
    intro. intro.  

Definition gt_b (l r : num) : bool := lt_b r l.

Definition gte_b :=
  fun l r => r <= l.

Fixpoint minus
  (m : nat) (n : nat) :=
    match m with
      | 0       => 0
      | S m' =>
        match n with
          | 0       => S m'
          | S n' => minus m' n'
        end
    end.

Fixpoint power
  (base exponent: num): num :=
    match exponent with
      | 0   => 1
      | S e => base * (power base e)
    end.

Fixpoint divide_aux
  (p m n: num): num :=
    match lte_b m n with
      | true => 0
      | false =>
        match p with
          | 0 => 0
          | S p => S (divide_aux p (minus m (S n)) n)
        end
    end.

Definition divide
  (m n: num): num :=
    match m with
      | O => S n (* XXX: arbitrary *)
      | S p => divide_aux n n p
    end.

Fixpoint mod_aux
  (p m n: num): num :=
    match lte_b m n with
      | true => m
      | false =>
        match p with
          | 0 => m
          | S p => mod_aux p (minus m (S n)) n
        end
    end.

Lemma lte_b_n_0_elim:
  forall n P,
    lte_b n 0 = true -> P 0 -> P n.
  intro. intro. case n.
  compute. auto.
  intro. compute. intro.
  discriminate H.
Qed.

Lemma nat_case:
  forall m P,
    P 0 -> (forall m, P (S m)) -> P m.
  intros. case m. auto. auto.
Qed.

Axiom nat_elim_2:
  forall {P: nat -> nat -> Type},
  forall m n,
    (forall m, P 0 m) ->
    (forall m, P (S m) 0) ->
    (forall m n, P m n -> P (S m) (S n)) ->
    P m n.

Axiom lte_b_true_to_eq_or_lt_b_true:
  forall m n,
    lte_b m n = true -> nat_eq_b m n = true \/ lt_b m n = true.

Axiom lte_b_m_Sn_elim:
  forall m n P,
  lte_b m (S n) = true ->
  (lte_b (S m) (S n) = true -> P) ->
  (m = S n -> P) -> P.

Axiom lte_b_mod_aux_m_m: 
  forall p n m,
    lte_b n p = true -> lte_b (mod_aux p n m) m = true.

Definition mod
  (m n: num): num :=
    match m with
      | O => n
      | S m => mod_aux n n m
    end.

Definition divide_mod
  (m n: num): (num * num) :=
    (divide m n, mod m n).

Fixpoint num_beq (l r : num) : bool :=
  match l with
    | O =>
      match r with
        | O => true
        | _ => false
      end
    | S l' =>
      match r with
        | O => false
        | S r' => num_beq l' r'
      end
  end.

Notation "x - y" := (minus x y) (at level 50, left associativity).
Notation "X <= Y" := (lte_b X Y).
Notation "X < Y" := (lt_b X Y).
Notation "X > Y" := (gt_b X Y).
Notation "X >= Y" := (gte_b X Y).

(* * Bitwise operations on numerics. *)

Program Fixpoint bits_of_num_aux
  (m: num) (exponent: num) {measure (mod m (power 2 exponent))}: list bool :=
    match m with
      | 0 => nil
      | m =>
        let d := power 2 exponent in
        let b := mod m d in
        let bit :=
          match b with
            | 0 => false
            | _ => true
          end
        in
          cons bit (bits_of_num_aux (minus m d) (S exponent))
    end.
  Obligation 2.

Axiom bitwise_not:
  num -> num.

Axiom bitwise_and:
  num -> num -> num.

Axiom bitwise_or:
  num -> num -> num.

Axiom bitwise_xor:
  num -> num -> num.

Axiom bitwise_asr:
  num -> num -> num.

Axiom bitwise_lsl:
  num -> num -> num.

Axiom bitwise_lsr:
  num -> num -> num.

(* * List library. *)

Notation "x :: l" := (cons x l) (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Fixpoint list_append
  {a : Type} (left : list a) (right : list a) :=
    match left with
      | []    => right
      | x::xs => x :: list_append xs right
    end.

Fixpoint list_map
  {a b : Type} (f : a -> b) (l : list a) :=
    match l with
      | []    => []
      | x::xs => f x :: list_map f xs
    end.

Fixpoint list_reverse
  {a : Type} (l : list a) :=
    match l with
      | []    => []
      | x::xs => list_append (list_reverse xs) [ x ]
    end.

Fixpoint list_length
  {a : Type} (l : list a) :=
    match l with
      | []    => 0
      | x::xs => S (list_length xs)
    end.

Fixpoint list_filter
  {a : Type} (p : a -> bool) (l : list a) : list a :=
    match l with
      | []    => []
      | x::xs =>
          if p x then
            x::list_filter p xs
          else
            list_filter p xs
    end.

Fixpoint list_for_all
  {elt : Type} (p : elt -> bool) (l : list elt) : bool :=
    match l with
      | []    => true
      | x::xs =>
        if p x then
          list_for_all p xs
        else
          false
    end.

Fixpoint list_exists
  {elt : Type} (p : elt -> bool) (l : list elt) : bool :=
    match l with
      | []    => true
      | x::xs =>
        if p x then
          true
        else
          list_exists p xs
    end.

Fixpoint list_fold_right
  {a b : Type} (f : a -> b -> b) (e : b) (l : list a) : b :=
    match l with
      | []    => e
      | x::xs => f x (list_fold_right f e xs)
    end.

Fixpoint list_fold_left
  {a b : Type} (f : a -> b -> a) (e : a) (l : list b) : a :=
    match l with
      | []    => e
      | x::xs => list_fold_left f (f e x) xs
    end.

(* * Finite map library. *)

Definition map (a b : Type) := list (a * b).

Definition map_empty {a b : Type} : map a b := nil.

Definition map_add {a b : Type} : a -> b -> map a b -> map a b :=
  fun k => fun v => fun m =>
    cons (k, v) m.

Fixpoint map_mem
  {a b : Type} (eq : a -> a -> bool) (k : a) (m : map a b) :=
    match m with
      | []    => false
      | x::xs =>
          let '(l, r) := x in
            if eq l k then
              true
            else
              map_mem eq k xs
    end.

Fixpoint map_find
  {a b : Type} (eq : a -> a -> bool) (k : a) (m : map a b) :=
    match m with
      | []    => DAEMON
      | x::xs =>
          let '(l, r) := x in
            if eq l k then
              r
            else
              map_find eq k xs
    end.

(* * Set library. *)

Definition set (a : Type) := a -> Prop.