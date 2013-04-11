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

Require Import Arith.Lt.
Require Import Ascii.
Require Import ClassicalDescription.
Require Import String.
Require Import Program.Wf.
Require Import Logic.JMeq.

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

Definition Prop_of_bool (b: bool): Prop :=
  match b with
    | true => True
    | false => False
  end.

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
  Obligation 2 of bits_of_num_aux_func.
    apply DAEMON.
  Qed.

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

(* * Finite maps. *)

Definition fmap (a b: Type) := list (a * b).

(* * Vector library. *)

Inductive vector (a : Type) : nat -> Type :=
  | vnil  : vector a 0
  | vcons : forall (n : nat), a -> vector a n -> vector a (S n).

Notation "x # l" := (vcons _ _ x l) (at level 60, right associativity).
Notation "[[ ]]" := (vnil _).
Notation "[[ x ; .. ; y ]]" := (vcons _ _ x .. (vcons _ _ y (vnil _)) ..).

Fixpoint vector_append
  {elt: Type} {m n: nat} (l: vector elt m) (r: vector elt n): vector elt (m + n) :=
    match l with
      | vnil         => r
      | vcons _ x xs => x # (vector_append xs r)
    end.

Fixpoint vector_map
  {a b: Type} {m: nat} (f: a -> b) (v: vector a m): vector b m :=
    match v with
      | vnil         => [[ ]]
      | vcons _ x xs => f x # vector_map f xs
    end.

Fixpoint vector_fold
  {a b: Type} {m: nat} (f: b -> a -> b) (e: b) (v: vector a m): b :=
    match v with
      | vnil => e
      | vcons _ x xs => vector_fold f (f e x) xs
    end.

Fixpoint vector_map_accum
  {a b c: Type} {m: nat} (f: a -> c -> b * c) (v: vector a m) (d: c): (vector b m) * c :=
    match v with
      | vnil         => ([[]], d)
      | vcons _ x xs =>
        let '(r, c) := f x d in
        let '(v, d) := vector_map_accum f xs c in
          (r # v, d)
    end.

Fixpoint vector_mapi
  {a b: Type} {m: nat} (f: nat -> a -> b) (v: vector a m): vector b m :=
    match v with
      | vnil => [[]]
      | vcons m x xs => f m x # vector_mapi f xs
    end.

Fixpoint vector_length
  {elt: Type} {m: nat} (v: vector elt m): nat :=
    match v with
      | vnil => 0
      | vcons _ x xs => S (vector_length xs)
    end.

Program Fixpoint vector_zip
  {a b: Type} {m: nat} (l: vector a m) (r: vector b m): vector (a * b) m :=
    match l with
      | vnil => [[]]
      | vcons _ x xs =>
        match r with
          | vnil => _
          | vcons _ y ys => (x, y) # vector_zip xs ys
        end
    end.

Fixpoint vector_replicate
  {elt: Type} (m: nat) (e: elt): vector elt m :=
    match m with
      | O => [[]]
      | S m => e # vector_replicate m e
    end.

Definition vector_extend
  {elt: Type} {m: nat} (n: nat) (e: elt) (v: vector elt m): vector elt (m + n) :=
    vector_append v (vector_replicate n e).

Program Definition vector_duplicate
  {elt: Type} {m: nat} (v: vector elt m): vector elt (2 * m) :=
    vector_append v v.

Program Fixpoint vector_index'
  {elt: Type} {m: nat} (n: nat) (invariant: lt n m) (v: vector elt m): elt :=
    match v with
      | vnil => _
      | vcons m x xs =>
        match n with
          | O => x
          | S n => vector_index' n _ xs
        end  
    end.
  Obligation 1.
    case (lt_n_O n invariant).
  Qed.
  Obligation 2.
    apply lt_S_n; apply invariant.
  Qed.

Definition vector_index
  {elt: Type} {m: nat} (n: nat) (v: vector elt m): elt :=
    vector_index' n DAEMON v.

Axiom vector_slice:
  forall {a: Type},
  forall {m: nat},
  forall (v: vector a m),
  forall (n o: nat),
    vector a (o - n).

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
  {elt: Type} (s: set elt): num :=
    List.length s. 

Definition set_exists
  {elt : Type} (p : elt -> bool) (s : set elt) : bool :=
    List.existsb p s.

Definition set_member
  {elt : Type} (e : elt) (s : set elt) : bool :=
    set_exists (fun x => e == x) s.

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

Axiom set_tc :
  forall {elt : Type},
  forall eq : elt -> elt -> bool,
  forall s : set (elt * elt),
    set (elt * elt).

(* * String an ASCII related functions. *)

Definition ascii_beq
  (l r : ascii) : bool :=
    match l with
      | Ascii b1 b2 b3 b4 b5 b6 b7 b8 =>
        match r with
          | Ascii b1' b2' b3' b4' b5' b6' b7' b8' =>
              andb (bool_beq b1 b1')
              (andb (bool_beq b2 b2')
              (andb (bool_beq b3 b3')
              (andb (bool_beq b4 b4')
              (andb (bool_beq b5 b5')
              (andb (bool_beq b6 b6')
              (andb (bool_beq b7 b7')
                    (bool_beq b8 b8')))))))
        end
    end.

Fixpoint string_beq
  (l r : string) : bool :=
    match l with
      | EmptyString  =>
        match r with
          | EmptyString => true
          | _           => false
        end
      | String hd tl =>
        match r with
          | String hd' tl' =>
              andb (ascii_beq hd hd') (string_beq tl tl')
          | _              => false
        end
    end.


(* * Default values. *)

Definition bool_default : bool := true.
Definition num_default : num := 0.
Definition set_default {a : Type}: set a := set_empty.
Definition list_default {a : Type}: list a := [].
Definition fmap_default {a b : Type}: list (a * b) := [].
Definition option_default {a : Type} : option a := None.
Definition ascii_default : ascii := Ascii true true true true true true true true.
Definition string_default : string := "" % string.