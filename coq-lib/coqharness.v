Require Import Coq.Bool.Bool.
Require Import Coq.ZArith.BinInt.
Require Import Coq.ZArith.Zorder.
Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import Coq.Arith.EqNat.
Require Import ClassicalDescription.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Program.Wf.

(* Logic *)

Axiom DAEMON: forall {a: Type}, a.

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

Coercion Prop_of_bool: bool >-> Sortclass.

Definition classical_boolean_equivalence {a : Type} (l r : a) : bool :=
  bool_of_Prop (l = r).

(* Lists *)

Notation " [] " := nil.
Notation " [ x ] " := (cons x nil).
Notation " x '::' xs " := (cons x xs).
Notation " [ x ; .. ; y ] " := (cons x .. (cons y nil) ..).

Fixpoint list_equal_by
  {elt: Type} (elteq: elt -> elt -> bool) (left right: list elt): bool :=
    match left with
      | [] =>
        match right with
          | [] => true
          | _  => false
        end
      | x::xs =>
        match right with
          | []    => false
          | y::ys => andb (elteq x y) (list_equal_by elteq xs ys)
        end
    end.

Fixpoint list_member_by
  {elt: Type} (elteq: elt -> elt -> bool) (e: elt) (l: list elt) :=
    match l with
      | [] => false
      | x::xs =>
          if elteq x e then
            true
          else
            list_member_by elteq e xs
    end.

Program Fixpoint list_head
  {elt: Type} (l: list elt) (p: 0 < List.length l): elt :=
    match l return 0 < List.length l -> elt with
      | [] => fun absurd => _
      | x::xs => fun irrelevant => x
    end p.
  Obligation 1.
    destruct (Coq.Arith.Lt.lt_irrefl 0).
    apply absurd.
Qed.

Program Fixpoint list_tail
  {elt: Type} (l: list elt) (p: 0 < List.length l): list elt :=
    match l return 0 < List.length l -> list elt with
      | [] => fun absurd => _
      | x::xs => fun irrelevant => xs
    end p.

(* Comparisons *)

Inductive ordering: Type :=
  | LT: ordering
  | EQ: ordering
  | GT: ordering.

Definition ordering_equal
  (left right: ordering): bool :=
    match left, right with
      | LT, LT => true
      | EQ, EQ => true
      | GT, GT => true
      | _, _ => false
    end.

(* Tuples. *)

Definition tuple_equal_by
  {elt elt': Type} (elteq: elt -> elt -> bool) (elteq': elt' -> elt' -> bool)
  (left right: elt * elt'): bool :=
    let (lleft, lright) := left in
    let (rleft, rright) := right in
      andb (elteq lleft rleft) (elteq' lright rright).

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

Program Fixpoint gen_pow_aux
  {a : Type} (mul : a -> a -> a) (a0 : a) (b : a) (e : nat) {measure e} : a := 
   match e with 
     | 0 => a0 (* cannot happen, call discipline guarentees e >= 1 *)
     | 1 => mul a0 b
     |(  S (S (e'))) => let e'' := div e 2 in
                   let a'  := (if beq_nat (modulo e 2) 0 then a0 else mul a0 b) in
                   gen_pow_aux mul a' (mul b b) e''
   end.
  Obligation 1.
    apply DAEMON. (* XXX: finish *)
  Defined.


(* Ints *)

Definition int_ltb (i j: Z): bool := Z.ltb i j.
Definition int_gtb (i j: Z): bool := Z.gtb i j.
Definition int_lteb (i j: Z): bool := Z.leb i j.
Definition int_gteb (i j: Z): bool := Z.geb i j.

(* Sets *)

Definition set := list.

Notation "X 'union' Y" := (app X Y) (at level 60, right associativity).

Fixpoint set_equal_by
  {elt: Type} (eltord: elt -> elt -> ordering) (left right: set elt): bool :=
    match left with
      | [] =>
        match right with
          | [] => true
          | _  => false
        end
      | x::xs =>
        match right with
          | y::ys =>
            match eltord x y with
              | EQ => set_equal_by eltord xs right
              | _  => false
            end
          | _ => false
        end
    end.

Fixpoint set_member_by
  {elt : Type} (eltord: elt -> elt -> ordering) (e : elt) (s : set elt) : bool :=
    match s with
      | [] => false
      | x::xs =>
        match eltord x e with
          | EQ => true
          | _  => set_member_by eltord e xs
        end
    end.

Axiom set_compare_by:
  forall {elt: Type}, (elt -> elt -> ordering) -> set elt -> set elt -> ordering.

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

Definition set_any
  {elt : Type} (p : elt -> bool) (s : set elt) : bool :=
    List.existsb p s.

Definition set_for_all
  {elt : Type} (p : elt -> bool) (s : set elt) : bool :=
    List.forallb p s.

Fixpoint set_inter_by
  {elt : Type} (eltord : elt -> elt -> ordering)
  (left : set elt) (right : set elt) : set elt :=
    match left with
      | []    => []
      | x::xs =>
        if set_member_by eltord x right then
          x::set_inter_by eltord xs right
        else
          set_inter_by eltord xs right
    end.

Fixpoint set_union_by
  {elt : Type} (eltord: elt -> elt -> ordering)
  (left right : set elt): set elt :=
    match left with
      | [] => right
      | x::xs =>
        if set_member_by eltord x right then
          set_union_by eltord xs right
        else
          x::set_union_by eltord xs right
    end.

Fixpoint set_diff_by
  {elt : Type} (eltord: elt -> elt -> ordering)
  (left right : set elt): set elt :=
    match left with
      | [] => []
      | x::xs =>
          if set_member_by eltord x right then
            set_diff_by eltord xs right
          else
            x::set_diff_by eltord xs right
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

Fixpoint set_subset_by
  {elt : Type} (eltord : elt -> elt -> ordering)
  (left right : set elt): bool :=
    match left with
      | []    => true
      | x::xs =>
        if set_member_by eltord x right then
          set_subset_by eltord xs right
        else
          false
    end.

Definition set_proper_subset_by
  {elt: Type} (eltord: elt -> elt -> ordering)
  (left right: set elt): bool :=
    andb (set_subset_by eltord left right) (negb (set_equal_by eltord left right)).

Definition set_from_list
  {elt: Type} (s: list elt): set elt := s.

Definition set_to_list
  {elt: Type} (l: set elt): list elt := l.

Definition set_sigma
  {elt elt': Type} (sa: set elt) (f: elt -> set elt'): set (elt * elt') :=
    List.fold_right (fun x xys => List.fold_right (fun y xys => set_add (x, y) xys) xys (f x)) set_empty sa.

Program Definition set_choose_dependent
  {elt: Type} (s: set elt) (p: 0 < (List.length s)): elt :=
    match s return forall x, s = x -> 0 < List.length x -> elt with
      | [] => fun x => fun eq => fun p => _
      | x::xs => fun _ => fun _ => fun _ => x
    end s (eq_refl s) p.
  Obligation 1.
    compute in p0.
    case (Coq.Arith.Le.le_Sn_0 0).
    assumption.
  Defined.
    
(* XXX: made general enough so that when we swap from lists we can use the
        same function with minor editing.  Same above.  Also, try to remain
        close to the Lem implementation.
*)
Program Definition set_case_by
  {elt elt': Type} (eltord: elt -> elt -> ordering) (s: set elt)
  (empty: elt') (single: elt -> elt') (otherwise: elt'): elt' :=
    match s return forall x, s = x -> List.length s = List.length x -> elt' with
      | [] => fun _ _ _ => empty
      | [e] => fun x srefl lrefl => single (set_choose_dependent [e] _)
      | _  => fun _ _ _ => otherwise
    end s (eq_refl s) (eq_refl (List.length s)).

Axiom set_tc :
  forall {elt : Type},
  forall eq : elt -> elt -> bool,
  forall s : set (elt * elt),
    set (elt * elt).

(* Maps *)

Definition fmap (k v: Type) := list (k * v).

Fixpoint fmap_equal_by
  {k v: Type} (keq: k -> k -> bool) (veq: v -> v -> bool)
    (left right: fmap k v): bool :=
  match left with
    | [] =>
      match right with
        | [] => true
        | _  => false
      end
    | x::xs =>
        if list_member_by (fun kv kv' =>
          match kv, kv' with
            | (k, v), (k', v') => andb (keq k k') (veq v v')
          end) x right then
         fmap_equal_by keq veq xs right
        else
          false
  end.

Definition fmap_empty {k v: Type}: fmap k v := [].

Definition fmap_add {k v: Type} (key: k) (value: v) (map: fmap k v): fmap k v :=
  (key, value)::map.

Definition fmap_is_empty {k v: Type} (map: fmap k v): bool :=
  match map with
    | [] => true
    | _  => false
  end.

Fixpoint fmap_lookup_by
  {k v: Type} (kord: k -> k -> ordering) (key: k) (map: fmap k v): option v :=
    match map with
      | []    => None
      | keyvalue::xs =>
        let (key', value) := keyvalue in
        match kord key key' with
          | EQ => Some value
          | _  => fmap_lookup_by kord key xs
        end
    end.

Fixpoint fmap_all
  {k v: Type} (P: k -> v -> bool) (map: fmap k v): bool :=
    match map with
      | [] => true
      | x::xs =>
        let (key, value) := x in
          andb (P key value) (fmap_all P xs)
    end.

Fixpoint fmap_delete_by
  {k v: Type} (kord: k -> k -> ordering) (key: k) (map: fmap k v): fmap k v :=
    match map with
      | [] => []
      | x::xs =>
        let (key', value) := x in
        match kord key key' with
          | EQ => fmap_delete_by kord key xs
          | _  => x::fmap_delete_by kord key xs
        end
    end.

Fixpoint fmap_map
  {k v w: Type} (f: v -> w) (map: fmap k v): fmap k w :=
    match map with
      | [] => []
      | x::xs =>
        let (key, value) := x in
          (key, f value)::fmap_map f xs
    end.

Definition fmap_domain_by
  {k v: Type} (kord: k -> k -> ordering) (map: fmap k v): set k :=
    List.map (@fst k v) map.

Definition fmap_range_by
  {k v: Type} (vord: v -> v -> ordering) (map: fmap k v): set v :=
    List.map (@snd k v) map.

(* Strings *)

Definition char_equal
  (c d: ascii): bool :=
    match c, d with
      | (Ascii b1 b2 b3 b4 b5 b6 b7 b8), (Ascii b1' b2' b3' b4' b5' b6' b7' b8') =>
          andb (eqb b1 b1')
          (andb (eqb b2 b2')
          (andb (eqb b3 b3')
          (andb (eqb b4 b4')
          (andb (eqb b5 b5')
          (andb (eqb b6 b6')
          (andb (eqb b7 b7') (eqb b8 b8')))))))
    end.

Fixpoint string_equal
  (s t: string): bool :=
    match s, t with
      | EmptyString, EmptyString => true
      | (String hd tl), (String hd' tl') =>
          andb (char_equal hd hd') (string_equal tl tl')
      | _, _ => false
    end.

Fixpoint string_to_char_list
  (s: string): list ascii :=
    match s with
      | EmptyString => []
      | String hd tl => hd::string_to_char_list tl
    end.

Fixpoint string_from_char_list
  (chars: list ascii): string :=
    match chars with
      | [] => EmptyString
      | hd::tl => String hd (string_from_char_list tl)
    end.

Fixpoint string_make_string
  (m: nat) (char: ascii): string :=
    match m with
      | 0 => EmptyString
      | S m' => String char (string_make_string m' char)
    end.

(* Word. *)

Program Fixpoint bitSeqBinopAux
  (binop : bool -> bool -> bool) (s1 : bool) (bl1 : list bool) (s2 : bool) (bl2 : list bool) {measure (Coq.Init.Datatypes.length bl1 + Coq.Init.Datatypes.length bl2)} := 
  match ((bl1, bl2)) with 
    | ([],  []) => []
    | (b1 :: bl1',  []) => (binop b1 s2) :: bitSeqBinopAux binop s1 bl1' s2 []
    | ([],  b2 :: bl2') => (binop s1 b2) :: bitSeqBinopAux binop s1 []   s2 bl2'
    | (b1 :: bl1',  b2 :: bl2') => (binop b1 b2) :: bitSeqBinopAux binop s1 bl1' s2 bl2'
  end.
  Obligation 3.
    simpl. rewrite <- plus_n_Sm. auto.
  Defined.

Program Fixpoint boolListFromNatural
  (acc : list bool) (remainder : nat) {measure remainder} := 
  if (nat_gtb remainder 0) then 
   (boolListFromNatural ((beq_nat (Coq.Numbers.Natural.Peano.NPeano.modulo remainder 2) 1) :: acc) 
      (Coq.Numbers.Natural.Peano.NPeano.div remainder 2))
  else
    List.rev acc.
  Obligation 1.
    apply DAEMON. (* XXX: todo *)
  Defined.

(* Default values for incomplete pattern matching. *)

Definition bool_default: bool := false.
Definition nat_default: nat := 0.
Definition Z_default: Z := Z0.
Definition list_default {elt: Type}: list elt := [].
Definition set_default {elt: Type}: set elt := [].
Definition fmap_default {key value: Type}: fmap key value := [].
Definition string_default: string := ("" % string).
Definition sum_default {left right: Type}: sum left right := inl (DAEMON (a:=left)).
Definition unit_default: unit := tt.
Definition maybe_default {elt: Type}: option elt := None.
