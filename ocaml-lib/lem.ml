(* ========================================================================== *)
(* Tuples                                                                     *)
(* ========================================================================== *)


let pair_equal eq1 eq2 (a1, b1) (a2, b2) =
  (eq1 a1 a2) && (eq2 b1 b2)

let pair_swap (v1, v2) = (v2, v1)

let curry f v1 v2 = f (v1, v2)

let uncurry f (v1, v2) = f v1 v2

(* ========================================================================== *)
(* Orderings                                                                  *)
(* ========================================================================== *)

let orderingIsLess r = (r < 0)
let orderingIsGreater r = (r > 0)
let orderingIsEqual r = (r = 0)

let ordering_cases (r : int) (lt : 'a) (eq : 'a) (gt : 'a) : 'a =  
  (if (r < 0) then lt else
   if (r = 0) then eq else gt)

let orderingEqual r1 r2 = 
  ordering_cases r1 (orderingIsLess r2) (orderingIsEqual r2) (orderingIsGreater r2)


(* ========================================================================== *)
(* Lists                                                                      *)
(* ========================================================================== *)


let list_null = function
  | [] -> true
  | _ -> false

let rec lexicographic_compare cmp l1 l2 : int = (match (l1,l2) with
  | ([], []) -> 0
  | ([], _::_) -> -1
  | (_::_, []) -> 1
  | (x::xs, y::ys) -> begin  
       ordering_cases (cmp x y) (-1) (lexicographic_compare cmp xs ys) (1)
    end
)

let rec lexicographic_less less less_eq l1 l2 = ((match (l1,l2) with
  | ([], []) -> false
  | ([], _::_) -> true
  | (_::_, []) -> false
  | (x::xs, y::ys) -> ((less x y) || ((less_eq x y) && (lexicographic_less less less_eq xs ys)))
))

let rec lexicographic_less_eq less less_eq l1 l2 = ((match (l1,l2) with
  | ([], []) -> true
  | ([], _::_) -> true
  | (_::_, []) -> false
  | (x::xs, y::ys) -> (less x y || (less_eq x y && lexicographic_less_eq less less_eq xs ys))
))

let rec list_index l n = (match l with 
  | []      -> None
  | x :: xs -> if n = 0 then (Some x) else list_index xs (n - 1)
)


(* ========================================================================== *)
(* Options                                                                    *)
(* ========================================================================== *)

let is_none = function
  | None -> true
  | Some _ -> false

let is_some = function
  | None -> false
  | Some _ -> true

let option_case d f mb = (match mb with 
  | Some a -> f a
  | None   -> d
)

let option_default d = function
  | Some a -> a
  | None   -> d

let option_map f = function
  | Some a -> Some (f a)
  | None   -> None

let option_bind m f =
  match m with
    | Some a -> f a
    | None   -> None

let option_equal eq o1 o2 = match (o1, o2) with
  | (None, None)       -> true
  | (None, Some _)     -> false
  | (Some _,  None)    -> false
  | (Some x1, Some x2) -> eq x1 x2


(* ========================================================================== *)
(* Machine words                                                              *)
(* ========================================================================== *)

(* In OCaml we represent bitvectors as a length (so that only the
   creation operations need a length parameter) and in-range bignum. *)

type mword = int * Nat_big_num.num

let machine_word_inject (n,w) = (n,Big_int_impl.BI.extract_big_int w 0 n)

let word_length (n,_) = n

let word_concat (n1,w1) (n2,w2) =
  (n1+n2, Nat_big_num.add (Big_int_impl.BI.shift_left_big_int w1 n2) w2)

let word_extract lo hi (n,w) =
  let sz = hi-lo+1 in
  (sz, Big_int_impl.BI.extract_big_int w lo sz)

let word_update (n,v) lo hi (_,w) =
  let old = Big_int_impl.BI.extract_big_int v lo (hi-lo+1) in
  let old = Big_int_impl.BI.shift_left_big_int old lo in
  let removed = Nat_big_num.sub v old in
  (n, Nat_big_num.add removed (Big_int_impl.BI.shift_left_big_int w lo))

let word_uminus (n,w) =
  let lim = Big_int_impl.BI.shift_left_big_int Big_int_impl.BI.unit_big_int n in
  (n,Nat_big_num.sub lim w)

let naturalFromWord (_,w) = w

let word_bin_arith f (n,x) ((_:int),y) =
  let w = f x y in
  (n, Big_int_impl.BI.extract_big_int w 0 n)

let word_plus = word_bin_arith Nat_big_num.add
let word_minus = word_bin_arith Nat_big_num.sub
let word_times = word_bin_arith Nat_big_num.mul
let word_udiv (n,x) (_,y) = (n, Nat_big_num.div x y)
let word_mod (n,x) (_,y) = (n, Nat_big_num.modulus x y)
