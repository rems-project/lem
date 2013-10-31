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

let ordering_cases r lt eq gt =  
  (if (r < 0) then lt else
   if (r = 0) then eq else gt)

let orderingEqual r1 r2 = 
  ordering_cases r1 (orderingIsLess r2) (orderingIsEqual r2) (orderingIsGreater r2)



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

let option_bind f = function
  | Some a -> f a
  | None   -> None

