(**************************************************************************)
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
(**************************************************************************)

let option_map f = function
  | None -> None
  | Some(o) -> Some(f o)

type ('a,'s) t = 's option * ('a * 's) list * 'a option

let filter p (opt, list, opt') =
  (opt, List.filter (fun (fst, snd) -> p fst) list,
    Util.option_bind (fun x -> if p x then Some x else None) opt')
;;

let empty = (None, [], None)

let is_empty = function
  | (_, [], None) -> true
  | _ -> false

let hd l =
  match l with
    | (_,(x,_)::_,_) -> x
    | (_,[],Some(x)) -> x
    | _ -> raise (Failure "Seplist.hd")

let hd_sep l = match l with
  | (Some(s),_,_) -> s
  | (None,(_,s)::_,_) -> s
  | _ -> raise (Failure "Seplist.hd_sep")

let tl l = match l with
  | (None, (x,s)::rest, e) ->
      (Some(s),rest,e)
  | (None, [], Some(x)) ->
      (None,[],None)
  | _ -> raise (Failure "Seplist.tl")

let tl_alt l = match l with
  | (_, (x,s)::rest, e) ->
      (Some(s),rest,e)
  | (_, [], Some(x)) ->
      (None,[],None)
  | _ -> raise (Failure "Seplist.tl_alt")

let tl_sep l = match l with
  | (Some(s), l, e) ->
      (None,l,e)
  | _ -> raise (Failure "Seplist.tl_sep")

let replace_all_seps ns (so, l, e) = 
  (Util.option_map ns so, List.map (fun (x, s) -> (x, ns s)) l, e)

let append d l1 l2 = match (l1, l2) with
  | ((o11, l1, None), (_, l2, o22)) ->
    (o11, l1 @ l2, o22)
  | ((o11, l1, Some x), (Some y, l2, o22)) ->
    (o11, l1 @ (x, y) :: l2, o22)
  | ((o11, l1, Some x), (None, [], None)) ->
    (o11, l1, Some x)
  | ((o11, l1, Some x), (None, l2, o22)) ->
    (o11, l1 @ (x, d) :: l2, o22)

let rec flatten d sll = match sll with
  | [] -> empty
  | (x :: xs) -> append d x (flatten d xs)

let to_list (_,l,o) = 
  let l = List.map fst l in
    match o with
      | None -> l
      | Some(x) -> l @ [x]

let to_pair_list default_s (o1,l,o2) = 
    match o2 with
      | None -> (o1, l)
      | Some(x) -> (o1, l @ [(x, default_s)])

let from_pair_list o1 l o2 = (o1, l, o2)

let from_pair_list_sym o1 l o2 = 
  let rec aux a0 l = 
    match l with 
      | [] -> begin
          match o2 with 
            | None -> ([], Some a0)
            | Some s -> ([(a0,s)], None)
        end
      | (s,a)::l' -> let (l'', o2') = aux a l' in
          ((a0,s) :: l'', o2')
  in
  match l with 
    | [] -> begin
              match (o1, o2) with
                | (Some a, Some s) -> (None, [(a,s)], None)
                | _ -> (o2, [], o1)
            end
    | (s0,a1)::l' -> let (l'', o2') = aux a1 l' in begin
                 match o1 with None -> (Some s0, l'', o2')
                             | Some a0 -> (None, (a0, s0)::l'', o2') 
                 end

let drop_first_sep (o1, l, o2) = (o1, (None, l, o2))

let to_list_map f (_,l,o) =
  let l = List.map (fun x -> f (fst x)) l in
   match o with
     | None -> l
     | Some(x) -> l @ [f x] 

let iter f (_,l,o) =
  List.iter (fun x -> f (fst x)) l;
  match o with
    | None -> ()
    | Some(x) -> f x 

let rec tsl_help f g = function
  | [] -> []
  | (x,y)::l -> f x :: g y :: tsl_help f g l

let to_sep_list f g (o1,l,o2) = 
  let l1 = tsl_help f g l in
  let l2 = 
    match o2 with
      | None -> l1
      | Some(x) -> l1 @ [f x]
  in
    match o1 with 
      | None -> l2
      | Some(x) -> g x :: l2

type ('s,'a) optsep = Optional | Require of 's | Forbid of ('s -> 'a)

let to_sep_list_first o f g (o1,l,o2) =
  match (o,o1) with
    (* Leave the list as is *)
    | (Optional, _) -> to_sep_list f g (o1,l,o2)
    (* Use add_first to make a new initial separator *)
    | (Require(s), None) -> to_sep_list f g (Some(s),l,o2)
    (* Leave the existing initial separator alone *)
    | (Require _, Some _) -> to_sep_list f g (o1,l,o2)
    (* Leave the list as is *)
    | (Forbid(g'), None) -> to_sep_list f g (o1,l,o2)
    (* Remove the initial separator, using g' *)
    | (Forbid(g'),Some(o1)) -> g' o1 :: to_sep_list f g (None, l, o2)

let to_sep_list_last o f g (o1,l,o2) =
  match (o,o2) with
    (* Leave the list as is *)
    | (Optional, _) -> to_sep_list f g (o1,l,o2)
    (* Leave the existing final separator *)
    | (Require _, None) -> to_sep_list f g (o1, l, o2)
    (* Use add_last to make a new final separator *)
    | (Require(s), Some(x)) -> to_sep_list f g (o1, l @ [(x,s)], None)
    (* Leave the list as is *)
    | (Forbid(g'), Some _) -> to_sep_list f g (o1, l, o2)
    (* Remove the existing final separator *)
    | (Forbid(g'), None) -> 
        begin
          match List.rev l with 
            | [] -> 
                begin
                  match o1 with
                    | None -> []
                    | Some(s) -> [g' s]
                end
            | (x,s)::rest -> 
                to_sep_list f g (o1, List.rev rest, Some(x)) @ [g' s]
        end

let map f (o1,l,o2) =
  (o1, List.map (fun (x,y) -> (f x, y)) l, option_map f o2)

let cons_sep x (o1,l,o2) =
  match o1 with
    | None ->
        (Some(x), l, o2)
    | Some _ ->
        assert false

let cons_sep_alt x = function
  | (None,[],None) -> (None,[],None)
  | (o1,l,o2) -> cons_sep x (o1,l,o2)

let cons_entry x = function
  | (None, [], None) ->
      (None, [], Some(x))
  | (Some(y), l, o) ->
      (None, (x,y)::l, o)
  | (None, a::b, _) ->
      assert false
  | (None, [], Some _) ->
      assert false

let sing x = (None, [], Some x)
  

let length (_,l,o2) =
  List.length l 
  + 
  begin
    match o2 with 
      | None -> 0
      | Some _ -> 1
  end

let map_changed (f : 'a -> 'a option) ((o1,l,o2) : ('a,'s) t) : ('a,'s) t option =
  let rec g = function
    | [] -> ([],false)
    | (x,s)::y ->
        let (r,c) = g y in
          match f x with
            | None -> ((x,s)::r,c)
            | Some(x') -> ((x',s)::r,true)
  in
  let (r,c) = g l in
  let (r',c') = 
    match o2 with
      | None -> (None, false)
      | Some(x) ->
          begin
            match f x with
              | None -> (Some(x), false)
              | Some(x) -> (Some(x), true)
          end
  in
    if c || c' then
      Some(o1,r,r')
    else
      None

let rec from_list = function
  | [] -> (None, [], None)
  | [(x,y)] -> (None, [], Some x)
  | (x,y) :: l ->
      let (o1,l,o2) = from_list l in
        (o1,(x,y)::l,o2)

let from_list_default d l =
  from_list (List.map (fun x -> (x, d)) l)

let from_list_prefix s b l =
  let (o1,l,o2) = from_list l in
    if b then
      (Some(s),l,o2)
    else
      (o1,l,o2)

let rec fls_help s = function
  | [] -> (Some(s),[],None)
  | [(x,y)] -> (None,[(x,s)],None)
  | (x,y)::l -> 
      let (o1,l,o2) = fls_help s l in
        (o1,(x,y)::l,o2)

let from_list_suffix l s b = 
  if not b then
    from_list l
  else
    fls_help s l

let map_acc_right f base_acc (o1,l,o2) =
  let (new_o2, new_acc) =
    match o2 with
      | None -> (None, base_acc)
      | Some(v) -> 
          let (x,y) = f v base_acc in
            (Some(x), y)
  in
  let (new_l,new_acc) =
    List.fold_right
      (fun (v,s) (l,acc) ->
         let (p,a) = f v acc in
           ((p,s)::l, a))
      l
      ([], new_acc) 
  in
    ((o1, new_l, new_o2), new_acc)

let map_acc_left f base_acc (o1,l,o2) =
  let (new_l,new_acc) =
    List.fold_left
      (fun (l,acc) (v,s) ->
         let (p,a) = f v acc in
           ((p,s)::l, a))
      ([], base_acc)
      l
  in
  let (new_o2, new_acc) =
    match o2 with
      | None -> (None, new_acc)
      | Some(v) -> 
          let (x,y) = f v new_acc in
            (Some(x), y)
  in
    ((o1, List.rev new_l, new_o2), new_acc)

let fold_left f base_acc sl =
  snd (map_acc_left (fun a c -> ((), f a c)) base_acc sl)

let fold_right f base_acc sl =
  snd (map_acc_right (fun a c -> ((), f a c)) base_acc sl)

let for_all f (o1,l,o2) =
  let rec help l = match l with
    | [] -> true
    | (x,_)::l -> f x && help l
  in
    match o2 with 
      | None -> help l
      | Some(x) -> help l && f x

let exists f (o1,l,o2) =
  let rec help l = match l with
    | [] -> false
    | (x,_)::l -> f x || help l
  in
    match o2 with 
      | None -> help l
      | Some(x) -> help l || f x

let find default_s f (o1,l,o2) =
  let rec help l = match l with
    | [] -> None
    | (x,s)::l -> if f x then Some (x,s) else help l
  in
    match help l with 
      | None -> (match o2 with 
         | None -> raise Not_found 
         | Some x -> if (f x) then (x, default_s) else raise Not_found)
      | Some(x,s) -> (x,s)

let rec pp f g ppf (fst_sep, lst, last_el) = 
  begin  
    match fst_sep with
      | None -> ()
      | Some(s) -> g ppf s
  end;
  Pp.lst "" (fun ppf (e,s) -> f ppf e; g ppf s) ppf lst;
  begin  
    match last_el with
      | None -> ()
      | Some(e) -> f ppf e
  end


