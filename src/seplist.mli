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

(** general thing of lists with optional separators *)

type ('a,'s) t

val empty : ('a,'s) t
val cons_sep : 's -> ('a,'s) t -> ('a,'s) t

(** [cons_sep_alt] doesn't add the separator if the list is empty *)
val cons_sep_alt : 's -> ('a,'s) t -> ('a,'s) t
val cons_entry : 'a -> ('a,'s) t -> ('a,'s) t

val is_empty : ('a,'s) t -> bool

(** [sing a] constructs a seplist with entry [a]. It does the same as
    [cons_entry a empty]. *)
val sing : 'a -> ('a, 's) t

(** gets the first entry, if there is one *)
val hd : ('a,'s) t -> 'a

(** gets the first seperator, if there is one *)
val hd_sep : ('a,'s) t -> 's

(** Removes the first entry, fails is there is none, or if a separator is
    first *)
val tl : ('a,'s) t -> ('a,'s) t

(** Removes the first entry, fails is there is none, removes any separator that
    precedes the first entry *)
val tl_alt : ('a,'s) t -> ('a,'s) t

(** Removes the first separator, fails is there is none, or if an entry
    is first *)
val tl_sep : ('a,'s) t -> ('a,'s) t

(** [append d sl1 sl2] appends the seplists [sl1] and [sl2]. If
    [sl1] ends with a value and [sl2] starts with a value, a default
    separator [s] is added. If [sl1] ends with a separator and [sl2] starts
    with a separator, the seperator of [sl2] is dropped. *)
val append : 's -> ('a,'s) t ->  ('a,'s) t ->  ('a,'s) t

(** [flatten d sll] flattens a list of seplists by applying [append]
    repeatedly *)
val flatten : 's -> ('a,'s) t list ->  ('a,'s) t 

(** Makes a normal list, ignoring separators *)
val to_list : ('a,'s) t -> 'a list

(** Makes a normal list of pairs. The first separator is returned separately, an
    default one added for the last entry, if the lists ends with a value *)
val to_pair_list : 's -> ('a,'s) t -> ('s option * ('a * 's) list)

(** constructs a seplist from a list of pairs. In contrast to from_list, the
    last separator is kept *)
val from_pair_list : 's option -> ('a * 's) list -> 'a option -> ('a, 's) t

(** [from_pair_list_sym first_val_opt sep_val_list last_sep_opt] 
    constructs a seplist from a list of pairs [sep_val_list]. In contrast to [from_pair_list], 
    the separator is the first component of these pairs. This also means that
    we now need an optional first value before the list and an optional last separator after the list,
    whereas from_pair_list has an optional first separator and last value. *)
val from_pair_list_sym : 'a option -> ('s * 'a) list -> 's option -> ('a, 's) t

(** If [sl] starts with a seperator, it is dropped and returned, otherwise nothing happens. *)
val drop_first_sep : ('a, 's) t -> 's option * ('a, 's) t

(** Flattens into a normal list with separators and elements intermixed *)
val to_sep_list : ('a -> 'b) -> ('s -> 'b) -> ('a,'s) t -> 'b list

type ('s,'a) optsep = Optional | Require of 's | Forbid of ('s -> 'a)

(** Flattens into a normal list with separators and elements intermixed, with
    special control over the first separator.  Optional indicates no special
    treatment (works as to_sep_list), Require adds the given initial separator if
    there is none, and Forbid removes the initial separator if there is one.  In
    the latter case, the initial separator is processed by the function argument
    to Forbid *)
val to_sep_list_first : ('s,'b) optsep -> ('a -> 'b) -> ('s -> 'b) -> ('a,'s) t
-> 'b list

(** As to_sep_list_first, but for the last separator *)
val to_sep_list_last : ('s,'b) optsep -> ('a -> 'b) -> ('s -> 'b) -> ('a,'s) t
-> 'b list

val to_list_map : ('a -> 'b) -> ('a,'s) t -> 'b list
val iter : ('a -> unit) -> ('a,'s) t -> unit

(** The from list functions ignore the last separator in the input list *)
val from_list : ('a * 's) list -> ('a,'s) t
val from_list_prefix : 's -> bool -> ('a * 's) list -> ('a,'s) t
val from_list_suffix : ('a * 's) list -> 's -> bool -> ('a,'s) t

(** [from_list_default d l] constructs a seplist form a list of entries [l] using
    the separator [d] as default separator between all entries. *)
val from_list_default : 's -> 'a list -> ('a,'s) t

(** [filter p s] filters all elements of the seplist [s] that satisfy the predicate
    [p], dropping the rest.
  *)
val filter : ('a -> bool) -> ('a, 's) t -> ('a, 's) t

val length : ('a,'s) t -> int

val map : ('a -> 'b) -> ('a,'s) t -> ('b, 's) t

(** Returns None if the function returns None on all of the elements, otherwise
    returns a list that uses the original element where the function returns None
*)
val map_changed : ('a -> 'a option) -> ('a,'s) t -> ('a,'s) t option

(** Maps with an accumulating parameter.  The _right version builds the
    accumulator right-to-left, and the _left version builds it left-to-right. *)
val map_acc_right : ('a -> 'c -> 'b * 'c) -> 'c -> ('a, 's) t -> ('b, 's) t * 'c

val map_acc_left : ('a -> 'c -> 'b * 'c) -> 'c -> ('a, 's) t -> ('b, 's) t * 'c

(** fold right implemented via [map_acc_right] *)
val fold_right : ('a -> 'c -> 'c) -> 'c -> ('a, 's) t -> 'c

(** fold left implemented via [map_acc_left] *)
val fold_left : ('a -> 'c -> 'c) -> 'c -> ('a, 's) t -> 'c

val for_all : ('a -> bool) -> ('a,'s) t -> bool
val exists : ('a -> bool) -> ('a,'s) t -> bool
val find : 's -> ('a -> bool) -> ('a,'s) t -> ('a * 's)

val pp : (Format.formatter -> 'a -> unit) -> (Format.formatter -> 'b -> unit) -> Format.formatter -> ('a,'b) t -> unit
                                                                           
val replace_all_seps : ('s -> 's) -> ('a, 's) t -> ('a, 's) t
