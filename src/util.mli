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

(** Mixed useful things *)
module Duplicate(S : Set.S) : sig 
  type dups = 
    | No_dups of S.t
    | Has_dups of S.elt
  val duplicates : S.elt list -> dups
end

(** [remove_duplicates l] removes duplicate elements from
    the list l. The elements keep there original order. The first
    occurence of an element is kept, all others deleted. *)
val remove_duplicates : 'a list -> 'a list

(** [remove_duplicates_gen p l] removes duplicate elements from
    the list l. It is a generalised version of [remove_duplicates] where
    the equality check is performed by [p]. *)
val remove_duplicates_gen : ('a -> 'a -> bool) -> 'a list -> 'a list

(** [get_duplicates l] returns the elements that appear multiple times
    in the list l. *)
val get_duplicates : 'a list -> 'a list

(** [get_duplicates_gen p l] returns the elements that appear multiple times
    in the list l. It is a generalised version of [get_duplicates] where
    the equality check is performed by [p]. *)
val get_duplicates_gen : ('a -> 'a -> bool) -> 'a list -> 'a list


(** {2 Option Functions} *)

(** [option_map f None] returns [None], whereas
    [option_map f (Some x)] returns [Some (f x)]. *)
val option_map : ('a -> 'b) -> 'a option -> 'b option

(** [option_cases None f_s f_n] returns [f_n], whereas
    [option_cases (Some x) f_s f_n] returns [f_s x]. *)
val option_cases : 'a option -> ('a -> 'b) -> (unit -> 'b) -> 'b

(** [option_bind f None] returns [None], whereas
    [option_bind f (Some x)] returns [f x]. *)
val option_bind : ('a -> 'b option) -> 'a option -> 'b option

(** [option_default d None] returns the default value [d], 
    whereas [option_default d (Some x)] returns [x]. *)
val option_default : 'a -> 'a option -> 'a

(** [option_default_map v d f] is short for 
    [option_default d (option_map f v)]. This means that
    [option_default_map None d f] returns [d], whereas
    [option_default_map (Some x) d f] returns [f x]. *)
val option_default_map : 'a option -> 'b -> ('a -> 'b) -> 'b

(** [option_get_exn exn None] throws the exception [exn],
    whereas [option_get_exn exn (Some x)] returns [x]. *)
val option_get_exn : exn -> 'a option -> 'a

(** [changed2 f g x h y] applies [g] to [x] and [h] to [y].
    If both function applications return [None], then [None] is
    returned. Otherwise [f] is applied to the results. For this
    application of [f], [x] is used in case [g x] returns [None] and
    similarly [y] in case [h y] returns [None]. *)
val changed2 : ('a -> 'b -> 'c) -> ('a -> 'a option) -> 'a -> ('b -> 'b option) -> 'b -> 'c option
                                              
(** [option_repeat f x] applies [f] to [x] till nothings changes any more. This means
    that if [f x] is [None], [x] is returned. Otherwise [option_repeat] calls itself recursively on the
    result of [f x]. *)
val option_repeat : ('a -> 'a option) -> 'a -> 'a


(** {2 List Functions} *)

(** [list_index p l] returns the first index [i] such that
    the predicate [p (l!i)] holds. If no such [i] exists,
    [None] is returned. *)
val list_index: ('a -> bool) -> 'a list -> int option

(** [list_subset l1 l2] tests whether all elements of [l1] also
    occur in [l2]. *)
val list_subset : 'a list -> 'a list -> bool

(** [list_diff l1 l2] removes all elements from [l1] that occur in [l2]. *)
val list_diff : 'a list -> 'a list -> 'a list

(** [list_longer n l] checks whether the list [l] has more than [n] elements.
    It is equivalent to [List.length l > n], but more efficient, as it aborts counting,
    when the limit is reached. *)
val list_longer : int -> 'a list -> bool

(** [list_null l] checks whether the list [l] is empty, i.e. if [l = []] holds. *)
val list_null : 'a list -> bool

(** [option_first f l] searches for the first element [x] of [l] such
    that the [f x] is not [None]. If such an element exists, [f x] is
    returned, otherwise [None]. *)
val option_first: ('a -> 'b option) -> 'a list -> 'b option

(** [map_changed f l] maps [f] over [l].
    If for all elements of [l] the
    function [f] returns [None], then [map_changed f l] returns [None].
    Otherwise, it uses [x] for all elements, where [f x] returns [None],
    and returns the resulting list. *)   
val map_changed : ('a -> 'a option) -> 'a list -> 'a list option

(** [map_changed_default d f l] maps [f] over [l].
    If for all elements of [l] the
    function [f] returns [None], then [map_changed f l] returns [None].
    Otherwise, it uses [d x] for all elements [x], where [f x] returns [None],
    and returns the resulting list. *)   
val map_changed_default : ('a -> 'b) -> ('a -> 'b option) -> 'a list -> 'b list option

(** [list_mapi f l] maps [f] over [l]. In contrast to the standard
    [map] function, [f] gets the current index of the list as an extra
    argument. Counting starts at [0]. *)
val list_mapi : (int -> 'a -> 'b) -> 'a list -> 'b list

(** [list_iter_sep sf f [a1; ...; an]] applies function [f] in turn to [a1; ...; an] and
    calls [sf ()] in between. It is equivalent to [begin f a1; sf(); f a2; sf(); ...; f an; () end]. *)
val list_iter_sep : (unit -> unit) -> ('a -> unit) -> 'a list -> unit 

(** [intercalate sep as] inserts [sep] between the elements of [as], i.e. it returns a list of the form
     [a1; sep; ... sep ; an]. *)
val intercalate : 'a -> 'a list -> 'a list

(** [interleave l1 l2] interleaves lists [l1] and [l2], by alternatingly taking an element of l1 and l2 
    till one of the lists is empty. Then the remaining elements are added. The first element is from [l1]. *) 
val interleave : 'a list -> 'a list -> 'a list

(** [replicate n e] creates a list that contains [n] times the element [e]. *)
val replicate : int -> 'a -> 'a list

(** [map_filter f l] maps [f] over [l] and removes all entries [x] of [l]
    with [f x = None]. *)
val map_filter : ('a -> 'b option) -> 'a list -> 'b list

(** [map_all f l] maps [f] over [l]. If at least one entry is [None], [None] is returned. Otherwise,
    the [Some] function is removed from the list. *)
val map_all : ('a -> 'b option) -> 'a list -> 'b list option

(** [list_to_front i l] resorts the list [l] by bringing the element at index [i]
    to the front. 
    @throws Failure if [i] is not smaller than the length of [l]*)
val list_to_front : int -> 'a list -> 'a list

(** [undo_list_to_front i l] resorts the list [l] by moving the head element to index index [i]
    It's the inverse of [list_to_front i l]. *)
val undo_list_to_front : int -> 'a list -> 'a list

(** [split_after n l] splits the first [n] elemenst from list [l], i.e. it returns two lists
    [l1] and [l2], with [length l1 = n] and [l1 @ l2 = l]. Fails if n is too small or large. *)
val split_after : int -> 'a list -> 'a list * 'a list

(** [list_fristn n l] gets the first [n] elemenst from list [l], i.e. it does the same as
    [fst (split_after n l)]. It fails if n is too small or large. *)
val list_firstn : int -> 'a list -> 'a list 

(** [list_dropn n l] drops the first [n] elemenst from list [l], i.e. it does the same as
    [snd (split_after n l)]. It fails if n is too small or large. *)
val list_dropn : int -> 'a list -> 'a list

(** [list_dest_snoc l] splits the last entry off a list. This mean
    that [list_dest_snoc (l @ [x])] returns [(l, x)]. It raises a
    [Failure "list_dest_snoc"] exception, if the list [l] is empty. *)
val list_dest_snoc : 'a list -> 'a list * 'a

(** [list_pick p l] tries to pick the first element from [l] that satisfies predicate [p].
    If such an element is found, it is returned together with the list [l] where this
    element has been removed. *)
val list_pick : ('a -> bool) -> 'a list -> ('a * 'a list) option


val compare_list : ('a -> 'b -> int) -> 'a list -> 'b list -> int


(** {2 Files} *)

(** [copy_file src dst] copies file [src] to file [dst]. Only files are supported,
    no directories. *)
val copy_file : string -> string -> unit

(** [move_file src dst] moves file [src] to file [dst]. In contrast to [Sys.rename] no error is
    produced, if [dst] already exists. Moreover, in case [Sys.rename] fails for some reason (e.g. because
    it does not work over filesystem boundaries), [copy_file] and [Sys.remove] are used as
    fallback. *)
val move_file : string -> string -> unit

(** [same_content_files file1 file2] checks, whether the files [file1] and [file2] have the same content.
If at least one of the files does not exist, [false] is returned. [same_content_files] throws an exception,
if one of the files exists, but cannot be read. *)
val same_content_files : string -> string -> bool

(** [absolute_dir dir] tries to get the absolute path name of directory [dir]. If this fails (usually, 
    because [dir] does not exist), [None] is returned. *)
val absolute_dir : string -> string option

(** [dir_eq d1 d2] uses [absolute_dir] to check whether the two directories are equal. *)
val dir_eq : string -> string -> bool

(** {2 Strings} *)

(** [string_to_list l] translates the string [l] to the list of its characters. *)
val string_to_list : string -> char list

(** [string_for_all p s] checks whether all characters of [s] satisfy [p]. *)
val string_for_all : (char -> bool) -> string -> bool

(** [is_simple_ident_string s] checks whether [s] is a "simple" identifier. The meaning of
    simple is fuzzy. Essentially it means that [s] can be used by all backends. Currently the
    restricting is that [s] is non-empty, starts with a letter and contains only letters, numbers
    and underscores. *)
val is_simple_ident_string : string -> bool

(** [is_simple_char c] checks whether [c] is an easily printable
    character. Currently these are the characters which Isabelle's
    parser and pretty-printer supports. This decision was taken, because Isabelle is the most
    restrictive of our backend. It might be revised at any point.

    The user can rely on that [is_simple_char] only accepts chars that need no escaping for any backend.
    These are simple letters (A-Z, a-z), digits (0-9) and a few selected special chars (space, parenthesis,
    punctuation ... ) *)
val is_simple_char : char -> bool

(** [string_split c string] splits the string into a list of strings on occurences of the char [c].
    The last remaining string is handed out separately. This encodes, that the resulting string list
    is never empty *)
val string_split : char -> string -> (string list * string)

(** [is_uppercase c] returns true if c is between A and Z *)
val is_uppercase : char -> bool

(** [is_lowercase c] returns true if c is between a and z *)
val is_lowercase : char -> bool

(** [uncapitalize_prefix n] tries to uncapitalize the first few letters of [n].
    In contrast to [uncapitalize], it continues with the next letter,
    till a non-uppercase letter is found. The idea is to produce nicer looking names when
    uncaptalizing. Turning [UTF8.lem] into [uTF8Script.sml] for example is strange and
    [utf8Script.sml] looks nicer. *)
val uncapitalize_prefix : string -> string

(** [string_map f s] maps [f] over all characters of a copy of [s]. It corresponds to [String.map], which
    is unluckily only available for OCaml 4 *)
val string_map : (char -> char) -> string -> string

(** [message_singular_plural (sing_message, multiple_message) l] is used
    to determine whether the singular or plural form should be used in messages. If the list [l] contains
    no elements or exactly one element, [sing_message] is returned. Otherwise, i.e. for multiple elements,
    the result is [multiple_message]. *)
val message_singular_plural : (string * string) -> 'a list -> string

(** [fresh_string forbidden] generates a stateful function [gen_fresh] that generates fresh strings. [gen_fresh s] 
    will return a string similar to [s] that has never been returned before and is not part of [forbidden]. By storing
    the result in internal state, it is ensured that the same result is never returned twice. This function is used
    for example to generate unique labels. *)
val fresh_string : string list -> (string -> string)

(** [unescaped] is the same [Scanf.unescaped] --- used for
 * backwards-compatibility with OCaml 3.12 *)
val unescaped : string -> string

(** [memo_rec f] returns a memoized version of the function [f] *)
val memo_rec : (('a -> 'b) -> 'a -> 'b) -> 'a -> 'b

(** {2 Useful Sets} *)

(** Sets of Integers *)
module StringSet : Set.S with type elt = string
module IntSet : Set.S with type elt = int
module IntIntSet : Set.S with type elt = int * int

(** Some useful extra functions for sets *)
module ExtraSet : functor (S : Set.S) ->
   sig
     (** Add a list of values to an existing set. *)
     val add_list : S.t -> S.elt list -> S.t

     (** Removes a list of values to an existing set. *)
     val remove_list : S.t -> S.elt list -> S.t

     (** Construct a set from a list. *)
     val from_list : S.elt list -> S.t

     (** Builds the union of a list of sets  *)
     val list_union : S.t list -> S.t

     (** Builds the intersection of a list of sets.
         If the list is empty, a match exception is thrown. *)
     val list_inter : S.t list -> S.t
   end

(** [rev_flatten xs] reverses and then flattens [xs], a list of lists.  Key property:
      rev_flatten (rev_map f xs) = flatten (map f xs)
  *)
val rev_flatten : 'a list list -> 'a list
