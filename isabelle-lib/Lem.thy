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

header{* Mappings of Syntax needed by Lem *}

theory "Lem" 

imports 
 	 Main
 	 LemExtraDefs
   "~~/src/HOL/Map"
 	 "~~/src/HOL/Library/Efficient_Nat"

begin 

subsection{* Finite Maps *}

abbreviation (input) "map_find k m \<equiv> the (m k)"
abbreviation (input) "map_update k v m \<equiv> m (k \<mapsto> v)"

subsection{* Lists *}

abbreviation (input) "list_mem e l \<equiv> (e \<in> set l)"
abbreviation (input) "list_forall P l \<equiv> (\<forall>e\<in>set l. P e)"
abbreviation (input) "list_exists P l \<equiv> (\<exists>e\<in>set l. P e)"
abbreviation (input) "list_unzip l \<equiv> (map fst l, map snd l)"

subsection{* Sets *}

abbreviation (input) "set_diff (s1::'a set) s2 \<equiv> s1 - s2"
abbreviation (input) "set_filter P (s::'a set) \<equiv> {x \<in> s. P x}"
abbreviation (input) "set_cross s1 s2 \<equiv> s1 \<times> s2"


subsection{* Natural numbers *}

abbreviation (input) "nat_exp (n1::nat) (n2::nat) \<equiv>  n1 ^ n2"
abbreviation (input) "nat_mod (n1::nat) (n2::nat) \<equiv>  n1 mod n2"


subsection{* Integers *}

abbreviation (input) "int_add (i1::int) (i2::int) \<equiv> i1 + i2"
abbreviation (input) "int_sub (i1::int) (i2::int) \<equiv> i1 - i2"
abbreviation (input) "int_mul (i1::int) (i2::int) \<equiv> i1 * i2"
abbreviation (input) "int_div (i1::int) (i2::int) \<equiv> i1 div i2"
abbreviation (input) "int_mod (i1::int) (i2::int) \<equiv> i1 mod i2"
abbreviation (input) "int_exp (i::int) (n::nat) \<equiv>  i ^ n"

abbreviation (input) "int_lt (i1::int) (i2::int) \<equiv> i1 < i2"
abbreviation (input) "int_le (i1::int) (i2::int) \<equiv> i1 \<le> i2"
abbreviation (input) "int_gt (i1::int) (i2::int) \<equiv> i1 > i2"
abbreviation (input) "int_ge (i1::int) (i2::int) \<equiv> i1 \<ge> i2"

abbreviation (input) "int_neg (i::int) \<equiv> -i"


subsection {* Dummy *}

definition bitwise_xor :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "bitwise_xor x y = undefined"

definition num_asr :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "num_asr n m = undefined"

definition num_lsl :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "num_lsl n m = undefined"

definition bitwise_or :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "bitwise_or n m = undefined"

definition bitwise_not :: "nat \<Rightarrow> nat" where
  "bitwise_not n = undefined"

definition bitwise_and :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "bitwise_and n m = undefined"


end
