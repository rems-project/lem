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
(*          Brian Campbell, University of Edinburgh                       *)
(*          Shaked Flur, University of Cambridge                          *)
(*          Thomas Bauereiss, University of Cambridge                     *)
(*          Stephen Kell, University of Cambridge                         *)
(*          Thomas Williams                                               *)
(*          Lars Hupel                                                    *)
(*          Basile Clement                                                *)
(*                                                                        *)
(*  The Lem sources are copyright 2010-2018                               *)
(*  by the authors above and Institut National de Recherche en            *)
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

chapter\<open>Mappings of Syntax needed by Lem\<close>

theory "Lem"

imports
         LemExtraDefs
         "HOL-Word.Word"
begin

type_synonym numeral = nat

subsection \<open>Finite Maps\<close>

abbreviation (input) "map_find k m \<equiv> the (m k)"
abbreviation (input) "map_update k v m \<equiv> m (k \<mapsto> v)"
abbreviation (input) "map_remove k m \<equiv> m |` (- {k})"
abbreviation (input) "map_any P m \<equiv> \<exists> (k, v) \<in> map_to_set m. P k v"
abbreviation (input) "map_all P m \<equiv> \<forall> (k, v) \<in> map_to_set m. P k v"

subsection \<open>Lists\<close>

abbreviation (input) "list_mem e l \<equiv> (e \<in> set l)"
abbreviation (input) "list_forall P l \<equiv> (\<forall>e\<in>set l. P e)"
abbreviation (input) "list_exists P l \<equiv> (\<exists>e\<in>set l. P e)"
abbreviation (input) "list_unzip l \<equiv> (map fst l, map snd l)"

subsection \<open>Sets\<close>

abbreviation (input) "set_filter P (s::'a set) \<equiv> {x \<in> s. P x}"
abbreviation (input) "set_bigunion S \<equiv> \<Union> S"
abbreviation (input) "set_biginter S \<equiv> \<Inter> S"

subsection \<open>Natural numbers\<close>

subsection \<open>Integers\<close>


subsection \<open>Dummy\<close>

consts
  bitwise_xor :: "nat \<Rightarrow> nat \<Rightarrow> nat"
  num_asr :: "nat \<Rightarrow> nat \<Rightarrow> nat"
  num_lsl :: "nat \<Rightarrow> nat \<Rightarrow> nat"
  bitwise_or :: "nat \<Rightarrow> nat \<Rightarrow> nat"
  bitwise_not :: "nat \<Rightarrow> nat"
  bitwise_and :: "nat \<Rightarrow> nat \<Rightarrow> nat"

subsection \<open>Machine words\<close>

definition word_update :: "'a::len0 word \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'b::len0 word \<Rightarrow> 'a word" where
  "word_update v lo hi w =
    (let sz = size v in
    of_bl (take (sz-hi-1) (to_bl v) @ to_bl w @ drop (sz-lo) (to_bl v)))"

definition signedIntegerFromWord :: "'a::len0 word \<Rightarrow> int" where
  \<comment> \<open>returns 0 for 0-length words; otherwise, treats the most-significant-bit as a sign bit\<close>
  "signedIntegerFromWord w = (if LENGTH('a) > 0 then sbintrunc (len_of TYPE('a) - 1) (uint w) else 0)"

lemma signedIntegerFromWord_sint[simp]:
  fixes w :: "'a::len word"
  shows "signedIntegerFromWord w = Word.sint w"
  by (auto simp: signedIntegerFromWord_def sint_uint)

lemma signedIntegerFromWord_0[simp]:
  "signedIntegerFromWord (w :: 0 word) = 0"
  by (auto simp: signedIntegerFromWord_def)

definition mostSignificantBit :: "'a::len0 word \<Rightarrow> bool" where
  \<comment> \<open>considers the most significant bit of 0-length words to be False\<close>
  "mostSignificantBit a \<longleftrightarrow> bin_sign (signedIntegerFromWord a) = -1"

lemma mostSignificantBit_msb[simp]: "mostSignificantBit (w::'a::len word) = Bits.msb w"
  by (auto simp: mostSignificantBit_def word_msb_def)

lemma mostSignificantBit_word0[simp]: "mostSignificantBit (w::0 word) \<longleftrightarrow> False"
  by (auto simp: mostSignificantBit_def)

definition signedLessEq :: "'a::len0 word \<Rightarrow> 'a word \<Rightarrow> bool"
  where "signedLessEq a b \<equiv> signedIntegerFromWord a \<le> signedIntegerFromWord b"

definition signedLess :: "'a::len0 word \<Rightarrow> 'a word \<Rightarrow> bool"
  where "signedLess x y \<equiv> signedLessEq x y \<and> x \<noteq> y"

lemma
  fixes x y :: "'a::len word"
  shows signedLessEq_word_sle[simp]: "signedLessEq x y \<longleftrightarrow> x <=s y"
    and signedLess_word_sless[simp]: "signedLess x y \<longleftrightarrow> x <s y"
  by (auto simp: signedLessEq_def signedLess_def word_sle_def word_sless_def)

lemma signedLessEq_0[simp]: "signedLessEq (x :: 0 word) y"
  by (auto simp: signedLessEq_def)

lemma word0_0: "(w :: 0 word) = 0"
  by transfer auto

lemma signedLess_0[simp]: "signedLess (x :: 0 word) y \<longleftrightarrow> False"
  using word0_0[of x] word0_0[of y]
  by (auto simp: signedLess_def)

definition arithShiftRight1 :: "'a::len0 word \<Rightarrow> 'a word"
  where "arithShiftRight1 w = word_of_int (bin_rest (signedIntegerFromWord w))"

definition arithShiftRight :: "'a::len0 word \<Rightarrow> nat \<Rightarrow> 'a word"
  where "arithShiftRight w n = (arithShiftRight1 ^^ n) w"

lemma arithShiftRight1_sshiftr1[simp]: "arithShiftRight1 (w::'a::len word) = sshiftr1 w"
  by (auto simp: arithShiftRight1_def sshiftr1_def)

lemma arithShiftRight_sshiftr[simp]: "arithShiftRight (w::'a::len word) n = w >>> n"
  by (induction n) (auto simp: arithShiftRight_def sshiftr_def)

definition signExtend :: "'a::len0 word \<Rightarrow> 'b::len0 word"
  where "signExtend w = word_of_int (signedIntegerFromWord w)"

lemma signExtend_scast[simp]: "signExtend (w::'a::len word) = scast w"
  by (auto simp: signExtend_def scast_def)

end
