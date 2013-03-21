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

header{* Auxiliary Definitions needed by Lem *}

theory "Lem" 

imports 
 	 Main
   "~~/src/HOL/Map"

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

abbreviation (input) "set_choose s \<equiv> (SOME x. (x \<in> s))"
abbreviation (input) "set_diff (s1::'a set) s2 \<equiv> s1 - s2"
abbreviation (input) "set_filter P (s::'a set) \<equiv> {x \<in> s. P x}"
abbreviation (input) "set_cross s1 s2 \<equiv> s1 \<times> s2"

lemma set_choose_thm[simp]:
  "s \<noteq> {} \<Longrightarrow> (set_choose s) \<in> s"
by (rule someI_ex) auto

definition set_lfp:: "'a set \<Rightarrow> ('a set \<Rightarrow> 'a set) \<Rightarrow> 'a set" where
  "set_lfp s f = lfp (\<lambda>s'. f s' \<union> s)"
  
lemma set_lfp_tail_rec_def :
assumes mono_f: "mono f"
shows "set_lfp s f = (if (f s) \<subseteq> s then s else (set_lfp (s \<union> f s) f))" (is "?ls = ?rs")
proof (cases "f s \<subseteq> s")
  case True note fs_sub_s = this

  from fs_sub_s have "\<Inter>{u. f u \<union> s \<subseteq> u} = s" by auto
  hence "?ls = s" unfolding set_lfp_def lfp_def .
  with fs_sub_s show "?ls = ?rs" by simp
next
  case False note not_fs_sub_s = this
  
  from mono_f have mono_f': "mono (\<lambda>s'. f s' \<union> s)"
    unfolding mono_def by auto

  have "\<Inter>{u. f u \<union> s \<subseteq> u} = \<Inter>{u. f u \<union> (s \<union> f s) \<subseteq> u}" (is "\<Inter>?S1 = \<Inter>?S2")
  proof 
    have "?S2 \<subseteq> ?S1" by auto
    thus "\<Inter>?S1 \<subseteq> \<Inter>?S2" by (rule Inf_superset_mono)
  next  
    { fix e
      assume "e \<in> \<Inter>?S2"
      hence S2_prop: "\<And>s'. f s' \<subseteq> s' \<Longrightarrow> s \<subseteq> s' \<Longrightarrow> f s \<subseteq> s' \<Longrightarrow> e \<in> s'" by simp
      
      { fix s'
        assume "f s' \<subseteq> s'" "s \<subseteq> s'"
        
        from mono_f `s \<subseteq> s'` 
        have "f s \<subseteq> f s'" unfolding mono_def by simp
        with `f s' \<subseteq> s'` have "f s \<subseteq> s'" by simp
        with `f s' \<subseteq> s'` `s \<subseteq> s'` S2_prop
        have "e \<in> s'" by simp
      }
      hence "e \<in> \<Inter>?S1" by simp
    }  
    thus "\<Inter>?S2 \<subseteq> \<Inter>?S1" by auto
  qed
  hence "?ls = (set_lfp (s \<union> f s) f)" 
     unfolding set_lfp_def lfp_def .     
  with not_fs_sub_s show "?ls = ?rs" by simp
qed
  
lemma set_lfp_simps [simp] :
"mono f \<Longrightarrow> f s \<subseteq> s \<Longrightarrow> set_lfp s f = s" 
"mono f \<Longrightarrow> \<not>(f s \<subseteq> s) \<Longrightarrow> set_lfp s f = (set_lfp (s \<union> f s) f)" 
by (metis set_lfp_tail_rec_def)+


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


definition list_of_set :: "'a set \<Rightarrow> 'a list" where
   "list_of_set s = (SOME l. (set l = s \<and> distinct l))"

lemma list_of_set [simp] : 
  assumes fin_s: "finite s"
  shows "(set (list_of_set s) = s \<and> distinct (list_of_set s))"
unfolding list_of_set_def
proof (rule someI_ex)
  show "\<exists>l. set l = s \<and> distinct l" using fin_s
  proof (induct s)
    case empty
      show ?case by auto
    case (insert e s)
      note e_nin_s = insert(2)
      from insert(3) obtain l where set_l: "set l = s" and dist_l: "distinct l" by blast

      from set_l have set_el: "set (e # l) = insert e s" by auto
      from dist_l set_l e_nin_s have dist_el: "distinct (e # l)" by simp

      from set_el dist_el show ?case by blast
  qed
qed


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
