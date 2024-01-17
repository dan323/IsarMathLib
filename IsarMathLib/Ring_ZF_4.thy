(*
    This file is a part of IsarMathLib - 
    a library of formalized mathematics for Isabelle/Isar.

    Copyright (C) 2023  Daniel de la Concepcion

    This program is free software; Redistribution and use in source and binary forms, 
    with or without modification, are permitted provided that the following conditions are met:

   1. Redistributions of source code must retain the above copyright notice, 
   this list of conditions and the following disclaimer.
   2. Redistributions in binary form must reproduce the above copyright notice, 
   this list of conditions and the following disclaimer in the documentation and/or 
   other materials provided with the distribution.
   3. The name of the author may not be used to endorse or promote products 
   derived from this software without specific prior written permission.

THIS SOFTWARE IS PROVIDED BY THE AUTHOR ``AS IS'' AND ANY EXPRESS OR IMPLIED 
WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF 
MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. 
IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, 
SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, 
PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; 
OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, 
WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR 
OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, 
EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

*)

section \<open>Rings - Matrix rings\<close>

theory Ring_ZF_4 imports Group_ZF_5 FinSupp_ZF

begin

definition (in ring0) vectorSum ("AVect") where
"n\<in>nat \<Longrightarrow> AVect(n) \<equiv> A{lifted to function space over}n"

abbreviation(in ring0) addvect ("_\<ra>\<^sub>__" 94) where
"q \<ra>\<^sub>n t \<equiv> AVect(n)`\<langle>q,t\<rangle>"

abbreviation(in ring0) addminus ("\<rm>\<^sub>__" 94) where
"\<rm>\<^sub>n t \<equiv> GroupInv(R,A) O t"

lemma (in ring0) vector_ring_sum_fun:
  assumes "n\<in>nat"
  shows "abelian_group(n\<rightarrow>R,AVect(n))" unfolding abelian_group_def
  abelian_group_axioms_def
proof(safe)
  from add_group.Group_ZF_2_1_T2 have
    "IsAgroup(n\<rightarrow>R,AVect(n))" using assms(1) vectorSum_def by auto
  then show g0:"group0(n\<rightarrow>R, AVect(n))" unfolding group0_def.
  from add_group.Group_ZF_2_1_L7 show "AVect(n){is commutative on}(n\<rightarrow>R)"
    unfolding vectorSum_def[OF assms(1)] using Ring_ZF_1_L1(3) by auto
qed

definition (in ring0) Lin where
"n\<in>nat \<Longrightarrow> m\<in>nat \<Longrightarrow> Lin(n,m) \<equiv> {f\<in>(n\<rightarrow>R)\<rightarrow>(m\<rightarrow>R). Homomor(f,n\<rightarrow>R,AVect(n),m\<rightarrow>R,AVect(m))}"

abbreviation (in ring0) SqrLin where
"SqrLin(n) \<equiv> Lin(n,n)"

locale free_module_ring = ring0 +
  assumes finite_rank:"n\<in>nat"

sublocale free_module_ring < module_space: abelian_group
  "n\<rightarrow>R" "AVect(n)" "ConstantFunction(n,\<zero>)" "\<lambda>q t. (q \<ra>\<^sub>n t)" "\<lambda>q. GroupInv(n \<rightarrow> R, AVect(n)) ` q"
     apply auto using vector_ring_sum_fun finite_rank apply simp
  using add_group.monoid.Group_ZF_2_1_L2 unfolding
  vectorSum_def[OF finite_rank] by auto

definition (in ring0) matrixSum ("ALin") where
"n\<in>nat \<Longrightarrow> m\<in>nat \<Longrightarrow> ALin(n,m) \<equiv> AVect(m){lifted to function space over}(n\<rightarrow>R)"

theorem (in free_module_ring) endo_ring_free_module:
  shows "IsAring(SqrLin(n),InEnd(ALin(n,n),n\<rightarrow>R,AVect(n)),InEnd(Composition(n\<rightarrow>R),n\<rightarrow>R,AVect(n)))"
  using module_space.end_is_ring[of "ALin(n,n)" n] unfolding matrixSum_def[OF finite_rank finite_rank]
  End_def Lin_def[OF finite_rank finite_rank] by auto

end