(*
    This file is a part of IsarMathLib -
    a library of formalized mathematics written for Isabelle/Isar.

    Copyright (C) 2024  Daniel de la Concepcion Saez

    This program is free software; Redistribution and use in source and binary forms,
    with or without modification, are permitted provided that the following conditions are met:

   1. Redistributions of source code must retain the above copyright notice,
   this list of conditions and the following disclaimer.
   2. Redistributions in binary form must reproduce the above copyright notice,
   this list of conditions and the following disclaimer in the documentation and/or
   other materials provided with the distribution.
   3. The name of the author may not be used to endorse or promote products
   derived from this software without specific prior written permission.

THIS SOFTWARE IS PROVIDED BY THE AUTHOR ``AS IS'' AND ANY EXPRESS OR IMPLIED WARRANTIES,
INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A
PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY DIRECT,
INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES LOSS OF USE, DATA, OR PROFITS OR
BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT,
STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE
USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

*)

theory Module_ZF_3 imports Module_ZF_2 VectorSpace_ZF Finite_ZF

begin

subsection\<open>Free modules\<close>

text\<open>A free module is one that is determined by a base\<close>

definition (in module0) freeModule ("_{is free module}") where
  "\<N>{is free module} \<equiv> \<exists>\<BB>\<in>Pow(\<N>). (\<BB> {is a base for}\<N>)"

abbreviation (in vector_space0) vec_freeModule ("_{is free module}") where
  "\<N>{is free module} \<equiv> vspce_mod.freeModule(\<N>)"

abbreviation (in vector_space0) vec_Span ("{span of}_") where
  "{span of}S \<equiv> vspce_mod.Span(S)"

lemma (in vector_space0) module_free:
  assumes "Finite(S)" "S\<subseteq>V" "V \<subseteq> {span of}S"
  shows "V{is free module}"
proof-
  let ?S="{n\<in>nat. \<exists>F\<in>Pow(S). n=|F| \<and> V \<subseteq> {span of}F}"
  let ?P="\<lambda>m. (m\<in>nat \<and> (\<exists>F\<in>Pow(S). m=|F| \<and> V \<subseteq> {span of}F))"
  from assms(1) have "|S| \<in>nat" using Finite_cardinal_in_nat by auto
  moreover note assms(3) ultimately
  have "|S|\<in>?S" by auto
  then have "?S\<noteq>0" by auto
  then have "?P(Least (?P))" using LeastI[OF _ nat_into_Ord, of ?P] by blast
  then obtain F where F:"F\<in>Pow(S)" "Least(?P) = |F|" "V \<subseteq> {span of}F" by auto
  from F(1) assms(2) have sub:"F\<subseteq> V" by auto
  from F(1) assms(1) have fin:"Finite(F)" using subset_Finite by auto
  {
    assume "\<not>vspce_mod.LinInde(F)"
    with vspce_mod.LinInde_def[OF sub] obtain X N M m where as:"X\<in>nat" "N:X\<rightarrow>K" "M\<in>inj(X,F)"
      "vspce_mod.LinearComb(X, N, M) = \<Theta>" "m\<in>X" "N`m\<noteq>\<zero>" by auto
    from as(1) have "X\<in>FinPow(X)" unfolding FinPow_def using nat_into_Finite by auto moreover
    then have Xm:"X\<setminus>{m}\<in>FinPow(X)" unfolding FinPow_def using subset_Finite[of "X-{m}" X] by auto
    have M:"M:X\<rightarrow>V" using inj_is_fun[OF as(3)] sub func1_1_L1B by auto
    ultimately have "vspce_mod.LinearComb(X\<setminus>{m}, N, M)+\<^sub>V(N`m)\<cdot>\<^sub>S(M`m) = \<Theta>"
      using vspce_mod.sum_one_element[OF as(2) _ _ as(5), of M] as(4,5)
      vspce_mod.coordinate_function[OF as(2), of M] apply_equality by auto
    then have "(N`m)\<inverse>\<cdot>\<^sub>S(vspce_mod.LinearComb(X\<setminus>{m}, N, M)+\<^sub>V(N`m)\<cdot>\<^sub>S(M`m)) = (N`m)\<inverse>\<cdot>\<^sub>S\<Theta>"
      by auto
    then have "(N`m)\<inverse>\<cdot>\<^sub>S(vspce_mod.LinearComb(X\<setminus>{m}, N, M)+\<^sub>V(N`m)\<cdot>\<^sub>S(M`m)) =\<Theta>"
      using vspce_mod.zero_fixed[OF Field_ZF_1_L5(3)[OF apply_type[OF as(2,5)] as(6)]] by auto
    then have "((N`m)\<inverse>\<cdot>\<^sub>Svspce_mod.LinearComb(X\<setminus>{m}, N, M))+\<^sub>V(N`m)\<inverse>\<cdot>\<^sub>S((N`m)\<cdot>\<^sub>S(M`m)) =\<Theta>"
      using vspce_mod.module_ax1[OF Field_ZF_1_L5(3)[OF apply_type[OF as(2,5)] as(6)]]
      vspce_mod.linComb_is_in_module[OF as(2) M Xm] apply_type[OF vspce_mod.H_val_type(2)[OF apply_type[OF as(2,5)]] apply_type[OF M as(5)]]
      by auto
    then have "(vspce_mod.LinearComb(X\<setminus>{m}, {\<langle>k,(N`m)\<inverse>\<cdot>(N`k)\<rangle>. k\<in>X}, M))+\<^sub>V((N`m)\<inverse>\<cdot>(N`m))\<cdot>\<^sub>S(M`m) =\<Theta>"
      using vspce_mod.linComb_action(1)[OF as(2) M Field_ZF_1_L5(3)[OF apply_type[OF as(2,5)] as(6)] Xm]
      vspce_mod.module_ax3[OF Field_ZF_1_L5(3)[OF apply_type[OF as(2,5)] as(6)] apply_type[OF as(2,5)]
      apply_type[OF M as(5)]] by auto
    then have "(vspce_mod.LinearComb(X\<setminus>{m}, {\<langle>k,(N`m)\<inverse>\<cdot>(N`k)\<rangle>. k\<in>X}, M))+\<^sub>V(M`m) =\<Theta>"
      using vspce_mod.module_ax4[OF apply_type[OF M as(5)]] Field_ZF_1_L6(2)[OF apply_type[OF as(2,5)] as(6)]
      by auto
    then have "((\<midarrow> (vspce_mod.LinearComb(X\<setminus>{m}, {\<langle>k,(N`m)\<inverse>\<cdot>(N`k)\<rangle>. k\<in>X}, M)))+\<^sub>V((vspce_mod.LinearComb(X\<setminus>{m}, {\<langle>k,(N`m)\<inverse>\<cdot>(N`k)\<rangle>. k\<in>X}, M))+\<^sub>V(M`m)))=(\<midarrow>(vspce_mod.LinearComb(X\<setminus>{m}, {\<langle>k,(N`m)\<inverse>\<cdot>(N`k)\<rangle>. k\<in>X}, M)))+\<^sub>V \<Theta>"
      by auto
    then have "\<Theta>+\<^sub>V(M`m) = \<midarrow>(vspce_mod.LinearComb(X\<setminus>{m}, {\<langle>k,(N`m)\<inverse>\<cdot>(N`k)\<rangle>. k\<in>X}, M))"
      using vec_spce_ax3b[OF vec_spce_ax4a[of "vspce_mod.LinearComb(X\<setminus>{m}, {\<langle>k,(N`m)\<inverse>\<cdot>(N`k)\<rangle>. k\<in>X}, M)"]] vec_spce_ax4a[of "vspce_mod.LinearComb(X\<setminus>{m}, {\<langle>k,(N`m)\<inverse>\<cdot>(N`k)\<rangle>. k\<in>X}, M)"] vspce_mod.linComb_is_in_module[OF
      vspce_mod.linComb_action(2)[OF as(2) M Field_ZF_1_L5(3)[OF apply_type[OF as(2,5)] as(6)] Xm] M Xm]
      apply_type[OF M as(5)] vec_spce_ax1 vec_spce_ax4b[of "vspce_mod.LinearComb(X\<setminus>{m}, {\<langle>k,(N`m)\<inverse>\<cdot>(N`k)\<rangle>. k\<in>X}, M)"]
      vec_spce_ax2[of "vspce_mod.LinearComb(X\<setminus>{m}, {\<langle>k,(N`m)\<inverse>\<cdot>(N`k)\<rangle>. k\<in>X}, M)" "\<midarrow>(vspce_mod.LinearComb(X\<setminus>{m}, {\<langle>k,(N`m)\<inverse>\<cdot>(N`k)\<rangle>. k\<in>X}, M))"]
      by auto
    then have "(M`m) = \<midarrow>(vspce_mod.LinearComb(X\<setminus>{m}, {\<langle>k,(N`m)\<inverse>\<cdot>(N`k)\<rangle>. k\<in>X}, M))"
      using vec_spce_ax3b[OF apply_type[OF M as(5)]]
      vec_spce_ax2[OF apply_type[OF M as(5)] vec_spce_ax3a] by auto
    then have "(M`m) = (\<rm>\<one>)\<cdot>\<^sub>S(vspce_mod.LinearComb(X\<setminus>{m}, {\<langle>k,(N`m)\<inverse>\<cdot>(N`k)\<rangle>. k\<in>X}, M))"
      using vspce_mod.inv_module[OF vspce_mod.linComb_is_in_module[OF
      vspce_mod.linComb_action(2)[OF as(2) M Field_ZF_1_L5(3)[OF apply_type[OF as(2,5)] as(6)] Xm] M Xm]] by auto
    then have "M`m = vspce_mod.LinearComb(X\<setminus>{m}, {\<langle>k,(\<rm>\<one>)\<cdot>({\<langle>ma, (N ` m)\<inverse>  \<cdot> (N ` ma)\<rangle> . ma \<in> X} ` k)\<rangle>. k\<in>X}, M)" using 
      vspce_mod.linComb_action(1)[OF vspce_mod.linComb_action(2)[OF as(2) M Field_ZF_1_L5(3)[OF apply_type[OF as(2,5)] as(6)] Xm] 
        M Ring_ZF_1_L3(1)[OF Ring_ZF_1_L2(2)] Xm] by auto
    then have "M`m = vspce_mod.LinearComb(X\<setminus>{m}, {\<langle>k,(\<rm>\<one>)\<cdot>((N ` m)\<inverse>  \<cdot> (N ` k))\<rangle>. k\<in>X}, M)"
      using apply_equality[OF _ vspce_mod.linComb_action(2)[OF as(2) M Field_ZF_1_L5(3)[OF apply_type[OF as(2,5)] as(6)] Xm]]
      by auto
    then have "M`m = vspce_mod.LinearComb(X\<setminus>{m}, {\<langle>k,(\<rm>((N ` m)\<inverse> \<cdot> (N ` k)))\<rangle>. k\<in>X}, M)"
      using apply_type[OF as(2)]  Ring_ZF_1_L3(6) Ring_ZF_1_L4(3)
      Ring_ZF_1_L7(1)[OF Ring_ZF_1_L2(2)] Field_ZF_1_L5(3)[OF apply_type[OF as(2) as(5)] as(6)]
      by auto
    then have EQ:"M`m = vspce_mod.LinearComb(X\<setminus>{m}, {\<langle>k,(\<rm>((N ` m)\<inverse>)) \<cdot> (N ` k)\<rangle>. k\<in>X}, M)"
      using apply_type[OF as(2)]
      Ring_ZF_1_L7(1) Field_ZF_1_L5(3)[OF apply_type[OF as(2) as(5)] as(6)]
      by auto
    have B:"{\<langle>k,(\<rm>((N ` m)\<inverse>)) \<cdot> (N ` k)\<rangle>. k\<in>X}:X\<rightarrow>K" using vspce_mod.linComb_action(2)[OF as(2) M _ Xm]
      Field_ZF_1_L5(3)[OF apply_type[OF as(2) as(5)] as(6)] Ring_ZF_1_L3(1) by auto
    from EQ obtain U where U:"U:V\<rightarrow>K" "M`m = vspce_mod.LinearComb(M `` (X \<setminus> cons(m, \<emptyset>)), U, id(V))"
        "\<forall>x\<in>V \<setminus> M `` (X \<setminus> {m}). U ` x = \<zero>" using vspce_mod.index_module[OF B M Xm] by auto
    let ?p="M`m"
    let ?F="F-{M`m}"
    have A:"M`m\<in>F" using apply_type[OF inj_is_fun[OF as(3)] as(5)] by auto
    then have "succ(|?F|)= |F| " using Finite_imp_succ_cardinal_Diff[of F "M`m"] fin by auto
    {
      fix v assume v:"v\<in>V"
      with F(3) have "v\<in>{span of}F" by auto
      moreover from A have "F\<noteq>0" by auto
      ultimately have "v\<in>{vspce_mod.LinearComb(Fa, AA, id(F)) . \<langle>Fa,
          AA\<rangle> \<in> {\<langle>FF,B\<rangle> \<in> FinPow(F) \<times> (F \<rightarrow> K) . \<forall>m\<in>F \<setminus> FF. B ` m = \<zero>}}"
        unfolding vspce_mod.Span_def[OF sub] by auto
      then obtain Q R where "v=vspce_mod.LinearComb(Q, R, id(F))"
        "Q \<in> FinPow(F)" "R:F \<rightarrow> K" "\<forall>m\<in>F \<setminus> Q. R ` m = \<zero>" by auto
      {
        assume "M`m\<in>Q"
        
        let ?N="{\<langle>n,R`(M`n)\<rs>(N`m)\<inverse>\<cdot>(N`n)\<rangle>. n\<in>X}"
        
  
  from assms(3) have "({span of}S) = V" using vspce_mod.minimal_submodule[OF assms(2)]
      vspce_mod.trivial_submodules(1) by auto
  then have "(vspce_mod.LinInde(S)) \<longrightarrow> (V{is free module})"
    using vspce_mod.ModBase_def[OF assms(2), of V] unfolding vspce_mod.freeModule_def
    using assms(2) by auto
  



end