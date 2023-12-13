(* 
    This file is a part of IsarMathLib - 
    a library of formalized mathematics written for Isabelle/Isar.

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

THIS SOFTWARE IS PROVIDED BY THE AUTHOR ``AS IS'' AND ANY EXPRESS OR IMPLIED WARRANTIES,
INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A
PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY DIRECT,
INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES LOSS OF USE, DATA, OR PROFITS OR
BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT,
STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE
USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

*)

theory Int_Module_ZF imports Module_ZF Int_ZF_1

begin

section \<open>$\mathbb{Z}$ modules\<close>

text \<open>When $\mathbb{Z}$ acts on a group, that action is unique.\<close>

lemma action_unique:
  assumes "IsAmodule(int,IntegerAddition,IntegerMultiplication,G,f,S1)" and "IsAmodule(int,IntegerAddition,IntegerMultiplication,G,f,S2)"
  shows "S1 = S2"
proof-
  have mod0:"module0(int,IntegerAddition,IntegerMultiplication,G,f,S1)"
      "module0(int,IntegerAddition,IntegerMultiplication,G,f,S2)"
      using isAmodule_imp_module0 assms by auto
  {
    fix r assume rg:"r:int"
    have "S1`($#0) = S1 ` TheNeutralElement(int, IntegerAddition)"
      using int0.Int_ZF_1_L8(1) by auto
    then have "\<forall>g\<in>G. (S1`($#0))`g = (S1 ` TheNeutralElement(int, IntegerAddition))`g" by auto
    then have eq:"\<forall>g\<in>G. (S1`($#0))`g = TheNeutralElement(G, f)"
      using module0.mult_zeroR[OF mod0(1)] by auto
    have "(S1`($#0)):G\<rightarrow>G" using apply_type[OF module0.S_fun[OF mod0(1)]]
      rg(1) unfolding End_def by auto
    from fun_is_set_of_pairs[OF this] eq
    have "S1`($#0) = {\<langle>g,TheNeutralElement(G, f)\<rangle>. g\<in>G}" by auto
    then have "S1`($#0) = G\<times>{TheNeutralElement(G, f)}" by auto
    then have s1:"(S1`($#0)) = ConstantFunction(G,TheNeutralElement(G, f))"
      unfolding ConstantFunction_def.
    have "S2`($#0) = S2 ` TheNeutralElement(int, IntegerAddition)"
      using int0.Int_ZF_1_L8(1) by auto
    then have "\<forall>g\<in>G. (S2`($#0))`g = (S2 ` TheNeutralElement(int, IntegerAddition))`g" by auto
    then have eq:"\<forall>g\<in>G. (S2`($#0))`g = TheNeutralElement(G, f)"
      using module0.mult_zeroR[OF mod0(2)] by auto
    have "(S2`($#0)):G\<rightarrow>G" using apply_type[OF module0.S_fun[OF mod0(2)]]
      rg(1) unfolding End_def by auto
    from fun_is_set_of_pairs[OF this] eq
    have "S2`($#0) = {\<langle>g,TheNeutralElement(G, f)\<rangle>. g\<in>G}" by auto
    then have "S2`($#0) = G\<times>{TheNeutralElement(G, f)}" by auto
    then have "(S2`($#0)) = ConstantFunction(G,TheNeutralElement(G, f))"
      unfolding ConstantFunction_def.
    with s1 have ee:"S1`($#0) = S2`($#0)" by auto
    {
      assume k:"\<langle>r,$#0\<rangle>\<in>IntegerOrder"
      then have kint:"r\<in>int" unfolding IntegerOrder_def by auto
      have "S1 ` r = S2 ` r"
      proof (rule int0.Back_induct_on_int[of r "$#0" "\<lambda>q. S1`q = S2`q"])
        from k show "\<langle>r,$#0\<rangle>\<in>IntegerOrder" .
        from ee show "S1`($#0) = S2`($#0)" .
        {
          fix n assume n:"\<langle>n, $# 0\<rangle> \<in> IntegerOrder" "S1 ` n = S2 ` n"
          from n(1) have nint:"n:int" unfolding IntegerOrder_def by auto
          have minone:"GroupInv(int, IntegerAddition) `
               TheNeutralElement(int, IntegerMultiplication):int"
            using group0.inverse_in_group[OF Int_ZF_1_T2(3)]
            ring0.Ring_ZF_1_L2(2)[OF int0.Int_ZF_1_1_L2(3)] by auto
          have "S1 ` (IntegerAddition ` \<langle>n, GroupInv(int, IntegerAddition) `
               TheNeutralElement(int, IntegerMultiplication)\<rangle>) = 
          (f{lifted to function space over}G)`\<langle>S1`n,S1`(GroupInv(int, IntegerAddition) `
               TheNeutralElement(int, IntegerMultiplication))\<rangle>"
            using assms(1) minone nint unfolding IsAmodule_def by auto
          then have "S1 ` (IntegerAddition ` \<langle>n, GroupInv(int, IntegerAddition) `
               TheNeutralElement(int, IntegerMultiplication)\<rangle>) = 
          (f{lifted to function space over}G)`\<langle>S2`n,S1`(GroupInv(int, IntegerAddition) `
               TheNeutralElement(int, IntegerMultiplication))\<rangle>" using n(2) by auto moreover
          have q:"\<forall>g\<in>G. GroupInv(G, f) ` ((S1 ` TheNeutralElement(int, IntegerMultiplication)) ` g) =
            (GroupInv(G, f) O (S1 ` TheNeutralElement(int, IntegerMultiplication))) `g"
            using comp_fun_apply[of "S1 ` TheNeutralElement(int, IntegerMultiplication)" G G]
            apply_type[OF module0.S_fun[OF mod0(1)] ring0.Ring_ZF_1_L2(2)[OF int0.Int_ZF_1_1_L2(3)]]
            unfolding End_def by auto
          with module0.inv_module2[OF mod0(1) _ ring0.Ring_ZF_1_L2(2)[OF int0.Int_ZF_1_1_L2(3)]]
          have ex:"\<forall>g\<in>G. S1 ` (GroupInv(int, IntegerAddition) ` TheNeutralElement(int, IntegerMultiplication))` g =
             (GroupInv(G, f) O S1 ` TheNeutralElement(int, IntegerMultiplication)) ` g" by auto
          have f1:"S1 ` (GroupInv(int, IntegerAddition) ` TheNeutralElement(int, IntegerMultiplication)): G\<rightarrow>G"
            using apply_type[OF module0.S_fun[OF mod0(1)]] ring0.Ring_ZF_1_L2(2)[OF int0.Int_ZF_1_1_L2(3)]
            ring0.Ring_ZF_1_L3(1)[OF int0.Int_ZF_1_1_L2(3)] unfolding End_def by auto
          have f2:"GroupInv(G, f) O (S1 ` TheNeutralElement(int, IntegerMultiplication)) : G\<rightarrow>G"
            using comp_fun[of "S1 ` TheNeutralElement(int, IntegerMultiplication)" G G
              "GroupInv(G,f)" G] apply_type[OF module0.S_fun[OF mod0(1)]] unfolding End_def
            using ring0.Ring_ZF_1_L2(2)[OF int0.Int_ZF_1_1_L2(3)] group0.group0_2_T2[of G f]
            unfolding group0_def using assms(1) unfolding IsAmodule_def by blast
          from ex f1 f2 have "S1 ` (GroupInv(int, IntegerAddition) ` TheNeutralElement(int, IntegerMultiplication)) =
            (GroupInv(G, f) O S1 ` TheNeutralElement(int, IntegerMultiplication))"
            using func_eq by blast
          ultimately have "S1 ` (IntegerAddition ` \<langle>n, GroupInv(int, IntegerAddition) `
               TheNeutralElement(int, IntegerMultiplication)\<rangle>) = 
          (f{lifted to function space over}G)`\<langle>S2`n,GroupInv(G, f) O (S1 ` TheNeutralElement(int, IntegerMultiplication))\<rangle>"
            by auto
          then have A:"S1 ` (IntegerAddition ` \<langle>n, GroupInv(int, IntegerAddition) `
               TheNeutralElement(int, IntegerMultiplication)\<rangle>) = 
          (f{lifted to function space over}G)`\<langle>S2`n,GroupInv(G, f) O id(G)\<rangle>"
            using module0.S_one[OF mod0(1)] by auto
          have "S2 ` (IntegerAddition ` \<langle>n, GroupInv(int, IntegerAddition) `
               TheNeutralElement(int, IntegerMultiplication)\<rangle>) = 
          (f{lifted to function space over}G)`\<langle>S2`n,S2`(GroupInv(int, IntegerAddition) `
               TheNeutralElement(int, IntegerMultiplication))\<rangle>"
            using assms(2) minone nint unfolding IsAmodule_def by auto
          then have "S2 ` (IntegerAddition ` \<langle>n, GroupInv(int, IntegerAddition) `
               TheNeutralElement(int, IntegerMultiplication)\<rangle>) = 
          (f{lifted to function space over}G)`\<langle>S2`n,S2`(GroupInv(int, IntegerAddition) `
               TheNeutralElement(int, IntegerMultiplication))\<rangle>" using n(2) by auto moreover
          have q:"\<forall>g\<in>G. GroupInv(G, f) ` ((S2 ` TheNeutralElement(int, IntegerMultiplication)) ` g) =
            (GroupInv(G, f) O (S2 ` TheNeutralElement(int, IntegerMultiplication))) `g"
            using comp_fun_apply[of "S2 ` TheNeutralElement(int, IntegerMultiplication)" G G]
            apply_type[OF module0.S_fun[OF mod0(2)] ring0.Ring_ZF_1_L2(2)[OF int0.Int_ZF_1_1_L2(3)]]
            unfolding End_def by auto
          with module0.inv_module2[OF mod0(2) _ ring0.Ring_ZF_1_L2(2)[OF int0.Int_ZF_1_1_L2(3)]]
          have ex:"\<forall>g\<in>G. S2 ` (GroupInv(int, IntegerAddition) ` TheNeutralElement(int, IntegerMultiplication))` g =
             (GroupInv(G, f) O S2 ` TheNeutralElement(int, IntegerMultiplication)) ` g" by auto
          have f1:"S2 ` (GroupInv(int, IntegerAddition) ` TheNeutralElement(int, IntegerMultiplication)): G\<rightarrow>G"
            using apply_type[OF module0.S_fun[OF mod0(2)]] ring0.Ring_ZF_1_L2(2)[OF int0.Int_ZF_1_1_L2(3)]
            ring0.Ring_ZF_1_L3(1)[OF int0.Int_ZF_1_1_L2(3)] unfolding End_def by auto
          have f2:"GroupInv(G, f) O (S2 ` TheNeutralElement(int, IntegerMultiplication)) : G\<rightarrow>G"
            using comp_fun[of "S2 ` TheNeutralElement(int, IntegerMultiplication)" G G
              "GroupInv(G,f)" G] apply_type[OF module0.S_fun[OF mod0(2)]] unfolding End_def
            using ring0.Ring_ZF_1_L2(2)[OF int0.Int_ZF_1_1_L2(3)] group0.group0_2_T2[of G f]
            unfolding group0_def using assms(1) unfolding IsAmodule_def by blast
          from ex f1 f2 have "S2 ` (GroupInv(int, IntegerAddition) ` TheNeutralElement(int, IntegerMultiplication)) =
            (GroupInv(G, f) O S2 ` TheNeutralElement(int, IntegerMultiplication))"
            using func_eq by blast
          ultimately have "S2 ` (IntegerAddition ` \<langle>n, GroupInv(int, IntegerAddition) `
               TheNeutralElement(int, IntegerMultiplication)\<rangle>) = 
          (f{lifted to function space over}G)`\<langle>S2`n,GroupInv(G, f) O (S2 ` TheNeutralElement(int, IntegerMultiplication))\<rangle>"
            by auto
          then have "S2 ` (IntegerAddition ` \<langle>n, GroupInv(int, IntegerAddition) `
               TheNeutralElement(int, IntegerMultiplication)\<rangle>) = 
          (f{lifted to function space over}G)`\<langle>S2`n,GroupInv(G, f) O id(G)\<rangle>"
            using module0.S_one[OF mod0(2)] by auto
          with A have "S1 ` (IntegerAddition ` \<langle>n, GroupInv(int, IntegerAddition) `
               TheNeutralElement(int, IntegerMultiplication)\<rangle>) =S2 ` (IntegerAddition ` \<langle>n, GroupInv(int, IntegerAddition) `
               TheNeutralElement(int, IntegerMultiplication)\<rangle>)" by auto
        }
        then show " \<forall>n. \<langle>n, $# 0\<rangle> \<in> IntegerOrder \<and> S1 ` n = S2 ` n \<longrightarrow>
          S1 `
          (IntegerAddition `
           \<langle>n, GroupInv(int, IntegerAddition) `
               TheNeutralElement(int, IntegerMultiplication)\<rangle>) =
          S2 `
          (IntegerAddition `
           \<langle>n, GroupInv(int, IntegerAddition) `
               TheNeutralElement(int, IntegerMultiplication)\<rangle>)" by auto
      qed
    }
    moreover
    {
      assume k:"\<langle>$#0,r\<rangle>\<in>IntegerOrder"
      then have kint:"r\<in>int" unfolding IntegerOrder_def by auto
      have "S1 ` r = S2 ` r"
      proof (rule int0.Induction_on_int[of "$#0" r "\<lambda>q. S1`q = S2`q"])
        from k show "\<langle>$#0,r\<rangle>\<in>IntegerOrder" .
        from ee show "S1 ` ($# 0) = S2 ` ($# 0)" .
        {
          fix m assume m:"\<langle>$# 0, m\<rangle> \<in> IntegerOrder" "S1 ` m = S2 ` m"
          from m(1) have mint:"m\<in>int" unfolding IntegerOrder_def by auto
          have n:"TheNeutralElement(int, IntegerMultiplication)\<in>int"
            using ring0.Ring_ZF_1_L2(2)[OF int0.Int_ZF_1_1_L2(3)].
          have "S1 ` (IntegerAddition ` \<langle>m, TheNeutralElement(int, IntegerMultiplication)\<rangle>) = 
          (f{lifted to function space over}G)`\<langle>S1`m,S1`(TheNeutralElement(int, IntegerMultiplication))\<rangle>"
            using assms(1) mint n unfolding IsAmodule_def by auto
          then have "S1 ` (IntegerAddition ` \<langle>m, TheNeutralElement(int, IntegerMultiplication)\<rangle>) = 
          (f{lifted to function space over}G)`\<langle>S2`m,id(G)\<rangle>"
            using module0.S_one[OF mod0(1)] m(2) by auto
          moreover
          have "S2 ` (IntegerAddition ` \<langle>m, TheNeutralElement(int, IntegerMultiplication)\<rangle>) = 
          (f{lifted to function space over}G)`\<langle>S2`m,S2`(TheNeutralElement(int, IntegerMultiplication))\<rangle>"
            using assms(2) mint n unfolding IsAmodule_def by auto
          then have "S2 ` (IntegerAddition ` \<langle>m, TheNeutralElement(int, IntegerMultiplication)\<rangle>) = 
          (f{lifted to function space over}G)`\<langle>S2`m,id(G)\<rangle>"
            using module0.S_one[OF mod0(2)] m(2) by auto
          ultimately
          have "S1 ` (IntegerAddition ` \<langle>m, TheNeutralElement(int, IntegerMultiplication)\<rangle>) = 
            S2 ` (IntegerAddition ` \<langle>m, TheNeutralElement(int, IntegerMultiplication)\<rangle>)" by auto
        }
        then show "\<forall>m. \<langle>$# 0, m\<rangle> \<in> IntegerOrder \<and> S1 ` m = S2 ` m \<longrightarrow>
          S1 ` (IntegerAddition ` \<langle>m, TheNeutralElement(int, IntegerMultiplication)\<rangle>) =
          S2 ` (IntegerAddition ` \<langle>m, TheNeutralElement(int, IntegerMultiplication)\<rangle>)" by auto
      qed
    } moreover note int0.Int_ZF_2_T1(2)
    ultimately have "S1`r = S2`r" unfolding IsTotal_def using rg(1)
      int0.Int_ZF_1_L8(1) ring0.Ring_ZF_1_L2(1)[OF int0.Int_ZF_1_1_L2(3)] by auto
  }
  then have "\<forall>r\<in>int. S1`r = S2`r" by auto
  from func_eq[OF _ _ this] show "S1 = S2" using 
      module0.S_fun[OF mod0(1)] module0.S_fun[OF mod0(2)] by auto
qed

text \<open>Every group accepts an action by $\mathbb{Z}$\<close>

text \<open>It is a well-defined function\<close>

lemma(in abelian_group) group_action_int_1:
  defines "S \<equiv> {\<langle>$# n,{\<langle>x,Fold(P,\<one>,n\<times>{x})\<rangle>. x\<in>G}\<rangle>. n\<in>nat}\<union> {\<langle>$- $# n,GroupInv(G,P) O {\<langle>x,Fold(P,\<one>, n\<times>{x})\<rangle>. x\<in>G}\<rangle>. n\<in>nat}"
  shows "S:int \<rightarrow> End(G,P)" unfolding Pi_def apply simp unfolding function_def
proof-
  {
    fix n assume n:"n\<in>nat"
    {
      fix x na assume x:"x\<in>G" "na\<in>nat"
      have "Fold(P,\<one>,na\<times>{x})\<in>G" using fold_props(2)[OF x(2) group_oper_fun _ group0_2_L2(1),
            of "ConstantFunction(na,x)"] group0_2_L2(1) func1_3_L1[OF x(1)] unfolding ConstantFunction_def
        by auto
    }
    then have FG:"\<forall>n\<in>nat. \<forall>x\<in>G. Fold(P,\<one>,n\<times>{x})\<in>G" by auto
    then have fun:"{\<langle>x,Fold(P,\<one>, n\<times>{x})\<rangle>. x\<in>G}:G\<rightarrow>G" using ZF_fun_from_total n by auto
    {
      fix x assume x:"x\<in>G"
      then have "{\<langle>x,Fold(P,\<one>, n\<times>{x})\<rangle>. x\<in>G}`x = Fold(P,\<one>, n\<times>{x})"
        using ZF_fun_from_tot_val0[OF fun] by auto
    }
    then have rule:"\<forall>x\<in>G. {\<langle>x,Fold(P,\<one>, n\<times>{x})\<rangle>. x\<in>G}`x = Fold(P,\<one>, n\<times>{x})" by auto
    {
      fix x y assume xy:"x:G" "y:G"
      then have A:"P`\<langle>{\<langle>x,Fold(P,\<one>, n\<times>{x})\<rangle>. x\<in>G}`x,{\<langle>x,Fold(P,\<one>, n\<times>{x})\<rangle>. x\<in>G}`y\<rangle> = P`\<langle>Fold(P,\<one>, n\<times>{x}),Fold(P,\<one>, n\<times>{y})\<rangle>"
        using rule by auto
      have "P`\<langle>Fold(P,\<one>, n\<times>{x}),Fold(P,\<one>, n\<times>{y})\<rangle> = Fold(P,\<one>, n\<times>{P`\<langle>x,y\<rangle>})"
      proof(rule nat_induct[of n "\<lambda>t. P`\<langle>Fold(P,\<one>, t\<times>{x}),Fold(P,\<one>, t\<times>{y})\<rangle> = Fold(P,\<one>, t\<times>{P`\<langle>x,y\<rangle>})"])
        from n show "n\<in>nat".
        have " Fold(P, \<one>, 0) = \<one>" using fold_empty[OF group_oper_fun _ group0_2_L2(1)] group0_2_L2(1)
          by auto
        then have "\<one>\<cdot>\<one> = \<one> \<Longrightarrow> P ` \<langle>Fold(P, \<one>, 0 \<times> {x}), Fold(P, \<one>, 0 \<times> {y})\<rangle> = Fold(P, \<one>, 0 \<times> {P ` \<langle>x, y\<rangle>})"
          by auto
        then show "P ` \<langle>Fold(P, \<one>, 0 \<times> {x}), Fold(P, \<one>, 0 \<times> {y})\<rangle> = Fold(P, \<one>, 0 \<times> {P ` \<langle>x, y\<rangle>})"
          using group0_2_L2(2) group0_2_L2(1) by auto
        {
          fix xa assume as:"xa\<in>nat" "P ` \<langle>Fold(P, \<one>, xa \<times> {x}), Fold(P, \<one>, xa \<times> {y})\<rangle> =
            Fold(P, \<one>, xa \<times> {P ` \<langle>x, y\<rangle>})"
          have dd:"domain(xa\<times>{x}) = xa" by auto
          then have e:"succ(xa) \<times> {x}= Append(xa\<times>{x},x)"
            unfolding Append_def by auto
          have dd:"domain(xa\<times>{P`\<langle>x,y\<rangle>}) = xa" by auto
          then have u:"succ(xa)\<times>{P`\<langle>x,y\<rangle>} = Append(xa\<times>{P`\<langle>x,y\<rangle>},P`\<langle>x,y\<rangle>)" unfolding Append_def
            by auto
          have "Fold(P, \<one>, succ(xa) \<times> {x}) = Fold(P, \<one>, Append(xa\<times>{x},x))" using subst[OF e, of "\<lambda>t. Fold(P,\<one>,succ(xa) \<times> {x}) = Fold(P,\<one>,t)"]
            by (simp only:refl)
          then have XX:"Fold(P, \<one>, succ(xa) \<times> {x}) =P ` \<langle>Fold(P, \<one>, xa\<times>{x}), x\<rangle>" using fold_append(2)[OF as(1) group_oper_fun
            func1_3_L1[OF xy(1), of xa]  group0_2_L2(1) xy(1)] unfolding ConstantFunction_def
            by (simp only:trans)
          have "domain(xa\<times>{y}) = xa" by auto
          then have e:"succ(xa) \<times> {y}= Append(xa\<times>{y},y)"
            unfolding Append_def by auto
          have ff:"(xa \<times> {P ` \<langle>x, y\<rangle>}):xa \<rightarrow> G" using func1_3_L1[OF group_op_closed[OF xy]]
            unfolding ConstantFunction_def by auto
          have g:"x\<cdot>y = P`\<langle>x,y\<rangle>" by auto
          have "Fold(P, \<one>, succ(xa) \<times> {y}) = Fold(P, \<one>, Append(xa\<times>{y},y))" using subst[OF e, of "\<lambda>t. Fold(P,\<one>,succ(xa) \<times> {y}) = Fold(P,\<one>,t)"]
            by (simp only:refl)
          then have YY:"Fold(P, \<one>, succ(xa) \<times> {y}) =P ` \<langle>Fold(P, \<one>, xa\<times>{y}), y\<rangle>" using fold_append(2)[OF as(1) group_oper_fun
            func1_3_L1[OF xy(2), of xa]  group0_2_L2(1) xy(2)] unfolding ConstantFunction_def
            by (simp only:trans)
          with XX have "P`\<langle>Fold(P, \<one>, succ(xa) \<times> {x}),Fold(P, \<one>, succ(xa) \<times> {y})\<rangle>= P`\<langle>P ` \<langle>Fold(P, \<one>, xa\<times>{x}), x\<rangle>,P ` \<langle>Fold(P, \<one>, xa\<times>{y}), y\<rangle>\<rangle>"
            by auto
          with FG as(1) xy have "P`\<langle>Fold(P, \<one>, succ(xa) \<times> {x}),Fold(P, \<one>, succ(xa) \<times> {y})\<rangle>= P`\<langle>P ` \<langle>Fold(P, \<one>, xa\<times>{x}), Fold(P, \<one>, xa\<times>{y})\<rangle>,P`\<langle>x, y\<rangle>\<rangle>" 
            using group0_4_L8(3)[OF _ _ xy(1) _ xy(2), of "Fold(P, \<one>, xa\<times>{x})" "Fold(P, \<one>, xa\<times>{y})"] abelian_group_axioms unfolding
            abelian_group_def abelian_group_axioms_def by auto
          with as(2) have "P`\<langle>Fold(P, \<one>, succ(xa) \<times> {x}),Fold(P, \<one>, succ(xa) \<times> {y})\<rangle>= P`\<langle>Fold(P, \<one>, xa \<times> {P ` \<langle>x, y\<rangle>}),P`\<langle>x, y\<rangle>\<rangle>"
            by auto
          then have "P`\<langle>Fold(P, \<one>, succ(xa) \<times> {x}),Fold(P, \<one>, succ(xa) \<times> {y})\<rangle>= Fold(P, \<one>, Append(xa \<times> {P ` \<langle>x, y\<rangle>},P ` \<langle>x, y\<rangle>))"
            using fold_append(2)[OF as(1) group_oper_fun ff group0_2_L2(1), of "P`\<langle>x,y\<rangle>", THEN sym] group_op_closed[OF xy]
            g by (simp only:trans)
          then show "P ` \<langle>Fold(P, \<one>, succ(xa) \<times> {x}), Fold(P, \<one>, succ(xa) \<times> {y})\<rangle> =
            Fold(P, \<one>, succ(xa) \<times> {P ` \<langle>x, y\<rangle>})" using subst[of _ _ "\<lambda>t. P ` \<langle>Fold(P, \<one>, succ(xa) \<times> {x}), Fold(P, \<one>, succ(xa) \<times> {y})\<rangle> =
            Fold(P, \<one>,t)", OF u[THEN sym]] by blast
        }
      qed
      moreover
      from rule have "{\<langle>x, Fold(P, \<one>, n \<times> {x})\<rangle> . x \<in> G} ` (P ` \<langle>x, y\<rangle>) = Fold(P, \<one>, n \<times> {P ` \<langle>x, y\<rangle>})"
        using group_op_closed xy by auto moreover
      note A ultimately
      have "P ` \<langle>{\<langle>x, Fold(P, \<one>, n \<times> {x})\<rangle> . x \<in> G} ` x, {\<langle>x, Fold(P, \<one>, n \<times> {x})\<rangle> . x \<in> G} ` y\<rangle> =
          {\<langle>x, Fold(P, \<one>, n \<times> {x})\<rangle> . x \<in> G} ` (P ` \<langle>x, y\<rangle>)" by auto
    }
    then have "\<forall>x\<in>G. \<forall>y\<in>G. P ` \<langle>{\<langle>x, Fold(P, \<one>, n \<times> {x})\<rangle> . x \<in> G} ` x, {\<langle>x, Fold(P, \<one>, n \<times> {x})\<rangle> . x \<in> G} ` y\<rangle> =
          {\<langle>x, Fold(P, \<one>, n \<times> {x})\<rangle> . x \<in> G} ` (P ` \<langle>x, y\<rangle>)" by auto
    then have "{\<langle>x,Fold(P,\<one>, n\<times>{x})\<rangle>. x\<in>G}\<in>End(G,P)" unfolding End_def 
      Homomor_def[OF groupAssum groupAssum]
      apply simp using fun by auto moreover
    then have "Composition(G)`\<langle>GroupInv(G,P), {\<langle>x,Fold(P,\<one>, n\<times>{x})\<rangle>. x\<in>G}\<rangle>\<in>End(G,P)"
      using end_composition[OF end_inverse_group] by auto
    then have "GroupInv(G,P) O {\<langle>x,Fold(P,\<one>, n\<times>{x})\<rangle>. x\<in>G}\<in>End(G,P)"
      using func_ZF_5_L2 fun group0_2_T2 by auto
    ultimately have "{\<langle>x,Fold(P,\<one>, n\<times>{x})\<rangle>. x\<in>G}\<in>End(G,P) \<and> GroupInv(G,P) O {\<langle>x,Fold(P,\<one>, n\<times>{x})\<rangle>. x\<in>G}\<in>End(G,P)" by auto
  }
  then have "\<forall>n\<in>nat. {\<langle>x,Fold(P,\<one>, n\<times>{x})\<rangle>. x\<in>G}\<in>End(G,P) \<and> GroupInv(G,P) O {\<langle>x,Fold(P,\<one>, n\<times>{x})\<rangle>. x\<in>G}\<in>End(G,P)" by auto
  then have "\<forall>n\<in>nat. \<langle>$# n,{\<langle>x,Fold(P,\<one>, n\<times>{x})\<rangle>. x\<in>G}\<rangle>\<in>int\<times>End(G,P) \<and> \<langle>$# $-n,GroupInv(G,P) O {\<langle>x,Fold(P,\<one>, n\<times>{x})\<rangle>. x\<in>G}\<rangle>\<in>int\<times>End(G,P)"
    by auto
  then have A1:"S \<subseteq> int \<times> End(G,P)" unfolding S_def by blast
  have dom:"domain(S) ={$#n. n\<in>nat}\<union>{ $- $# n. n\<in>nat}" unfolding domain_def S_def by auto
  {
    fix z assume z:"z:int"
    {
      assume "znegative(z)"
      then obtain n where n:"z=$- $# succ(n)" "n:nat" using zneg_int_of z by auto
      then have "z\<in>{$- $#n. n\<in>nat}" using nat_succI[of n] by auto
      then have "z\<in>domain(S)" using dom by auto
    } moreover
    {
      assume "\<not>znegative(z)"
      then obtain n where n:"z= $# n" "n:nat" using not_zneg_int_of z by auto
      then have "z\<in>{$#n. n\<in>nat}" using nat_succI[of n] by auto
      then have "z\<in>domain(S)" using dom by auto
    } ultimately
    have "z\<in>domain(S)" by auto
  }
  then have A2:"int \<subseteq> domain(S)" by auto
  {
    fix x y z assume as:"\<langle>x, y\<rangle> \<in> S" "\<langle>x, z\<rangle> \<in> S"
    {
      assume "\<langle>x,y\<rangle>\<in>{\<langle>$# n,{\<langle>x,Fold(P,\<one>,n\<times>{x})\<rangle>. x\<in>G}\<rangle>. n\<in>nat}"
      "\<langle>x,z\<rangle>\<in>{\<langle>$# n,{\<langle>x,Fold(P,\<one>,n\<times>{x})\<rangle>. x\<in>G}\<rangle>. n\<in>nat}"
      then have "y=z" by auto
    } moreover
    {
      assume "\<langle>x,y\<rangle>\<in>{\<langle>$-$# n,GroupInv(G,P) O {\<langle>x,Fold(P,\<one>,n\<times>{x})\<rangle>. x\<in>G}\<rangle>. n\<in>nat}"
      "\<langle>x,z\<rangle>\<in>{\<langle>$-$# n,GroupInv(G,P) O {\<langle>x,Fold(P,\<one>,n\<times>{x})\<rangle>. x\<in>G}\<rangle>. n\<in>nat}"
      then have "y=z" by auto
    } moreover
    {
      assume "\<langle>x,y\<rangle>\<in>{\<langle>$# n,{\<langle>x,Fold(P,\<one>,n\<times>{x})\<rangle>. x\<in>G}\<rangle>. n\<in>nat}"
      "\<langle>x,z\<rangle>\<in>{\<langle>$- $# n,GroupInv(G,P) O {\<langle>x,Fold(P,\<one>, n\<times>{x})\<rangle>. x\<in>G}\<rangle>. n\<in>nat}"
      then obtain n m where n:"n:nat" "m\<in>nat" "$#n = $- $#m" "$#n=x" "y={\<langle>x,Fold(P,\<one>,n\<times>{x})\<rangle>. x\<in>G}"
        "z=GroupInv(G,P) O {\<langle>x,Fold(P,\<one>, m\<times>{x})\<rangle>. x\<in>G}" by auto
      have "\<not>znegative($#n)" using not_znegative_int_of.
      with n(3) have "\<not>znegative($-$#m)" by auto
      then have "$#m = $# 0" using not_znegative_imp_zero by auto
      then have "x=$#0" using n(3,4) int0.Int_ZF_1_L11 int0.Int_ZF_1_L8(1)
        int0.Int_ZF_1_L9A[of "$#0"] int0.Int_ZF_1_L8A(1) by auto
      with n(4) have nz:"n=0" using int_of_inject n(1) by auto
      with n(5) have "y={\<langle>x,Fold(P,\<one>,0)\<rangle>. x\<in>G}" by auto
      then have y:"y=G\<times>{Fold(P,\<one>,0)}" by auto
      from n(3) \<open>n=0\<close> have "$-$#m = $#0" by auto
      then have "$-$-$#m = $-$#0" by auto
      then have "$# m = $-$#0" using zminus_zminus by auto
      then have "$# m = $#0" by auto
      then have mz:"m= 0" using int_of_inject n(2) by auto
      {
        fix u assume u:"u\<in>z"
        with n(6) mz have "u\<in>GroupInv(G,P) O {\<langle>x,Fold(P,\<one>, 0)\<rangle>. x\<in>G}" by auto
        then obtain u1 u2 u3 where u:"u=\<langle>u1,u3\<rangle>" "\<langle>u1,u2\<rangle>\<in>{\<langle>x,Fold(P,\<one>, 0)\<rangle>. x\<in>G}"
          "\<langle>u2,u3\<rangle>\<in>GroupInv(G,P)" unfolding comp_def by auto
        from u(2) have "u2=Fold(P,\<one>, 0)" by auto
        then have u2:"u2=\<one>" using fold_empty[OF group_oper_fun _ group0_2_L2(1)]
          group0_2_L2(1) by auto
        with u(3) have "\<one>\<cdot>u3 = \<one>" "u3:G" unfolding GroupInv_def by auto
        then have "u3=\<one>" using group0_2_L2(2) by auto
        with u2 have "u2=u3" by auto
        with u(1,2) have "u\<in>{\<langle>x,Fold(P,\<one>, 0)\<rangle>. x\<in>G}" by auto
      }
      then have "z \<subseteq> {\<langle>x,Fold(P,\<one>, 0)\<rangle>. x\<in>G}" by auto
      with y have "z \<subseteq> y" by auto moreover
      {
        fix t assume "t:y"
        then have t:"t:G\<times>{Fold(P,\<one>, 0)}" using y by auto
        then have "t:G\<times>{\<one>}" using fold_empty[OF group_oper_fun _ group0_2_L2(1)]
          group0_2_L2(1) by auto
        then obtain g where g:"g\<in>G" "t=\<langle>g,\<one>\<rangle>" by auto
        moreover have "\<langle>\<one>,\<one>\<rangle>\<in>GroupInv(G,P)"
          unfolding GroupInv_def using group0_2_L2 by auto
        with g have "t\<in>GroupInv(G,P) O (G\<times>{\<one>})" by auto
        then have "t\<in>GroupInv(G,P) O {\<langle>x,Fold(P,\<one>, 0)\<rangle>. x\<in>G}"
          using fold_empty[OF group_oper_fun _ group0_2_L2(1)]
          group0_2_L2(1) by force
        then have "t\<in>GroupInv(G,P) O {\<langle>x,Fold(P,\<one>, m\<times>{x})\<rangle>. x\<in>G}" using mz
          by auto
        then have "t:z" using n(6) by auto
      }
      then have "y\<subseteq>z" by auto ultimately
      have "y=z" by auto
    } moreover
    {
      assume "\<langle>x,z\<rangle>\<in>{\<langle>$# n,{\<langle>x,Fold(P,\<one>,n\<times>{x})\<rangle>. x\<in>G}\<rangle>. n\<in>nat}"
      "\<langle>x,y\<rangle>\<in>{\<langle>$- $# n,GroupInv(G,P) O {\<langle>x,Fold(P,\<one>, n\<times>{x})\<rangle>. x\<in>G}\<rangle>. n\<in>nat}"
      then obtain n m where n:"n:nat" "m\<in>nat" "$#n = $- $#m" "$#n=x" "z={\<langle>x,Fold(P,\<one>,n\<times>{x})\<rangle>. x\<in>G}"
        "y=GroupInv(G,P) O {\<langle>x,Fold(P,\<one>, m\<times>{x})\<rangle>. x\<in>G}" by auto
      have "\<not>znegative($#n)" using not_znegative_int_of.
      with n(3) have "\<not>znegative($-$#m)" by auto
      then have "$#m = $# 0" using not_znegative_imp_zero by auto
      then have "x=$#0" using n(3,4) int0.Int_ZF_1_L11 int0.Int_ZF_1_L8(1)
        int0.Int_ZF_1_L9A[of "$#0"] int0.Int_ZF_1_L8A(1) by auto
      with n(4) have nz:"n=0" using int_of_inject n(1) by auto
      with n(5) have "z={\<langle>x,Fold(P,\<one>,0)\<rangle>. x\<in>G}" by auto
      then have y:"z=G\<times>{Fold(P,\<one>,0)}" by auto
      from n(3) \<open>n=0\<close> have "$-$#m = $#0" by auto
      then have "$-$-$#m = $-$#0" by auto
      then have "$# m = $-$#0" using zminus_zminus by auto
      then have "$# m = $#0" by auto
      then have mz:"m= 0" using int_of_inject n(2) by auto
      {
        fix u assume u:"u\<in>y"
        with n(6) mz have "u\<in>GroupInv(G,P) O {\<langle>x,Fold(P,\<one>, 0)\<rangle>. x\<in>G}" by auto
        then obtain u1 u2 u3 where u:"u=\<langle>u1,u3\<rangle>" "\<langle>u1,u2\<rangle>\<in>{\<langle>x,Fold(P,\<one>, 0)\<rangle>. x\<in>G}"
          "\<langle>u2,u3\<rangle>\<in>GroupInv(G,P)" unfolding comp_def by auto
        from u(2) have "u2=Fold(P,\<one>, 0)" by auto
        then have u2:"u2=\<one>" using fold_empty[OF group_oper_fun _ group0_2_L2(1)]
          group0_2_L2(1) by auto
        with u(3) have "\<one>\<cdot>u3 = \<one>" "u3:G" unfolding GroupInv_def by auto
        then have "u3=\<one>" using group0_2_L2(2) by auto
        with u2 have "u2=u3" by auto
        with u(1,2) have "u\<in>{\<langle>x,Fold(P,\<one>, 0)\<rangle>. x\<in>G}" by auto
      }
      then have "y \<subseteq> {\<langle>x,Fold(P,\<one>, 0)\<rangle>. x\<in>G}" by auto
      with y have "y \<subseteq> z" by auto moreover
      {
        fix t assume "t:z"
        then have t:"t:G\<times>{Fold(P,\<one>, 0)}" using y by auto
        then have "t:G\<times>{\<one>}" using fold_empty[OF group_oper_fun _ group0_2_L2(1)]
          group0_2_L2(1) by auto
        then obtain g where g:"g\<in>G" "t=\<langle>g,\<one>\<rangle>" by auto
        moreover have "\<langle>\<one>,\<one>\<rangle>\<in>GroupInv(G,P)"
          unfolding GroupInv_def using group0_2_L2 by auto
        with g have "t\<in>GroupInv(G,P) O (G\<times>{\<one>})" by auto
        then have "t\<in>GroupInv(G,P) O {\<langle>x,Fold(P,\<one>, 0)\<rangle>. x\<in>G}"
          using fold_empty[OF group_oper_fun _ group0_2_L2(1)]
          group0_2_L2(1) by force
        then have "t\<in>GroupInv(G,P) O {\<langle>x,Fold(P,\<one>, m\<times>{x})\<rangle>. x\<in>G}" using mz
          by auto
        then have "t:y" using n(6) by auto
      }
      then have "z\<subseteq>y" by auto ultimately
      have "y=z" by auto
    } moreover note as
    ultimately have "y=z" unfolding S_def by auto
  }
  then have "\<forall>x y. \<langle>x, y\<rangle> \<in> S \<longrightarrow> (\<forall>z. \<langle>x, z\<rangle> \<in> S \<longrightarrow> y = z)" by auto
  with A1 A2 show "S \<subseteq> int \<times> End(G, P) \<and>
    int \<subseteq> domain(S) \<and> (\<forall>x y. \<langle>x, y\<rangle> \<in> S \<longrightarrow> (\<forall>y'. \<langle>x, y'\<rangle> \<in> S \<longrightarrow> y = y'))" by auto
qed

text\<open>\<close>

lemma(in abelian_group) group_action_int_1_5:
  defines "S \<equiv> {\<langle>$# n,{\<langle>x,Fold(P,\<one>,n\<times>{x})\<rangle>. x\<in>G}\<rangle>. n\<in>nat}\<union> {\<langle>$- $# n,GroupInv(G,P) O {\<langle>x,Fold(P,\<one>, n\<times>{x})\<rangle>. x\<in>G}\<rangle>. n\<in>nat}"
  assumes "n\<in>nat" "x\<in>G"
  shows "(S`($#n))`x =Fold(P,\<one>,n\<times>{x})" "(S`($- $#n))`x =Fold(P,\<one>,n\<times>{x})\<inverse>"
proof-
  have "S`($#n) = {\<langle>x,Fold(P,\<one>,n\<times>{x})\<rangle>. x\<in>G}" unfolding S_def
    apply(rule apply_equality[OF _ group_action_int_1]) using assms(2) by auto
  then have "(S`($#n))`x = {\<langle>x,Fold(P,\<one>,n\<times>{x})\<rangle>. x\<in>G}`x" by auto
  then show "(S`($#n))`x =Fold(P,\<one>,n\<times>{x})" using apply_equality[OF
    lamI[OF assms(3),of "\<lambda>t. Fold(P,\<one>,n\<times>{t})"]] lam_funtype
    lambda_fun_alt[of G "\<lambda>t. Fold(P,\<one>,n\<times>{t})"] by auto
  have "S`($- $#n) =GroupInv(G,P) O {\<langle>x,Fold(P,\<one>,n\<times>{x})\<rangle>. x\<in>G}" unfolding S_def
    apply(rule apply_equality[OF _ group_action_int_1]) using assms(2) by auto
  then have "(S`($- $#n))`x = (GroupInv(G,P) O {\<langle>x,Fold(P,\<one>,n\<times>{x})\<rangle>. x\<in>G})`x" by auto
  then have "(S`($- $#n))`x = GroupInv(G,P)`({\<langle>x,Fold(P,\<one>,n\<times>{x})\<rangle>. x\<in>G}`x)"
    using comp_fun_apply[OF lam_funtype assms(3)]
    lambda_fun_alt[of G "\<lambda>t. Fold(P,\<one>,n\<times>{t})"] by auto
  then have "(S`($- $#n))`x = GroupInv(G,P)`(Fold(P,\<one>,n\<times>{x}))"
    using apply_equality[OF lamI[OF assms(3), of "\<lambda>t. Fold(P,\<one>,n\<times>{t})"] lam_funtype[of G "\<lambda>t. Fold(P,\<one>,n\<times>{t})"]
   ] lambda_fun_alt[of G "\<lambda>t. Fold(P,\<one>,n\<times>{t})"] by auto
  then show "(S`($- $#n))`x = (Fold(P,\<one>,n\<times>{x}))\<inverse>"
    by auto
qed

text\<open>\<close>

lemma(in abelian_group) group_action_int_2:
  defines "S \<equiv> {\<langle>$# n,{\<langle>x,Fold(P,\<one>,n\<times>{x})\<rangle>. x\<in>G}\<rangle>. n\<in>nat}\<union> {\<langle>$- $# n,GroupInv(G,P) O {\<langle>x,Fold(P,\<one>, n\<times>{x})\<rangle>. x\<in>G}\<rangle>. n\<in>nat}"
  shows "S`TheNeutralElement(int,IntegerMultiplication) = TheNeutralElement(End(G, P), Composition(G) {in End} [G,P])"
proof-
  have id:"TheNeutralElement(End(G, P), Composition(G) {in End} [G,P]) = id(G)" using end_comp_monoid(2).
  have S:"S`($# 1) = {\<langle>x,Fold(P,\<one>,1\<times>{x})\<rangle>. x\<in>G}"
    using apply_equality[OF _ group_action_int_1] unfolding S_def by auto
  {
    fix x assume x:"x\<in>G"
    have tail:"Tail(1\<times>{x}) = 0" using tail_props(1)[OF nat_0I, of "1\<times>{x}" G]
      using func1_3_L1[OF x, of 1] unfolding ConstantFunction_def by auto
    have apf:"(1\<times>{x})`0 = x" using apply_equality[of 0 x "1\<times>{x}"]
      using func1_3_L1[OF x, of 1] unfolding ConstantFunction_def
      by auto
    have "Fold(P,\<one>,1\<times>{x}) = Fold(P,\<one>\<cdot>x,0)" using fold_detach_first[of 0,
          OF nat_0I group_oper_fun _ group0_2_L2(1), of "1\<times>{x}"] tail
      func1_3_L1[OF x, of 1] apf unfolding ConstantFunction_def by auto
    then have "Fold(P,\<one>,1\<times>{x}) = x" using fold_empty[OF group_oper_fun
      _ x, of 0] group0_2_L2(2) x by auto
  }
  with S have "S`($# 1) = {\<langle>x,x\<rangle>. x\<in>G}" by auto
  then have "S`($# 1) = id(G)" unfolding id_def lambda_fun_alt by auto
  then show ?thesis using subst[OF int0.Int_ZF_1_L8(2), of "%t. S`t = id(G)"] subst[OF end_comp_monoid(2)[THEN sym], of "\<lambda>t. S`TheNeutralElement(int,IntegerMultiplication) =t"]
    by blast
qed

lemma(in abelian_group) group_action_int_2_5:
  assumes "z1\<in>nat" "z2\<in>nat" "g\<in>G"
  shows "Fold(P,\<one>,(z1#+z2)\<times>{g}) = Fold(P,\<one>,(z1)\<times>{g})\<cdot>Fold(P,\<one>,(z2)\<times>{g})"
proof(rule nat_induct[of z2 "\<lambda>t. Fold(P,\<one>,(z1#+t)\<times>{g}) = Fold(P,\<one>,z1\<times>{g})\<cdot>Fold(P,\<one>,t\<times>{g})"])
  {
    fix x na assume x:"x\<in>G" "na\<in>nat"
    have "Fold(P,\<one>,na\<times>{x})\<in>G" using fold_props(2)[OF x(2) group_oper_fun _ group0_2_L2(1),
          of "ConstantFunction(na,x)"] group0_2_L2(1) func1_3_L1[OF x(1)] unfolding ConstantFunction_def
      by auto
  }
  then have FG:"\<forall>n\<in>nat. \<forall>x\<in>G. Fold(P,\<one>,n\<times>{x})\<in>G" by auto
  from assms(2) show "z2:nat".
  have "Fold(P, \<one>, (z1 #+ 0) \<times> {g}) =Fold(P, \<one>, z1 \<times> {g})" using add_0_right assms(1) by auto
      moreover
  have "Fold(P,\<one>,0\<times>{g}) = \<one>" using fold_empty[OF group_oper_fun _ group0_2_L2(1)]
    assms(3) by auto
  then have "Fold(P, \<one>, z1 \<times> {g})\<cdot>Fold(P,\<one>,0\<times>{g}) = Fold(P, \<one>, z1 \<times> {g})"
    using group0_2_L2(2) FG assms(1,3) by auto
  ultimately
  show "Fold(P, \<one>, (z1 #+ 0) \<times> {g}) =Fold(P, \<one>, z1 \<times> {g})\<cdot>Fold(P,\<one>,0\<times>{g})" by auto
  {
    fix s assume s:"s\<in>nat"
    have "s\<times>{g}:s\<rightarrow>G" using func1_3_L1[OF assms(3)]
    have "Fold(P, \<one>, succ(s) \<times> {g}) = P`\<langle>Fold(P, \<one>,s\<times>{g}),g\<rangle>" using fold_append(2)[OF s
          group_oper_fun _ group0_2_L2(1) assms(3)]
    

lemma(in abelian_group) group_action_int_3:
  defines "S \<equiv> {\<langle>$# n,{\<langle>x,Fold(P,\<one>,n\<times>{x})\<rangle>. x\<in>G}\<rangle>. n\<in>nat}\<union> {\<langle>$- $# n,GroupInv(G,P) O {\<langle>x,Fold(P,\<one>, n\<times>{x})\<rangle>. x\<in>G}\<rangle>. n\<in>nat}"
  shows "\<forall>r\<in>int. \<forall>s\<in>int. \<forall>g\<in>G. S ` (IntegerAddition` \<langle>r, s\<rangle>) ` g = P ` \<langle>(S ` r) ` g, (S ` s) ` g\<rangle>"
proof(safe)
  fix r s g assume as:"r:int" "s:int" "g:G"
  from as(1) int_cases obtain n where n:"n\<in>nat" "r=$#n \<or> r=$- $# succ(n)" by auto
  from as(2) int_cases obtain m where m:"m\<in>nat" "s=$#m \<or> s=$- $# succ(m)" by auto
  {
    assume ass:"r=$#n" "s=$#m"
    then have "IntegerAddition`\<langle>r, s\<rangle> = $#(n#+m)" using int_of_add[of n m]
      int0.Int_ZF_1_L2 as(1,2) by auto
    moreover have "n#+m\<in>nat" by auto
    ultimately have "S ` (IntegerAddition` \<langle>r, s\<rangle>) `g = Fold(P,\<one>,(n#+m)\<times>{g})"
      using group_action_int_1_5(1)[of "n#+m", OF _ as(3)] unfolding S_def by auto
  

end