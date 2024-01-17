(* 
    This file is a part of IsarMathLib - 
    a library of formalized mathematics written for Isabelle/Isar.

    Copyright (C) 2024 Daniel de la Concepcion

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
EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.*)

section \<open>Regular Expressions\<close>

theory Regular_Expression_ZF imports Finite_State_Machines_ZF
begin

subsection\<open>Definition of REGEX\<close>

text\<open>We will define regular expression as a subset of all languages.
Identifying a regex with the language it defines.

We do this to simplify the theorems we will proof.\<close>

definition unit where
  "unit(x) \<equiv> {ConstantFunction(1,x)}"
definition union where
  "union(x,y) \<equiv> x\<union>y"
definition conc where
  "conc(x, y) \<equiv> {Concat(w1, w2) . \<langle>w1,w2\<rangle> \<in> x\<times>y}"
definition star where
  "star(x,\<Sigma>) \<equiv> lfp(Lists(\<Sigma>), %X. {0} \<union> {Concat(y,j). \<langle>y,j\<rangle>:X\<times>x})"

lemma empty_listI:
  shows "{0} \<subseteq> Lists(\<Sigma>)" unfolding Lists_def
  apply safe apply simp
proof
  show "0:0\<rightarrow>\<Sigma>" unfolding Pi_def function_def by auto
  from nat_0I show "0\<in>nat".
qed

lemma unitI:
  assumes "x\<in>\<Sigma>"
  shows "unit(x) \<subseteq> Lists(\<Sigma>)" unfolding unit_def
proof(safe)
  have "ConstantFunction(1, x) : 1 \<rightarrow> \<Sigma>" using assms
    func1_3_L1 by auto
  then show "ConstantFunction(1, x) \<in> Lists(\<Sigma>)" unfolding Lists_def
    using nat_1I by auto
qed

lemma concI:
  assumes "L1\<in>Pow(Lists(\<Sigma>))" "L2\<in>Pow(Lists(\<Sigma>))"
  shows "conc(L1,L2) \<subseteq> Lists(\<Sigma>)"
proof
  {
    fix w assume "w\<in>conc(L1,L2)"
    then obtain w1 w2 where w:"w=Concat(w1,w2)" "w1\<in>L1" "w2\<in>L2" using conc_def
      by auto
    from this(2,3) assms(2,1) obtain n1 n2 where "n1\<in>nat" "n2\<in>nat" "w1:n1\<rightarrow>\<Sigma>" "w2:n2\<rightarrow>\<Sigma>"
      unfolding Lists_def by blast
    then have "Concat(w1,w2):n1#+n2 \<rightarrow> \<Sigma>" "n1#+n2 \<in>nat" using concat_props(1) by auto
    with w(1) show "w\<in>Lists(\<Sigma>)" unfolding Lists_def by auto
  }
qed

lemma star_bnd_mono: 
  assumes "x\<in>Pow(Lists(\<Sigma>))"
  shows "bnd_mono(Lists(\<Sigma>), %X. {0} \<union> {Concat(y,j). \<langle>y,j\<rangle>:X\<times>x})"
  apply (rule bnd_monoI) apply simp apply auto
  using empty_listI apply simp
proof-
  {
    fix i q assume as:"i\<in>Lists(\<Sigma>)" "q\<in>x"
    from assms as(2) have "q\<in>Lists(\<Sigma>)" by auto
    moreover note as(1)
    ultimately obtain n1 n2 where "n1\<in>nat" "n2\<in>nat" "q:n1\<rightarrow>\<Sigma>" "i:n2\<rightarrow>\<Sigma>"
      unfolding Lists_def by blast
    then have "Concat(i,q):n2#+n1 \<rightarrow> \<Sigma>" "n2#+n1 \<in>nat" using concat_props(1) by auto
    then show "Concat(i,q)\<in>Lists(\<Sigma>)" unfolding Lists_def by auto
  }
qed
 
lemma star_unfold:
  assumes "x:Pow(Lists(\<Sigma>))"
  shows "star(x,\<Sigma>) = {0} \<union> {Concat(y,j). \<langle>y,j\<rangle>:star(x,\<Sigma>)\<times>x}"
  apply(rule def_lfp_unfold) using star_def apply auto
  using star_bnd_mono[OF assms] by auto

corollary star_sub:
  assumes "x:Pow(Lists(\<Sigma>))"
  shows "x \<subseteq> star(x,\<Sigma>)"
proof
  fix t assume "t:x"
  with assms have "t\<in>Lists(\<Sigma>)" by auto
  then obtain n where n:"t:n\<rightarrow>\<Sigma>" "n\<in>nat" unfolding Lists_def by auto
  have "0\<in>{0} \<union> {Concat(y,j). \<langle>y,j\<rangle>:star(x,\<Sigma>)\<times>x}" by auto
  then have "0\<in>star(x,\<Sigma>)" using star_unfold[OF assms] by auto
  with `t\<in>x` have "Concat(0,t): {Concat(y,j). \<langle>y,j\<rangle>:star(x,\<Sigma>)\<times>x}" by auto
  then have "t\<in>{Concat(y,j). \<langle>y,j\<rangle>:star(x,\<Sigma>)\<times>x}" using concat_0_left[of t] n by auto
  then have "t\<in>{0} \<union> {Concat(y,j). \<langle>y,j\<rangle>:star(x,\<Sigma>)\<times>x}" by auto
  then show "t\<in>star(x,\<Sigma>)" using star_unfold[OF assms] by auto
qed
  

lemma star_induct:
  assumes "x:Pow(Lists(\<Sigma>))"
  shows  "[| n \<in> star(x,\<Sigma>);  
    P(0);  
    !!j y. [| j \<in> star(x,\<Sigma>); y\<in>x;  P(j) |] ==> P(Concat(j,y)) |] ==> P(n)"
  using def_induct[of "star(x,\<Sigma>)" "Lists(\<Sigma>)" "\<lambda>X. {0} \<union> {Concat(j, y) . \<langle>j,y\<rangle> \<in> X \<times> x}" n P
     ,OF star_def star_bnd_mono[OF assms]] by auto

corollary starI:
  assumes "x:Pow(Lists(\<Sigma>))"
  shows "star(x,\<Sigma>) \<subseteq> Lists(\<Sigma>)"
  unfolding star_def using lfp_subset by auto

lemma unionI:
  assumes "L1\<in>Pow(Lists(\<Sigma>))" "L2\<in>Pow(Lists(\<Sigma>))"
  shows "union(L1,L2) \<subseteq> Lists(\<Sigma>)"
proof
  {
    fix w assume "w\<in>union(L1,L2)"
    then have "w\<in>L1 \<or> w\<in>L2" unfolding union_def by auto
    with assms show "w\<in>Lists(\<Sigma>)" by auto
  }
qed

consts
  Reg       :: "i\<Rightarrow>i"
inductive
  domains   "Reg(\<Sigma>)" \<subseteq> "Pow(Lists(\<Sigma>))"
  intros
    empty_regI:  "0 \<in> Reg(\<Sigma>)"
    emptyList_regI: "{0} \<in> Reg(\<Sigma>)"
    unit_regI: "x \<in> \<Sigma> \<Longrightarrow> unit(x) \<in> Reg(\<Sigma>)"
    conc_regI: "x \<in> Reg(\<Sigma>) \<Longrightarrow> y \<in> Reg(\<Sigma>) \<Longrightarrow> conc(x,y) \<in> Reg(\<Sigma>)"
    disj_regI: "x \<in> Reg(\<Sigma>) \<Longrightarrow> y \<in> Reg(\<Sigma>) \<Longrightarrow> union(x,y) \<in> Reg(\<Sigma>)"
    star_regI: "x \<in> Reg(\<Sigma>) \<Longrightarrow> star(x,\<Sigma>) \<in> Reg(\<Sigma>)"
  type_intros empty_subsetI PowI empty_listI unitI concI unionI starI

text\<open>Some secondary regular expressions\<close>

definition wild where
  "Finite(\<Sigma>) \<Longrightarrow> wild(\<Sigma>) \<equiv> \<Union>{unit(x). x\<in>\<Sigma>}"
definition quant where
  "r\<in>Reg(\<Sigma>) \<Longrightarrow> quant(r) \<equiv> union(r,{0})"


lemma wildI:
  assumes "Finite(\<Sigma>)"
  shows "wild(\<Sigma>)\<in>Reg(\<Sigma>)" unfolding wild_def[OF assms]
  apply (rule Finite1_L3) using Reg.empty_regI apply simp
proof(safe)
  fix A B assume "A\<in>Reg(\<Sigma>)" "B\<in>Reg(\<Sigma>)"
  then have "union(A,B)\<in>Reg(\<Sigma>)" using Reg.disj_regI by auto
  then show "A\<union>B\<in>Reg(\<Sigma>)" unfolding union_def by auto next
  from assms have "Finite({unit(x). x\<in>\<Sigma>})" using Finite_RepFun by auto
  moreover have "{unit(x). x\<in>\<Sigma>} \<subseteq> Reg(\<Sigma>)" using Reg.unit_regI by auto
  ultimately show "{unit(x). x\<in>\<Sigma>} \<in> Fin(Reg(\<Sigma>))"
    using Finite_Fin by auto
qed

corollary star_wild:
  assumes "Finite(\<Sigma>)"
  shows "star(wild(\<Sigma>),\<Sigma>) = Lists(\<Sigma>)"
proof
  have w:"wild(\<Sigma>): Pow(Lists(\<Sigma>))" using wildI[OF assms] Reg.dom_subset by auto
  show "star(wild(\<Sigma>),\<Sigma>) \<subseteq> Lists(\<Sigma>)"
    using star_regI[OF wildI[OF assms]] Reg.dom_subset by auto
  {
    fix t assume t:"t\<in>Lists(\<Sigma>)"
    {
      assume tne:"t\<in>NELists(\<Sigma>)"
      {
        fix b assume b:"b:1\<rightarrow>\<Sigma>"
        then have "b={\<langle>0,b`0\<rangle>}" using func_eq_set_of_pairs[of b 1 \<Sigma> "\<lambda>u. b`u"] by auto
        then have "b=ConstantFunction(1,b`0)" using const_fun_def_alt[of 1 "b`0"] by auto
        then have "b\<in>unit(b`0)" unfolding unit_def by auto moreover
        from b have "b`0\<in>\<Sigma>" using apply_type[of b 1 _ 0] by auto
        ultimately have "b\<in>wild(\<Sigma>)" unfolding wild_def[OF assms] by auto
        then have "b\<in>star(wild(\<Sigma>),\<Sigma>)" using star_sub w by auto
      }
      then have A:"\<forall>b\<in>1\<rightarrow>\<Sigma>. b\<in>star(wild(\<Sigma>),\<Sigma>)" by auto
      {
        fix b assume b:"b\<in>NELists(\<Sigma>)" "b \<in> star(wild(\<Sigma>), \<Sigma>)"
        from b obtain q where q:"q:nat" "b:succ(q)\<rightarrow>\<Sigma>" unfolding NELists_def by auto
        {
          fix s assume s:"s\<in>\<Sigma>"
          have "Append(b,s) = Concat(b,{\<langle>0,s\<rangle>})" using append_concat_pair[
                OF nat_succI[OF q(1)] q(2) s].
          moreover
          have "{\<langle>0,s\<rangle>} = ConstantFunction(1,s)" using const_fun_def_alt by auto
          then have "{\<langle>0,s\<rangle>}\<in>unit(s)" unfolding unit_def by auto
          with s have "{\<langle>0,s\<rangle>}\<in>wild(\<Sigma>)" unfolding wild_def[OF assms] by auto
          moreover note b(2) ultimately
          have "Append(b,s)\<in>{Concat(u,v). \<langle>u,v\<rangle>\<in>star(wild(\<Sigma>), \<Sigma>)\<times>wild(\<Sigma>)}"
            by auto
          then have "Append(b,s)\<in>{0}\<union>{Concat(u,v). \<langle>u,v\<rangle>\<in>star(wild(\<Sigma>), \<Sigma>)\<times>wild(\<Sigma>)}" by auto
          with star_unfold[OF w] have "Append(b,s)\<in>star(wild(\<Sigma>), \<Sigma>)" by auto
        }
        then have "\<forall>s\<in>\<Sigma>. Append(b,s)\<in>star(wild(\<Sigma>), \<Sigma>)" by auto
      }
      then have B:"\<forall>b\<in>NELists(\<Sigma>). b \<in> star(wild(\<Sigma>), \<Sigma>) \<longrightarrow> (\<forall>x\<in>\<Sigma>. Append(b, x) \<in> star(wild(\<Sigma>), \<Sigma>))" by auto
      with A tne have "t\<in>star(wild(\<Sigma>),\<Sigma>)" using list_induct[where P="\<lambda>t. t\<in>star(wild(\<Sigma>),\<Sigma>)", of \<Sigma> t]
        by auto
    } moreover
    {
      assume tt:"t\<notin>NELists(\<Sigma>)"
      from t obtain m where m:"m:nat" "t:m\<rightarrow>\<Sigma>" unfolding Lists_def by auto
      {
        assume "m\<noteq>0"
        with m(1) obtain q where q:"m=succ(q)" "q\<in>nat" using natE[of m "\<exists>q\<in>nat. m=succ(q)"] by auto
        with m(2) have "t\<in>NELists(\<Sigma>)" unfolding NELists_def by auto
        with tt have False by auto
      }
      then have "m=0" by auto
      with m(2) have "t=0" by auto
      then have "t:{0}" by auto
      then have "t\<in>{0} \<union> {Concat(y, j) . \<langle>y,j\<rangle> \<in> star(wild(\<Sigma>), \<Sigma>) \<times> wild(\<Sigma>)}" by auto
      then have "t:star(wild(\<Sigma>),\<Sigma>)" using star_unfold[OF w] by auto
    } ultimately have "t:star(wild(\<Sigma>),\<Sigma>)" by auto
  }
  then show "Lists(\<Sigma>) \<subseteq> star(wild(\<Sigma>), \<Sigma>)" by auto
qed
  
lemma quantI:
  assumes "r\<in>Reg(\<Sigma>)"
  shows "quant(r)\<in>Reg(\<Sigma>)"
  unfolding quant_def[OF assms] using Reg.disj_regI
    assms Reg.emptyList_regI by auto

theorem zero_to_one:
  defines "zTO1 \<equiv> conc(conc(unit(0),star(wild(2),2)),unit(1))"
  shows "zTO1 \<in> Reg(2)" "zTO1 = {i\<in>Lists(2). i`0 = 0 \<and> Last(i) = 1}"
proof-
  have star:"star(wild(2),2) \<in>Reg(2)" using Reg.star_regI[where \<Sigma>=2] wildI[OF nat_into_Finite[OF nat_2I]]
    by auto
  then have "conc(unit(0),star(wild(2),2)) \<in> Reg(2)" using Reg.conc_regI Reg.unit_regI[of 0 2] by auto
  then have "conc(conc(unit(0),star(wild(2),2)),unit(1)) \<in>Reg(2)" using Reg.conc_regI Reg.unit_regI[of 1 2] by auto
  then show "zTO1 \<in> Reg(2)" unfolding zTO1_def.
  have "zTO1 = {Concat(w1,w2). \<langle>w1,w2\<rangle>\<in>conc(unit(0),star(wild(2),2))\<times>unit(1)}"
    unfolding zTO1_def conc_def by auto
  then have "zTO1 = {Concat(w1,ConstantFunction(1,1)). w1:conc(unit(0),star(wild(2),2))}"
    unfolding unit_def by force
  then have "zTO1 = {Concat(Concat(w1,w2),ConstantFunction(1,1)). \<langle>w1,w2\<rangle>:unit(0)\<times>star(wild(2),2)}"
    unfolding conc_def by force
  then have z1_def:"zTO1 = {Concat(Concat(ConstantFunction(1,0),w2),ConstantFunction(1,1)). w2:star(wild(2),2)}"
    unfolding unit_def by force
  {
    fix t assume "t\<in>zTO1"
    with z1_def obtain w where w:"w\<in>star(wild(2),2)" "t=Concat(Concat(ConstantFunction(1,0),w),ConstantFunction(1,1))"
      by auto
    from w(1) star have A:"w\<in>Lists(2)" using Reg.dom_subset by auto
    then obtain n where AA:"n:nat" "w:n\<rightarrow>2" unfolding Lists_def by auto
    have BB:"ConstantFunction(1,0): 1 \<rightarrow> 2" unfolding ConstantFunction_def Pi_def function_def by auto
    then have B:"ConstantFunction(1,0):Lists(2)" unfolding Lists_def using nat_1I by auto
    have CC:"ConstantFunction(1,1): 1 \<rightarrow> 2" unfolding ConstantFunction_def Pi_def function_def by auto
    then have C:"ConstantFunction(1,1):Lists(2)" unfolding Lists_def using nat_1I by auto
    from AA BB have DD:"Concat(ConstantFunction(1,0),w)\<in>1#+n \<rightarrow> 2"
      using concat_props(1)[of 1 n _ 2] nat_1I by auto
    with CC have EE:"Concat(Concat(ConstantFunction(1,0),w),ConstantFunction(1,1))\<in>(1#+n)#+1 \<rightarrow> 2"
      using concat_props(1)[of "1#+n" 1 _ 2] nat_1I by auto
    with w(2) have T1:"t\<in>Lists(2)" unfolding Lists_def by auto
    have "0\<in>1#+n" using zero_less_add[OF AA(1) nat_1I] unfolding lt_def by auto moreover
    have "1#+n\<in>nat" by auto moreover
    have "t`0 = Concat(Concat(ConstantFunction(1,0),w),ConstantFunction(1,1))`0" using w(2) by auto
    ultimately have "t`0 = Concat(ConstantFunction(1,0),w)`0" using concat_props(2)[of "1#+n" 1 _ 2, OF _ nat_1I DD CC]
      by auto moreover
    have "0\<in>1" by auto
    ultimately have "t`0 = ConstantFunction(1,0)`0" using concat_props(2)[OF nat_1I AA(1) BB AA(2)] by auto
    then have T2:"t`0 = 0" using func1_3_L2 by auto
    from EE have "Concat(Concat(ConstantFunction(1,0),w),ConstantFunction(1,1))\<in>succ(1#+n) \<rightarrow> 2"
      using add_succ_right add_0_right by auto
    then have last:"Last(t) = t`(1#+n)" using last_seq_elem w(2) by auto
    have "t=Append
   (Concat(Concat(ConstantFunction(1, 0), w), Init(ConstantFunction(1, 1))), ConstantFunction(1, 1) ` 0)" using concat_init_last_elem[of "1#+n", OF _ nat_0I DD CC]
      w(2) by auto
    then have tt:"t=Append
   (Concat(Concat(ConstantFunction(1, 0), w), Init(ConstantFunction(1, 1))), 1)" using func1_3_L2 by auto
    have FF:"Init(ConstantFunction(1, 1)): 0 \<rightarrow> 2" using init_props(1)[OF nat_0I CC] by auto
    then have "Init(ConstantFunction(1, 1)) = 0" by auto
    then have GG:"Concat(Concat(ConstantFunction(1, 0), w), Init(ConstantFunction(1, 1))):(1#+n) \<rightarrow> 2"
      using concat_props(1)[of "1#+n", OF _ nat_0I DD FF] add_0_right by auto
    have "t`(1#+n) = 1" using append_props(3)[OF GG, of 1 t] tt by auto
    with last have T3:"Last(t) = 1" by auto
    with T1 T2 have "t\<in>{i\<in>Lists(2). i`0 = 0 \<and> Last(i) = 1}" by auto
  } 
  then have "zTO1 \<subseteq> {i\<in>Lists(2). i`0 = 0 \<and> Last(i) = 1}" by auto moreover
  {
    fix t assume t:"t\<in>Lists(2)" "t`0 = 0" "Last(t) = 1"
    from t(1) obtain n where n:"n\<in>nat" "t:n\<rightarrow>2" unfolding Lists_def by auto
    {
      assume "n=0"
      with n(2) have "t=0" by auto
      with t(3) have "Last(0) = 1" by auto
      then have False unfolding Last_def apply auto
        unfolding apply_def image_def by auto
    } moreover
    {
      fix q assume q:"n=succ(q)" "q\<in>nat"
      have A:"t`q=1" using last_seq_elem n(2) q(1) t(3) by auto
      from q n(2) have "t= Append(Init(t),t`q)" using init_props(3) by auto
      then have t3:"t = Concat(Init(t),ConstantFunction(1,1))" using append_1elem[OF _
        init_props(1)[OF q(2), of t 2], of "ConstantFunction(1,1)"] n(2) q(1) func1_3_L2[of 0 1 1] 
        func1_3_L1[of 1 2 1] q(2) A by auto
      then have "t`0 = Concat(Init(t),ConstantFunction(1,1))`0" by auto
      moreover have init:"Init(t):q\<rightarrow>2" using n(2) q init_props(1) by auto moreover
      {
        assume "q=0"
        with A t(2) have False by auto
      }
      with q(2) obtain s where s:"s\<in>nat" "q=succ(s)" using natE[of q "\<exists>s\<in>nat. q=succ(s)"] by auto
      from s have "0\<in>q" using nat_0_le unfolding lt_def by auto
      moreover have "ConstantFunction(1,1):1\<rightarrow>2" using func1_3_L1[of 1 2 1] by auto
      ultimately have "t`0 = Init(t)`0" using concat_props(2)[OF q(2) nat_1I, of "Init(t)" 2 
              "ConstantFunction(1,1)"] by auto
      then have "Init(t)`0 = 0" using t(2) by auto
      then have "ConstantFunction(1,0) = {\<langle>0,Init(t)`0\<rangle>}" unfolding ConstantFunction_def by auto
      then have "Init(t) = Concat(ConstantFunction(1,0), Tail(Init(t)))" 
        using first_concat_tail[OF s(1), of "Init(t)" 2] init s(2) by auto
      with t3 have T:"t=Concat(Concat(ConstantFunction(1,0), Tail(Init(t))),ConstantFunction(1,1))"
        by auto
      from init s have "Tail(Init(t)):s\<rightarrow>2" using tail_props(1) by auto
      with s(1) have "Tail(Init(t)):Lists(2)" unfolding Lists_def by auto
      with T have "t\<in>{Concat(Concat(ConstantFunction(1,0),w2),ConstantFunction(1,1)). w2:star(wild(2),2)}"
        using star_wild nat_into_Finite[OF nat_2I] by auto
      with z1_def have "t\<in>zTO1" by auto
    }
    ultimately have "t\<in>zTO1" using natE[OF n(1), of "t\<in>zTO1"] by auto
  }
  then have "{i \<in> Lists(2) . i ` 0 = 0 \<and> Last(i) = 1} \<subseteq> zTO1" by auto
  ultimately
  show "zTO1 = {i \<in> Lists(2) . i ` 0 = 0 \<and> Last(i) = 1}" by auto
qed

theorem unit_regular_language:
  assumes "Finite(\<Sigma>)" "x\<in>\<Sigma>"
  shows "unit(x) {is a regular language on}\<Sigma>"
proof-
  let ?Su = "succ(2)"
  let ?su = "0"
  let ?tu = "{\<langle>\<langle>0,s\<rangle>,2\<rangle>. s\<in>\<Sigma>-{x}}\<union>{\<langle>\<langle>0,x\<rangle>,1\<rangle>}\<union>{\<langle>\<langle>1,s\<rangle>,2\<rangle>. s\<in>\<Sigma>}\<union>{\<langle>\<langle>2,s\<rangle>,2\<rangle>. s\<in>\<Sigma>}"
  let ?Fu = "{1}"
  have "Finite(succ(2))" using nat_into_Finite[OF nat_succI[OF nat_2I]]. moreover
  have "0\<in>succ(2)" by auto moreover
  have "{1}\<subseteq>succ(2)" by auto moreover
  have tu:"?tu:succ(2)\<times>\<Sigma>\<rightarrow>succ(2)" unfolding Pi_def function_def using assms(2) by auto
  ultimately have dfsa:"(?Su,?su,?tu,?Fu){is an DFSA for alphabet}\<Sigma>"
    unfolding DFSA_def[OF assms(1)] by auto
  {
    fix t assume tt:"t\<in>unit(x)"
    then have t:"t=ConstantFunction(1,x)" unfolding unit_def by auto
    then have "t\<in>NELists(\<Sigma>)" unfolding NELists_def using func1_3_L1[OF assms(2)] by auto
    then have "\<langle>\<langle>t,?su\<rangle>,\<langle>Init(t),?tu`\<langle>?su,Last(t)\<rangle>\<rangle>\<rangle>\<in>({reduce D-relation}(?Su,?su,?tu){in alphabet}\<Sigma>)"
      unfolding DFSAExecutionRelation_def[OF assms(1) dfsa] by auto moreover
    have "Last(t) = t`0" using last_seq_elem[of t 0 \<Sigma>] func1_3_L1[OF assms(2), of 1] t
      by auto
    then have "Last(t) = x" using func1_3_L2[of 0 1 x] t by auto
    then have "?tu`\<langle>?su,Last(t)\<rangle> = 1" using apply_equality tu by auto moreover
    from t have "Init(t) =0" using func1_3_L1[of x \<Sigma> 1] assms(2) init_props(1)[OF nat_0I] by auto
    ultimately have "\<langle>\<langle>t,?su\<rangle>,\<langle>0,1\<rangle>\<rangle>\<in>({reduce D-relation}(?Su,?su,?tu){in alphabet}\<Sigma>)" by auto
    then have "\<exists>q\<in>?Fu. \<langle>\<langle>t,?su\<rangle>,\<langle>0,q\<rangle>\<rangle>\<in>({reduce D-relation}(?Su,?su,?tu){in alphabet}\<Sigma>)^*"
      using r_into_rtrancl by auto
    then have "t<-D (?Su,?su,?tu,?Fu){in alphabet}\<Sigma>" "t\<in>Lists(\<Sigma>)"
      using DFSASatisfy_def[OF assms(1) dfsa, of t] unitI[OF assms(2)] tt by auto
  }
  then have "unit(x) \<subseteq> {t\<in>Lists(\<Sigma>). t<-D (?Su,?su,?tu,?Fu){in alphabet}\<Sigma>}" by auto
  moreover
  {
    fix t assume t:"t\<in>Lists(\<Sigma>)" "t<-D (?Su,?su,?tu,?Fu){in alphabet}\<Sigma>"
    from t have "\<exists>q\<in>?Fu. \<langle>\<langle>t,?su\<rangle>,\<langle>0,q\<rangle>\<rangle>\<in>({reduce D-relation}(?Su,?su,?tu){in alphabet}\<Sigma>)^*"
      unfolding DFSASatisfy_def[OF assms(1) dfsa t(1)] by auto
    then have "\<langle>\<langle>t,?su\<rangle>,\<langle>0,1\<rangle>\<rangle>\<in>({reduce D-relation}(?Su,?su,?tu){in alphabet}\<Sigma>)^*" by auto moreover
    have "\<langle>\<langle>t,?su\<rangle>,\<langle>0,1\<rangle>\<rangle>\<notin>id(field({reduce D-relation}(?Su,?su,?tu){in alphabet}\<Sigma>))" by auto ultimately
    have "\<langle>\<langle>t,?su\<rangle>,\<langle>0,1\<rangle>\<rangle>\<notin>id(field({reduce D-relation}(?Su,?su,?tu){in alphabet}\<Sigma>))" "\<langle>\<langle>t,?su\<rangle>,\<langle>0,1\<rangle>\<rangle>\<in>id(field({reduce D-relation}(?Su,?su,?tu){in alphabet}\<Sigma>)) \<union> ((({reduce D-relation}(?Su,?su,?tu){in alphabet}\<Sigma>)^*) O ({reduce D-relation}(?Su,?su,?tu){in alphabet}\<Sigma>))" 
      using rtrancl_rev[of "({reduce D-relation}(?Su,?su,?tu){in alphabet}\<Sigma>)"] by auto
    then have "\<langle>\<langle>t,?su\<rangle>,\<langle>0,1\<rangle>\<rangle>:((({reduce D-relation}(?Su,?su,?tu){in alphabet}\<Sigma>)^*) O ({reduce D-relation}(?Su,?su,?tu){in alphabet}\<Sigma>))"
      by auto
    then obtain q where q:"\<langle>\<langle>t,?su\<rangle>,q\<rangle>\<in>({reduce D-relation}(?Su,?su,?tu){in alphabet}\<Sigma>)"
      "\<langle>q,\<langle>0,1\<rangle>\<rangle>\<in>({reduce D-relation}(?Su,?su,?tu){in alphabet}\<Sigma>)^*" using compE by auto
    from q(1) have qq:"q=\<langle>Init(t),?tu`\<langle>?su,Last(t)\<rangle>\<rangle>" "t\<in>NELists(\<Sigma>)" 
      unfolding DFSAExecutionRelation_def[OF assms(1) dfsa] by auto
    have "snd(fst(\<langle>q, 0, 1\<rangle>)) = 2 \<longrightarrow> snd(snd(\<langle>q, 0, 1\<rangle>)) = 2"
    proof(rule rtrancl_full_induct[of q "\<langle>0,1\<rangle>" "{reduce D-relation}(?Su,?su,?tu){in alphabet}\<Sigma>"
    "\<lambda>u. snd(fst(u)) = 2 \<longrightarrow> snd(snd(u)) =2", OF q(2)])
      {
        fix v assume "v\<in>field({reduce D-relation}(?Su,?su,?tu){in alphabet}\<Sigma>)"
        then show "snd(fst(\<langle>v,v\<rangle>)) = 2 \<longrightarrow> snd(snd(\<langle>v,v\<rangle>)) = 2" by auto
      }
      {
        fix xa y z assume as:"snd(fst(\<langle>xa, y\<rangle>)) = 2 \<longrightarrow> snd(snd(\<langle>xa, y\<rangle>)) = 2"
      "\<langle>xa, y\<rangle> \<in>({reduce D-relation}(succ(2),0,?tu){in alphabet}\<Sigma>)^*"
      "\<langle>y, z\<rangle> \<in>{reduce D-relation}(succ(2),0,?tu){in alphabet}\<Sigma>"
        {
          assume ass:"snd(fst(\<langle>xa, z\<rangle>)) = 2"
          from ass have "snd(xa) = 2" by auto
          with as(1) have yy:"snd(y) = 2" by auto
          from as(3) obtain l s where y:"y=\<langle>l,s\<rangle>" "s:?Su" "l:NELists(\<Sigma>)" "z=\<langle>Init(l),?tu`\<langle>s,Last(l)\<rangle>\<rangle>"
            unfolding DFSAExecutionRelation_def[OF assms(1) dfsa] by auto
          from yy y(1) have "s=2" by auto
          with y(4) have "z=\<langle>Init(l),?tu`\<langle>2,Last(l)\<rangle>\<rangle>" by auto
          moreover have "Last(l)\<in>\<Sigma>" using last_type y(3) by auto
          ultimately have "snd(snd(\<langle>xa, z\<rangle>)) = 2" using apply_equality tu by auto
        }
        then show "snd(fst(\<langle>xa, z\<rangle>)) = 2 \<longrightarrow> snd(snd(\<langle>xa, z\<rangle>)) = 2" by auto
      }
    qed
    then have q2:"snd(q)\<noteq>2" by auto
    {
      assume "Last(t)\<noteq>x"
      then have "Last(t)\<in>\<Sigma>-{x}" using last_type[OF qq(2)] by auto
      then have "?tu`\<langle>?su,Last(t)\<rangle> = 2" using apply_equality tu by auto
      with qq(1) q2 have False by auto
    }
    then have lx:"Last(t) = x" by auto
    then have u:"?tu`\<langle>?su,Last(t)\<rangle> = 1" using tu apply_equality by auto
    {
      assume z:"Init(t)\<noteq>0"
      from u q(2) qq(1) have r:"\<langle>\<langle>Init(t),1\<rangle>,\<langle>0,1\<rangle>\<rangle>\<in>({reduce D-relation}(succ(2),0,?tu){in alphabet}\<Sigma>)^*" by auto
      with z have zz:"\<langle>\<langle>Init(t),1\<rangle>,\<langle>0,1\<rangle>\<rangle>\<notin>id(field({reduce D-relation}(succ(2),0,?tu){in alphabet}\<Sigma>))" by auto
      from r have "\<langle>\<langle>Init(t),1\<rangle>,\<langle>0,1\<rangle>\<rangle>\<in>id(field({reduce D-relation}(succ(2),0,?tu){in alphabet}\<Sigma>)) \<union> (({reduce D-relation}(succ(2),0,?tu){in alphabet}\<Sigma>)^* O ({reduce D-relation}(succ(2),0,?tu){in alphabet}\<Sigma>))"
        using rtrancl_rev[of "({reduce D-relation}(succ(2),0,?tu){in alphabet}\<Sigma>)"] by auto
      with zz have "\<langle>\<langle>Init(t),1\<rangle>,\<langle>0,1\<rangle>\<rangle>\<in>(({reduce D-relation}(succ(2),0,?tu){in alphabet}\<Sigma>)^* O ({reduce D-relation}(succ(2),0,?tu){in alphabet}\<Sigma>))" by auto
      then obtain h where hh:"\<langle>\<langle>Init(t),1\<rangle>,h\<rangle>\<in>({reduce D-relation}(succ(2),0,?tu){in alphabet}\<Sigma>)" "\<langle>h,\<langle>0,1\<rangle>\<rangle>\<in>({reduce D-relation}(succ(2),0,?tu){in alphabet}\<Sigma>)^*"
        using compE by auto
      then have h:"Init(t)\<in>NELists(\<Sigma>)" "h=\<langle>Init(Init(t)),?tu`\<langle>1,Last(Init(t))\<rangle>\<rangle>" unfolding DFSAExecutionRelation_def[OF assms(1) dfsa] by auto
      from h(1) have "Last(Init(t)) \<in>\<Sigma>" using last_type by auto
      with h(2) have h_def:"h=\<langle>Init(Init(t)),2\<rangle>" using apply_equality tu by auto
      have "snd(fst(\<langle>h, 0, 1\<rangle>)) = 2 \<longrightarrow> snd(snd(\<langle>h, 0, 1\<rangle>)) = 2"
      proof(rule rtrancl_full_induct[of h "\<langle>0,1\<rangle>" "{reduce D-relation}(?Su,?su,?tu){in alphabet}\<Sigma>"
      "\<lambda>u. snd(fst(u)) = 2 \<longrightarrow> snd(snd(u)) =2", OF hh(2)])
        {
          fix v assume "v\<in>field({reduce D-relation}(?Su,?su,?tu){in alphabet}\<Sigma>)"
          then show "snd(fst(\<langle>v,v\<rangle>)) = 2 \<longrightarrow> snd(snd(\<langle>v,v\<rangle>)) = 2" by auto
        }
        {
          fix xa y z assume as:"snd(fst(\<langle>xa, y\<rangle>)) = 2 \<longrightarrow> snd(snd(\<langle>xa, y\<rangle>)) = 2"
        "\<langle>xa, y\<rangle> \<in>({reduce D-relation}(succ(2),0,?tu){in alphabet}\<Sigma>)^*"
        "\<langle>y, z\<rangle> \<in>{reduce D-relation}(succ(2),0,?tu){in alphabet}\<Sigma>"
          {
            assume ass:"snd(fst(\<langle>xa, z\<rangle>)) = 2"
            from ass have "snd(xa) = 2" by auto
            with as(1) have yy:"snd(y) = 2" by auto
            from as(3) obtain l s where y:"y=\<langle>l,s\<rangle>" "s:?Su" "l:NELists(\<Sigma>)" "z=\<langle>Init(l),?tu`\<langle>s,Last(l)\<rangle>\<rangle>"
              unfolding DFSAExecutionRelation_def[OF assms(1) dfsa] by auto
            from yy y(1) have "s=2" by auto
            with y(4) have "z=\<langle>Init(l),?tu`\<langle>2,Last(l)\<rangle>\<rangle>" by auto
            moreover have "Last(l)\<in>\<Sigma>" using last_type y(3) by auto
            ultimately have "snd(snd(\<langle>xa, z\<rangle>)) = 2" using apply_equality tu by auto
          }
          then show "snd(fst(\<langle>xa, z\<rangle>)) = 2 \<longrightarrow> snd(snd(\<langle>xa, z\<rangle>)) = 2" by auto
        }
      qed
      with h_def have False by auto
    }
    then have z:"Init(t) = 0" by auto
    from qq(2) obtain n where t:"t:succ(n)\<rightarrow>\<Sigma>" "n\<in>nat" unfolding NELists_def by auto
    then have "Init(t):n\<rightarrow>\<Sigma>" using init_props(1) by auto
    with z have "n=0" unfolding Pi_def apply simp by auto
    with t(1) have t_fun:"t:1\<rightarrow>\<Sigma>" by auto
    then have "t={\<langle>0,t`0\<rangle>}" using fun_is_set_of_pairs[of t 1 \<Sigma>] by auto
    then have "t=ConstantFunction(1,t`0)" using const_fun_def_alt by auto moreover
    have "t`0=Last(t)" using last_seq_elem t_fun by auto moreover note lx
    ultimately have "t= ConstantFunction(1,x)" by auto
    then have "t\<in>unit(x)" unfolding unit_def by auto
  }
  ultimately have "unit(x) = {t\<in>Lists(\<Sigma>). t<-D (?Su,?su,?tu,?Fu){in alphabet}\<Sigma>}" by auto
  then show "unit(x) {is a regular language on}\<Sigma>"
    unfolding IsRegularLanguage_def[OF assms(1)] using dfsa by auto
qed


theorem union_regular_language:
  assumes "Finite(\<Sigma>)" "x\<in>Reg(\<Sigma>)" "y\<in>Reg(\<Sigma>)" 
    "x{is a regular language on}\<Sigma>" "y{is a regular language on}\<Sigma>"
  shows "union(x,y) {is a regular language on}\<Sigma>"
proof-
  from assms(1,4,5) have "(x\<union>y) {is a regular language on}\<Sigma>"
    using regular_union by auto
  then show "union(x,y) {is a regular language on}\<Sigma>"
    unfolding union_def.
qed

theorem reg_is_regular_language:
  assumes "Finite(\<Sigma>)"
  shows "Reg(\<Sigma>) = {L\<in>Pow(Lists(\<Sigma>)). L{is a regular language on}\<Sigma>}"
proof
  have z:"0 \<in> {L \<in> Pow(Lists(\<Sigma>)) . L{is a regular language on}\<Sigma>}" using regular_0 assms by auto
  have "0:0\<rightarrow>\<Sigma>" by auto
  then have "0\<in>Lists(\<Sigma>)" unfolding Lists_def using nat_0I by blast
  then have "{0}\<in>Pow(Lists(\<Sigma>))" by auto
  then have emp:"{0} \<in> {L \<in> Pow(Lists(\<Sigma>)) . L{is a regular language on}\<Sigma>}" using regular_empty_word assms by auto
  have "\<And>x. x\<in>\<Sigma> \<Longrightarrow> unit(x)\<in>{L \<in> Pow(Lists(\<Sigma>)) . L{is a regular language on}\<Sigma>}" using unit_regular_language
    assms unit_regI[THEN subsetD[OF Reg.dom_subset]] by auto
  show "Reg(\<Sigma>) \<subseteq> {L \<in> Pow(Lists(\<Sigma>)). L{is a regular language on}\<Sigma>}"
    using Reg.induct[of _ \<Sigma>, where P="\<lambda>q. q\<in>{L \<in> Pow(Lists(\<Sigma>)). L{is a regular language on}\<Sigma>}", OF _ z emp]
      
      
      
  
  

end