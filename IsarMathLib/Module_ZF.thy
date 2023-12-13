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

theory Module_ZF imports Group_ZF_5 Ring_ZF_1
  CommutativeSemigroup_ZF

begin

section \<open>Ring modules\<close>

text \<open>A ring module is a structure given by a ring $R$, an abelian group $M$
  and a ring homomorphism $S:R\to End(M,+)$ such that $S(1)=id(G)$.\<close>

definition
  "IsAmodule(R,AR,MR,M,AM,S) \<equiv> 
  (IsAring(R,AR,MR) \<and> IsAgroup(M,AM) \<and> AM{is commutative on}M \<and>
  S:R\<rightarrow>End(M,AM) \<and> (\<forall>r\<in>R. \<forall>s\<in>R. S`(AR`\<langle>r,s\<rangle>)=(AM{lifted to function space over}M)`\<langle>S`r,S`s\<rangle>)\<and>
  (\<forall>r\<in>R. \<forall>s\<in>R. S`(MR`\<langle>r,s\<rangle>)=Composition(M)`\<langle>S`r,S`s\<rangle>)
  \<and>( S`(TheNeutralElement(R,MR))=TheNeutralElement(End(M,AM),restrict(Composition(M),End(M,AM)\<times>End(M,AM)))))"

text \<open>Let\<acute>s define a module locale:\<close>

locale module0 =

fixes R and A and M 
 
  assumes ringAssum: "IsAring(R,A,M)"

  fixes ringa (infixl "\<ra>\<^sub>R" 90)
  defines ringa_def [simp]: "aa\<ra>\<^sub>R b \<equiv> A`\<langle> aa,b\<rangle>"

  fixes ringminus ("\<rm>\<^sub>R _" 89)
  defines ringminus_def [simp]: "(\<rm>\<^sub>R b) \<equiv> GroupInv(R,A)`(b)"

  fixes ringsub (infixl "\<rs>\<^sub>R" 90)
  defines ringsub_def [simp]: "c\<rs>\<^sub>R b \<equiv> c\<ra>\<^sub>R(\<rm>\<^sub>R b)"

  fixes ringm (infixl "\<cdot>\<^sub>R" 95)
  defines ringm_def [simp]: "c\<cdot>\<^sub>R b \<equiv> M`\<langle> c,b\<rangle>"

  fixes ringzero ("\<zero>\<^sub>R")
  defines ringzero_def [simp]: "\<zero>\<^sub>R \<equiv> TheNeutralElement(R,A)"

  fixes ringone ("\<one>\<^sub>R")
  defines ringone_def [simp]: "\<one>\<^sub>R \<equiv> TheNeutralElement(R,M)"

  fixes ringtwo ("\<two>\<^sub>R")
  defines ringtwo_def [simp]: "\<two>\<^sub>R \<equiv> \<one>\<^sub>R\<ra>\<^sub>R \<one>\<^sub>R"

  fixes ringsq ("_\<twosuperior>" [96] 97)
  defines ringsq_def [simp]: "b\<twosuperior> \<equiv> b\<cdot>\<^sub>Rb"

  fixes G f
  assumes Ggroup: "IsAgroup(G,f)"

  fixes grop (infixl "\<ra>\<^sub>G" 90)
  defines grop_def [simp]: "x\<ra>\<^sub>Gy \<equiv> f`\<langle>x,y\<rangle>"

  fixes grinv ("\<rm>\<^sub>G _" 89)
  defines grinv_def [simp]: "(\<rm>\<^sub>G x) \<equiv> GroupInv(G,f)`(x)"

  fixes grsub (infixl "\<rs>\<^sub>G" 90)
  defines grsub_def [simp]: "x\<rs>\<^sub>G y \<equiv> x\<ra>\<^sub>G(\<rm>\<^sub>Gy)"

  fixes gzero ("\<zero>\<^sub>G")
  defines gzero_def [simp]: "\<zero>\<^sub>G \<equiv> TheNeutralElement(G,f)"

  assumes Gabelian: "f{is commutative on}G"

  fixes S

  fixes action (infixl "\<cdot>\<^sub>M" 90)
  defines action_def [simp]: "r \<cdot>\<^sub>M m \<equiv> (S`r)`m"

  assumes S_fun: "S:R\<rightarrow>End(G,f)"

  assumes S_dist1: "\<forall>r\<in>R. \<forall>s\<in>R. \<forall>g\<in>G. (r\<ra>\<^sub>Rs)\<cdot>\<^sub>M g=(r\<cdot>\<^sub>M g)\<ra>\<^sub>G(s\<cdot>\<^sub>M g)"
  assumes S_dist2: "\<forall>r\<in>R. \<forall>s\<in>R. \<forall>g\<in>G. (r\<cdot>\<^sub>Rs)\<cdot>\<^sub>M g=(r \<cdot>\<^sub>M(s\<cdot>\<^sub>M g))"

  assumes S_one: "S`(\<one>\<^sub>R)=id(G)"

text \<open>The module is an abelian group.\<close>

sublocale module0 < ab_group:"abelian_group" G f "\<zero>\<^sub>G" "\<lambda>x y. x\<ra>\<^sub>Gy"
  "\<lambda>x. \<rm>\<^sub>Gx" using Gabelian Ggroup unfolding grop_def gzero_def
  grinv_def unfolding abelian_group_def group0_def abelian_group_axioms_def by auto

text \<open>The module has an action from a ring.\<close>

sublocale module0 < ring:"ring0" R A M
  unfolding ringa_def ringm_def ringminus_def ringone_def
  ringsq_def ringsub_def ringtwo_def ringzero_def ring0_def
  using ringAssum by auto

text \<open>In the context @{text "module0"}, we have a module.\<close>

lemma(in module0) isAmodule:
  shows "IsAmodule(R,A,M,G,f,S)"
proof-
  have A1:"IsAring(R,A,M)" using ringAssum by auto
  have A2:"IsAgroup(G,f)" using Ggroup by auto
  have A3:"f{is commutative on}G" using Gabelian by auto 
  have A4:"S:R\<rightarrow>End(G,f)" using S_fun by auto
  {
    fix r s assume AS:"r\<in>R""s\<in>R"
    then have EE:"S`r\<in>End(G,f)""S`s\<in>End(G,f)" using apply_type[OF S_fun] by auto
    {
      fix g assume AS2:"g\<in>G"
      with EE have ff:"((f{lifted to function space over}G)`\<langle>S`r,S`s\<rangle>)`g=((S`r)`g)\<ra>\<^sub>G((S`s)`g)"
        using ab_group.Group_ZF_2_1_L3 unfolding End_def by auto
      from AS AS2 have "(S`(A`\<langle>r,s\<rangle>))`g=(r\<cdot>\<^sub>M g)\<ra>\<^sub>G(s\<cdot>\<^sub>M g)" using S_dist1 by auto
      then have "(S`(A`\<langle>r,s\<rangle>))`g=((S`r)`g)\<ra>\<^sub>G((S`s)`g)" by auto
      with ff have "((f{lifted to function space over}G)`\<langle>S`r,S`s\<rangle>)`g=(S`(A`\<langle>r,s\<rangle>))`g" by auto
    }
    then have reg:"\<forall>g\<in>G. ((f{lifted to function space over}G)`\<langle>S`r,S`s\<rangle>)`g=(S`(A`\<langle>r,s\<rangle>))`g" by auto
    have FS:"(f{lifted to function space over}G)`\<langle>S`r,S`s\<rangle>:G\<rightarrow>G" using EE monoid0.Group_ZF_2_1_L0[OF ab_group.group0_2_L1
      ] unfolding End_def by auto
    have "A`\<langle>r,s\<rangle>\<in>R" using ring.Ring_ZF_1_L4(1) AS by auto
    then have SA:"(S`(A`\<langle>r,s\<rangle>)):G\<rightarrow>G" using apply_type[OF S_fun] unfolding End_def by auto
    have "(f{lifted to function space over}G)`\<langle>S`r,S`s\<rangle>=S`(A`\<langle>r,s\<rangle>)" using fun_extension[OF FS SA] reg by auto
  }
  then have A5:"\<forall>r\<in>R. \<forall>s\<in>R. (S`(A`\<langle>r,s\<rangle>))=((f{lifted to function space over}G)`\<langle>S`r,S`s\<rangle>)" by auto
  {
    fix r s assume AS:"r\<in>R""s\<in>R"
    then have "S`r\<in>End(G,f)""S`s\<in>End(G,f)" using apply_type[OF S_fun] by auto
    then have SG:"S`r:G\<rightarrow>G""S`s:G\<rightarrow>G" unfolding End_def by auto
    then have comp:"Composition(G)`\<langle>S`r,S`s\<rangle>=(S`r)O(S`s)" using func_ZF_5_L2 by auto
    from AS have "r\<cdot>\<^sub>R s\<in>R" using ring.Ring_ZF_1_L4(3) by auto
    then have B1:"S`(r\<cdot>\<^sub>R s):G\<rightarrow>G" using apply_type[OF S_fun] unfolding End_def by auto
    have B2:"(Composition(G)`\<langle>S`r,S`s\<rangle>):G\<rightarrow>G" using comp SG comp_fun by auto
    {
      fix g assume gg:"g\<in>G"
      with AS have "(S`(M`\<langle>r,s\<rangle>))`g=(r \<cdot>\<^sub>M(s\<cdot>\<^sub>M g))" using S_dist2 by auto
      then have "(S`(M`\<langle>r,s\<rangle>))`g=(S`r)`((S`s)`g)" by auto
      then have "(S`(M`\<langle>r,s\<rangle>))`g=((S`r)O(S`s))`g" using comp_fun_apply[OF SG(2) gg] by auto  
      with comp have "(S`(M`\<langle>r,s\<rangle>))`g=(Composition(G)`\<langle>S`r,S`s\<rangle>)`g" by auto
    }
    then have "S`(M`\<langle>r,s\<rangle>)=Composition(G)`\<langle>S`r,S`s\<rangle>" using fun_extension[OF B1 B2] by auto
  }
  then have A6:"\<forall>r\<in>R. \<forall>s\<in>R. S`(M`\<langle>r,s\<rangle>)=Composition(G)`\<langle>S`r,S`s\<rangle>" using S_dist2 by auto
  have "id(G) = TheNeutralElement(End(G,f),restrict(Composition(G),End(G,f)\<times>End(G,f)))"
    using ab_group.end_comp_monoid(2)[THEN sym] .
  then have "S`(TheNeutralElement(R, M))=TheNeutralElement(End(G,f),restrict(Composition(G),End(G,f)\<times>End(G,f)))"
    using S_one trans[of "S`(TheNeutralElement(R, M))" "id(G)" "TheNeutralElement(End(G, f), Composition(G) {in End} [G,f])"]
    unfolding ringone_def by blast
  with A1 A2 A3 A4 A5 A6 show ?thesis unfolding IsAmodule_def by blast
qed

text \<open>When we have a module, then we can use the results in @{text "module0"}.\<close>

lemma isAmodule_imp_module0:
  assumes "IsAmodule(R,A,M,G,f,S)"
  shows "module0(R,A,M,G,f,S)" unfolding module0_def
proof(safe)
  show "IsAring(R, A, M)" using assms unfolding IsAmodule_def by auto
  show A2:"IsAgroup(G,f)" using assms unfolding IsAmodule_def by auto
  show A3:"f{is commutative on}G" using assms unfolding IsAmodule_def by auto
  show A4:"S:R\<rightarrow>End(G,f)" using assms unfolding IsAmodule_def by auto
  have "TheNeutralElement(End(G,f),restrict(Composition(G),End(G,f)\<times>End(G,f)))=id(G)"
    using group0.end_comp_monoid(2) A2 unfolding group0_def by force
  then show "S ` TheNeutralElement(R, M) = id(G)" using assms unfolding IsAmodule_def by auto
  fix r s g assume "r\<in>R" "s\<in>R" "g\<in>G"
  then have SF:"S ` (A ` \<langle>r, s\<rangle>) = (f {lifted to function space over} G) ` \<langle>S ` r, S ` s\<rangle>" using assms unfolding IsAmodule_def by auto
  from `r\<in>R``s\<in>R` have SG:"S`r:G\<rightarrow>G""S`s:G\<rightarrow>G" using apply_type[OF A4] unfolding End_def by auto
  show "S ` (A ` \<langle>r, s\<rangle>) ` g = f ` \<langle>(S ` r) ` g, (S ` s) ` g\<rangle>" using group0.Group_ZF_2_1_L3[OF _ _ SG `g\<in>G`] SF A2 unfolding group0_def by auto
  from `r\<in>R``s\<in>R` have SF:"S`(M`\<langle>r,s\<rangle>)=Composition(G) ` \<langle>S ` r, S ` s\<rangle>" using assms unfolding IsAmodule_def by auto
  then have "S`(M`\<langle>r,s\<rangle>)= (S ` r)O (S ` s)" using func_ZF_5_L2[OF SG] by auto
  then have "(S`(M`\<langle>r,s\<rangle>))`g= ((S ` r)O (S ` s))`g" by auto
  with `g\<in>G` show "(S`(M`\<langle>r,s\<rangle>))`g= (S ` r)`((S ` s)`g)" using comp_fun_apply[OF SG(2)] by auto
qed

text\<open>The function $S:R\to End(M,+)$ is an homomorphism of groups considering
the addition in $R$\<close>

lemma(in module0) S_homomor:
  defines "F \<equiv> InEnd(f{lifted to function space over}G,G,f)"
  shows "Homomor(S,R,A,End(G,f),F)"
proof-
  have "IsAgroup(R,A)" using ringAssum unfolding IsAring_def by auto moreover
  have "IsAgroup(End(G,f),F)" unfolding F_def using ab_group.end_addition_group(1) by auto moreover
  {
    fix r s assume AS:"r\<in>R""s\<in>R"
    then have fun:"S`r\<in>End(G,f)""S`s\<in>End(G,f)" using apply_type S_fun by auto
    then have fun2:"S`r:G\<rightarrow>G""S`s:G\<rightarrow>G" unfolding End_def by auto
    {
      fix g assume g:"g\<in>G"
      with AS have "(r\<ra>\<^sub>Rs)\<cdot>\<^sub>Mg=(r\<cdot>\<^sub>M g)\<ra>\<^sub>G(s\<cdot>\<^sub>M g)" using S_dist1 by auto
      then have "(S`(A`\<langle>r,s\<rangle>))`g=f`\<langle>(S`r)`g,(S`s)`g\<rangle>" by auto
      then have "(S`(A`\<langle>r,s\<rangle>))`g=(F`\<langle>(S`r),(S`s)\<rangle>)`g" using ab_group.Group_ZF_2_1_L3[OF _ fun2 g]
        assms fun by auto
    }
    then have reg:"\<forall>g\<in>G. (S`(A`\<langle>r,s\<rangle>))`g=(F`\<langle>(S`r),(S`s)\<rangle>)`g" by auto moreover
    from AS have "A`\<langle>r,s\<rangle>\<in>R" using ring.Ring_ZF_1_L4(1) by auto
    then have f1:"S`(A`\<langle>r,s\<rangle>):G\<rightarrow>G" using apply_type[OF S_fun] unfolding End_def by auto
    have f2:"F`\<langle>(S`r),(S`s)\<rangle>:G\<rightarrow>G" using assms fun ab_group.monoid.Group_ZF_2_1_L0[OF _ fun2] by auto
    from reg have "S`(A`\<langle>r,s\<rangle>)=F`\<langle>(S`r),(S`s)\<rangle>" using fun_extension[OF f1 f2] by auto
  }
  ultimately show ?thesis using Homomor_def by auto
qed
 
text \<open>The multiplication by zero, gives zero.\<close>

lemma(in module0) mult_zeroG:
  assumes "r\<in>R"
  shows "r \<cdot>\<^sub>M \<zero>\<^sub>G=\<zero>\<^sub>G"
proof-
  have "S`r\<in>End(G,f)" using S_fun assms apply_type by auto
  then have "Homomor(S`r,G,f,G,f)" "S`r:G\<rightarrow>G" unfolding End_def by auto
  moreover have "IsAgroup(G,f)" using Ggroup by auto
  ultimately have "(S`r)`\<zero>\<^sub>G=\<zero>\<^sub>G" using image_neutral by auto
  then show ?thesis by auto
qed

text\<open>The zero ring element should be the
constant endomorphism to the neutral group element.\<close>

lemma(in module0) mult_zeroR:
  assumes "g\<in>G"
  shows "\<zero>\<^sub>R \<cdot>\<^sub>M g=\<zero>\<^sub>G"
proof-
  let ?F="restrict(f{lifted to function space over}G,End(G,f)\<times>End(G,f))"
  have "IsAgroup(R,A)" using ringAssum unfolding IsAring_def by auto moreover
  have "IsAgroup(End(G,f),?F)" using ab_group.end_addition_group(1) by auto moreover
  have "Homomor(S,R,A,End(G,f),?F)" using S_homomor assms by auto
  ultimately have A1:"S`\<zero>\<^sub>R=TheNeutralElement(End(G,f),?F)" 
    using image_neutral[of R A "End(G,f)" _ S] S_fun
    unfolding ringzero_def by blast moreover
  have "IsAgroup(G\<rightarrow>G,f{lifted to function space over}G)" using ab_group.Group_ZF_2_1_T2
    by auto
  then have "TheNeutralElement(End(G,f),?F)=TheNeutralElement(G\<rightarrow>G,f{lifted to function space over}G)" 
    using group0.group0_3_L4[of "G\<rightarrow>G" "f{lifted to function space over}G" "End(G,f)"]
    using ab_group.end_addition_group(1)[of "f{lifted to function space over}G"] 
    unfolding IsAsubgroup_def group0_def by blast
  then have A2:"TheNeutralElement(End(G,f),?F)=ConstantFunction(G, \<zero>\<^sub>G)" using ab_group.monoid.Group_ZF_2_1_L2[of G, THEN sym] 
    unfolding gzero_def using trans[of "TheNeutralElement(End(G, f), InEnd(f {lifted to function space over} G, G, f))"
    "TheNeutralElement(G \<rightarrow> G, f {lifted to function space over} G)" "ConstantFunction(G, TheNeutralElement(G, f))"]
    by blast
  have "(S`\<zero>\<^sub>R)`g=\<zero>\<^sub>G" using func1_3_L2[of g G "\<zero>\<^sub>G"] assms(1)
    trans[OF A1 A2] by auto
  then show ?thesis by auto
qed

text \<open>Taking inverses in a module is just multiplying by $-1$\<close>

lemma(in module0) inv_module:
  assumes "g\<in>G"
  shows "(\<rm>\<^sub>R\<one>\<^sub>R) \<cdot>\<^sub>M g=\<rm>\<^sub>G g"
proof-
  have A:"\<one>\<^sub>R\<in>R" using ring.Ring_ZF_1_L2(2) by auto
  then have B:"(\<rm>\<^sub>R\<one>\<^sub>R) \<in> R" using ring.Ring_ZF_1_L3(1) by auto
  have "g\<ra>\<^sub>G ((\<rm>\<^sub>R\<one>\<^sub>R) \<cdot>\<^sub>M g)=(\<one>\<^sub>R \<cdot>\<^sub>M g)\<ra>\<^sub>G ((\<rm>\<^sub>R\<one>\<^sub>R) \<cdot>\<^sub>M g)" using S_one id_conv assms by auto
  also have "\<dots>=(\<one>\<^sub>R \<rs>\<^sub>R\<one>\<^sub>R) \<cdot>\<^sub>M g" using S_dist1 unfolding ringsub_def using A B assms by auto
  also have "\<dots>=\<zero>\<^sub>R \<cdot>\<^sub>M g" using ring.Ring_ZF_1_L3(7)[OF A] by auto
  also have "\<dots>=\<zero>\<^sub>G" using mult_zeroR assms by auto
  ultimately have "g\<ra>\<^sub>G ((\<rm>\<^sub>R\<one>\<^sub>R) \<cdot>\<^sub>M g)=\<zero>\<^sub>G" by auto moreover
  from B have "S`(\<rm>\<^sub>R\<one>\<^sub>R)\<in>End(G,f)" using S_fun apply_type by auto
  then have "(\<rm>\<^sub>R\<one>\<^sub>R) \<cdot>\<^sub>M g\<in>G" unfolding End_def using apply_type assms by auto
  ultimately show ?thesis using ab_group.group0_2_L9(2)[OF assms] by auto
qed

text\<open>The ring negative elements give out
the inverse group elements.\<close>

corollary(in module0) inv_module2:
  assumes "g\<in>G" "r\<in>R"
  shows "(\<rm>\<^sub>Rr) \<cdot>\<^sub>M g=\<rm>\<^sub>G (r\<cdot>\<^sub>M g)"
proof-
  have A:"\<one>\<^sub>R\<in>R" using ring.Ring_ZF_1_L2(2) by auto
  then have B:"(\<rm>\<^sub>R\<one>\<^sub>R) \<in> R" using ring.Ring_ZF_1_L3(1) by auto
  from assms(2) have "S`r:G\<rightarrow>G" using apply_type[OF S_fun] unfolding End_def by auto
  with assms(1) have "(r\<cdot>\<^sub>M g)\<in>G" using apply_type by auto
  then have "(\<rm>\<^sub>G (r\<cdot>\<^sub>M g))=(\<rm>\<^sub>R\<one>\<^sub>R)\<cdot>\<^sub>M(r \<cdot>\<^sub>M g)" using inv_module by auto
  also have "\<dots>=((\<rm>\<^sub>R\<one>\<^sub>R)\<cdot>\<^sub>Rr) \<cdot>\<^sub>M g" using S_dist2 B assms by auto
  also have "\<dots>=(\<rm>\<^sub>R(\<one>\<^sub>R\<cdot>\<^sub>Rr)) \<cdot>\<^sub>M g" using A assms(2) ring.Ring_ZF_1_L7(1) by auto
  also have "\<dots>=(\<rm>\<^sub>Rr) \<cdot>\<^sub>M g" using ring.Ring_ZF_1_L3(6) assms(2) by auto
  ultimately show ?thesis by auto
qed

subsection \<open>$R$-linear functions\<close>

text  \<open>A group homomorphism between $R$-modules is called $R$-linear
if the actions of $R$ can be commuted with the homomorphism. \<close>

definition
  RLinear 
  where "IsAmodule(R,A,M,G,P,S1) \<Longrightarrow> IsAmodule(R,A,M,H,F,S2) \<Longrightarrow> 
    RLinear(f,R,A,M,G,P,S1,H,F,S2) \<equiv> Homomor(f,G,P,H,F) \<and> (\<forall>g\<in>G. \<forall>r\<in>R. f`((S1`r)`g)=(S2`r)`(f`g))"

text \<open>We can consider the set of endomorphisms, which commute with the action.\<close>

definition
  REnd 
  where "IsAmodule(R,A,M,G,P,S) \<Longrightarrow> REnd(R,A,M,G,P,S)\<equiv>{f\<in>End(G,P). (\<forall>g\<in>G. \<forall>r\<in>R. f`((S`r)`g)=(S`r)`(f`g))}"

text\<open>Linear endomorphisms are closed under composition.\<close>

theorem(in module0) Rend_comp:
  assumes "h\<in>REnd(R,A,M,G,f,S)""g\<in>REnd(R,A,M,G,f,S)"
  shows "Composition(G)`\<langle>h,g\<rangle>\<in>REnd(R,A,M,G,f,S)"
proof-
  from assms have endo:"h\<in>End(G,f)""g\<in>End(G,f)" using REnd_def isAmodule by auto
  then have A:"Composition(G)`\<langle>h,g\<rangle>\<in>End(G,f)" using ab_group.end_composition by auto
  from endo have fun:"h\<in>G\<rightarrow>G""g\<in>G\<rightarrow>G" unfolding End_def by auto
  {
    fix m r assume "m\<in>G""r\<in>R"
    then have "S`r\<in>End(G,f)" using S_fun apply_type by auto
    then have "S`r:G\<rightarrow>G" unfolding End_def by auto
    with `m\<in>G` have p:"(S`r)`m\<in>G" using apply_type by auto
    have r:"Composition(G)`\<langle>h,g\<rangle>=h O g" using func_ZF_5_L2 fun by auto
    then have "(Composition(G)`\<langle>h,g\<rangle>)`(r\<cdot>\<^sub>M m)=(h O g)`(r\<cdot>\<^sub>M m)" by auto
    also have "\<dots>=h`( g`(r\<cdot>\<^sub>M m))" using comp_fun_apply fun(2) p
      by auto
    also have "\<dots>=h`( r\<cdot>\<^sub>M (g` m))" using assms(2) using REnd_def isAmodule `m\<in>G` `r\<in>R` by auto
    also have "\<dots>= r\<cdot>\<^sub>M (h`(g` m))" using assms(1) using REnd_def isAmodule fun(2) `m\<in>G` `r\<in>R` by auto
    also have "\<dots>= r\<cdot>\<^sub>M ((h O g)` m)" using comp_fun_apply fun(2) `m\<in>G` by auto
    ultimately have "(Composition(G)`\<langle>h,g\<rangle>)`(r\<cdot>\<^sub>M m)=r\<cdot>\<^sub>M ((Composition(G)`\<langle>h,g\<rangle>)` m)" using r by auto
  }
  with A show ?thesis using REnd_def isAmodule by auto
qed

text\<open>Linear homomorphisms form a monoid under composition.\<close>

theorem(in module0) REnd_monoid_comp:
  shows "IsAmonoid(REnd(R,A,M,G,f,S),restrict(Composition(G),REnd(R,A,M,G,f,S)\<times>REnd(R,A,M,G,f,S)))"
  and "TheNeutralElement(REnd(R,A,M,G,f,S),restrict(Composition(G),REnd(R,A,M,G,f,S)\<times>REnd(R,A,M,G,f,S)))=id(G)"
proof-
  have A1:"REnd(R,A,M,G,f,S)\<subseteq>G\<rightarrow>G" using REnd_def isAmodule unfolding End_def by auto
  {
    fix g r assume "g\<in>G""r\<in>R"
    then have "S`r\<in>End(G,f)" using S_fun apply_type by auto
    then have "S`r:G\<rightarrow>G" unfolding End_def by auto
    with `g\<in>G` have p:"(S`r)`g\<in>G" using apply_type by auto
    then have "id(G)`(r\<cdot>\<^sub>M g)=r\<cdot>\<^sub>M (id(G)` g)" using `g\<in>G` by auto
  }
  moreover
  have "TheNeutralElement(End(G, f), restrict(Composition(G), End(G, f) \<times> End(G, f)))\<in>End(G,f)"
    using monoid0.unit_is_neutral[of "End(G,f)" "Composition(G) {in End} [G,f]"] ab_group.end_comp_monoid(1) unfolding monoid0_def by blast
  with subst[OF ab_group.end_comp_monoid(2), of "\<lambda>t. t\<in>End(G,f)"] have "id(G)\<in>End(G,f)" by blast ultimately
  have "id(G)\<in>REnd(R,A,M,G,f,S)" using isAmodule REnd_def by auto
  then have A2:"TheNeutralElement(G\<rightarrow>G, Composition(G))\<in>REnd(R,A,M,G,f,S)" using Group_ZF_2_5_L2(2) by auto
  have A3:"REnd(R,A,M,G,f,S){is closed under}Composition(G)" using Rend_comp unfolding IsOpClosed_def by auto
  with A1 A2 show "IsAmonoid(REnd(R,A,M,G,f,S),restrict(Composition(G),REnd(R,A,M,G,f,S)\<times>REnd(R,A,M,G,f,S)))" using monoid0.group0_1_T1 unfolding monoid0_def using Group_ZF_2_5_L2(1)
    by force
  have "IsAmonoid(G\<rightarrow>G,Composition(G))" using Group_ZF_2_5_L2(1) by auto
  with A1 A2 A3 show "TheNeutralElement(REnd(R,A,M,G,f,S),restrict(Composition(G),REnd(R,A,M,G,f,S)\<times>REnd(R,A,M,G,f,S)))=id(G)"
    using group0_1_L6 Group_ZF_2_5_L2(2) by auto
qed

section\<open>Linear combinations and independence\<close>
  
text\<open>An important tool is linear combinations; finite sums of elements of the module
multiplied by elements of the ring.\<close>

definition(in module0)
  LinearComb ("\<Sum>[_;{_,_}]" 88)
  where "fR:C\<rightarrow>R \<Longrightarrow> fG:C\<rightarrow>G \<Longrightarrow> D\<in>FinPow(C) \<Longrightarrow> LinearComb(D,fR,fG) \<equiv> if D\<noteq>0 then CommSetFold(f,{\<langle>m,(fR`m)\<cdot>\<^sub>M (fG`m)\<rangle>. m\<in>domain(fR)},D)
    else \<zero>\<^sub>G"

text\<open>A linear combination is an element in the module.\<close>

lemma(in module0) fun_aux:
  assumes "AA:C\<rightarrow>R" "B:C\<rightarrow>G"
  shows "{\<langle>m,(AA`m)\<cdot>\<^sub>M (B`m)\<rangle>. m\<in>C}:C\<rightarrow>G"
proof-
  {
    fix m assume "m\<in>C"
    then have p:"AA`m\<in>R""B`m\<in>G" using assms(1,2) apply_type by auto
    then have "S`(AA`m)\<in>End(G,f)" using S_fun apply_type by auto
    then have "S`(AA`m):G\<rightarrow>G" unfolding End_def by auto
    then have "(AA`m)\<cdot>\<^sub>M(B`m)\<in>G" using p(2) apply_type by auto
  }
  then have "{\<langle>m,(AA`m)\<cdot>\<^sub>M (B`m)\<rangle>. m\<in>C}\<subseteq>C\<times>G" by auto moreover
  {
    fix x y assume "\<langle>x,y\<rangle>\<in>{\<langle>m,(AA`m)\<cdot>\<^sub>M (B`m)\<rangle>. m\<in>C}"
    then have xx:"x\<in>C""y=(AA`x)\<cdot>\<^sub>M (B`x)" by auto
    {
      fix y' assume "\<langle>x,y'\<rangle>\<in>{\<langle>m,(AA`m)\<cdot>\<^sub>M (B`m)\<rangle>. m\<in>C}"
      then have "y'=(AA`x)\<cdot>\<^sub>M (B`x)" by auto
      with xx(2) have "y=y'" by auto
    }
    then have "\<forall>y'. \<langle>x,y'\<rangle>\<in>{\<langle>m,(AA`m)\<cdot>\<^sub>M (B`m)\<rangle>. m\<in>C} \<longrightarrow> y=y'" by auto
  }
  then have "\<forall>x y. \<langle>x,y\<rangle>\<in>{\<langle>m,(AA`m)\<cdot>\<^sub>M (B`m)\<rangle>. m\<in>C} \<longrightarrow> (\<forall>y'. \<langle>x,y'\<rangle>\<in>{\<langle>m,(AA`m)\<cdot>\<^sub>M (B`m)\<rangle>. m\<in>C} \<longrightarrow> y=y')"
    by auto 
  moreover have "domain({\<langle>m,(AA`m)\<cdot>\<^sub>M (B`m)\<rangle>. m\<in>C})\<subseteq>C" unfolding domain_def by auto ultimately
  show "{\<langle>m,(AA`m)\<cdot>\<^sub>M (B`m)\<rangle>. m\<in>C}:C\<rightarrow>G" unfolding Pi_def function_def by auto
qed

text\<open>A linear combination results in a group element where
the functions and the sets are well defined.\<close>

theorem(in module0) linComb_is_in_module:
  assumes "AA:C\<rightarrow>R" "B:C\<rightarrow>G" "D\<in>FinPow(C)"
  shows "(\<Sum>[D;{AA,B}])\<in>G"
proof-
  {
    assume noE:"D\<noteq>0"
    have ffun:"{\<langle>m,(AA`m)\<cdot>\<^sub>M (B`m)\<rangle>. m\<in>C}:C\<rightarrow>G" using fun_aux assms by auto
    note commsemigr.sum_over_set_add_point(1)[OF
      commsemigr.intro[OF _ _ ffun] assms(3) noE]
      ab_group.abelian_group_axioms abelian_group_def
      group0_def IsAgroup_def IsAmonoid_def abelian_group_axioms_def moreover
    from assms(1) have "domain(AA)=C" unfolding Pi_def by auto
    ultimately have ?thesis unfolding LinearComb_def[OF assms(1-3)] using noE by auto
  }
  then show ?thesis unfolding LinearComb_def[OF assms(1-3)] 
    using ab_group.group0_2_L2 by auto
qed

text\<open>A linear combination of one element functions is just a multiplication of
an element in the ring and one in the module.\<close>

lemma(in module0) linComb_one_element:
  assumes "x\<in>X" "AA:X\<rightarrow>R" "B:X\<rightarrow>G"
  shows "\<Sum>[{x};{AA,B}]=(AA`x)\<cdot>\<^sub>M(B`x)"
proof-
  have dom:"domain(AA)=X" using assms(2) func1_1_L1 by auto
  have fin:"{x}\<in>FinPow(X)" unfolding FinPow_def using assms(1) by auto
  have A:"\<Sum>[{x};{AA,B}]=CommSetFold(f,{\<langle>t,(AA`t)\<cdot>\<^sub>M (B`t)\<rangle>. t\<in>X},{x})"
    unfolding LinearComb_def[OF assms(2,3) fin] dom by auto
  have assoc:"f{is associative on}G" using ab_group.abelian_group_axioms
    unfolding abelian_group_def group0_def IsAgroup_def IsAmonoid_def by auto
  have comm:"commsemigr(G, f, X, {\<langle>t,(AA`t)\<cdot>\<^sub>M (B`t)\<rangle>. t\<in>X})"
    unfolding commsemigr_def
    using ab_group.abelian_group_axioms 
    unfolding abelian_group_def abelian_group_axioms_def
    group0_def IsAgroup_def IsAmonoid_def using fun_aux[OF assms(2,3)] by auto
  have sing:"1\<approx>{x}" "|{x}|=1" using singleton_eqpoll_1 eqpoll_sym by auto
  then obtain b where b:"b\<in>bij(|{x}|,{x})" "b\<in>bij(1,{x})" unfolding eqpoll_def by auto then
  have "\<Sum>[{x};{AA,B}]=Fold1(f,{\<langle>t,(AA`t)\<cdot>\<^sub>M (B`t)\<rangle>. t\<in>X} O b)" 
    using commsemigr.sum_over_set_bij[OF comm fin, of b] trans[OF A] by blast
  also have "\<dots>=({\<langle>t,(AA`t)\<cdot>\<^sub>M (B`t)\<rangle>. t\<in>X} O b)`0" using semigr0.prod_of_1elem[of G f] unfolding semigr0_def using
    comp_fun[OF _ fun_aux[OF assms(2,3)], of b 1] b(2) assms(1) func1_1_L1B[of b 1 "{x}" X] assoc unfolding bij_def inj_def by blast
  also have "\<dots>=({\<langle>t,(AA`t)\<cdot>\<^sub>M (B`t)\<rangle>. t\<in>X})`(b`0)" using comp_fun_apply b unfolding bij_def inj_def by auto
  also have "\<dots>= {\<langle>t,(AA`t)\<cdot>\<^sub>M (B`t)\<rangle>. t\<in>X}`x" using apply_type[of b 1 "\<lambda>t. {x}" 0] b unfolding bij_def inj_def
    by auto
  ultimately show ?thesis using apply_equality[OF _ fun_aux[OF assms(2,3)]] assms(1) by auto
qed


text \<open>It is useful to know how the action of $R$ applies to a linear combination.\<close>

lemma(in module0) linComb_action:
  assumes "AA:X\<rightarrow>R" "B:X\<rightarrow>G" "r\<in>R" "D\<in>FinPow(X)"
  shows "r\<cdot>\<^sub>M(\<Sum>[D;{AA,B}])=\<Sum>[D;{{\<langle>k,r\<cdot>\<^sub>R(AA`k)\<rangle>. k\<in>X},B}]" and "{\<langle>m,r \<cdot>\<^sub>R(AA`m)\<rangle>. m\<in>X}:X\<rightarrow>R"
proof-
  show f:"{\<langle>m,r \<cdot>\<^sub>R(AA`m)\<rangle>. m\<in>X}:X\<rightarrow>R" unfolding Pi_def function_def domain_def
    using apply_type[OF assms(1)] assms(3) ring.Ring_ZF_1_L4(3) by auto
  {
    fix AAt Bt assume as:"AAt:X \<rightarrow> R" "Bt:X \<rightarrow> G"
    have "\<Sum>[0;{AAt,Bt}]=\<zero>\<^sub>G" using LinearComb_def[OF as] unfolding FinPow_def by auto
    then have "r \<cdot>\<^sub>M (\<Sum>[0;{AAt,Bt}])=\<zero>\<^sub>G" using assms(3) mult_zeroG by auto moreover
    have mr:"{\<langle>m,r\<cdot>\<^sub>R(AAt`m)\<rangle>. m\<in>X}:X\<rightarrow>R" unfolding Pi_def function_def domain_def
      using apply_type[OF as(1)] assms(3) ring.Ring_ZF_1_L4(3) by auto
    then have "\<Sum>[0;{{\<langle>x, r \<cdot>\<^sub>R (AAt ` x)\<rangle> . x \<in> X},Bt}]=\<zero>\<^sub>G" using LinearComb_def[OF mr as(2)]
      unfolding FinPow_def by auto
    ultimately have "r \<cdot>\<^sub>M (\<Sum>[0;{AAt,Bt}]) = \<Sum>[0;{{\<langle>x, r \<cdot>\<^sub>R (AAt ` x)\<rangle> . x \<in> X},Bt}]" by auto
  }
  then have case0:"(\<forall>AAt\<in>X \<rightarrow> R.
    \<forall>Bt\<in>X \<rightarrow> G. r \<cdot>\<^sub>M (\<Sum>[0;{AAt,Bt}]) = \<Sum>[0;{{\<langle>x, r \<cdot>\<^sub>R (AAt ` x)\<rangle> . x \<in> X},Bt}])" by auto
  {
    fix Tk assume A:"Tk\<in>FinPow(X)" "Tk\<noteq>0"
    then obtain t where tt:"t\<in>Tk" by auto
    {
      assume "(\<forall>AAk\<in>X\<rightarrow>R. \<forall>Bk\<in>X\<rightarrow>G. (r\<cdot>\<^sub>M(\<Sum>[Tk-{t};{AAk,Bk}])=\<Sum>[Tk-{t};{{\<langle>k,r\<cdot>\<^sub>R(AAk`k)\<rangle>. k\<in>X},Bk}]))"
      with tt obtain t where t:"t\<in>Tk" "(\<forall>AAk\<in>X\<rightarrow>R. \<forall>Bk\<in>X\<rightarrow>G. (r\<cdot>\<^sub>M(\<Sum>[Tk-{t};{AAk,Bk}])=\<Sum>[Tk-{t};{{\<langle>k,r\<cdot>\<^sub>R(AAk`k)\<rangle>. k\<in>X},Bk}]))" by auto
      let ?Tk="Tk-{t}"
      have CC:"Tk=?Tk\<union>{t}" using t by auto
      have DD:"?Tk\<in>FinPow(X)" using A(1) unfolding FinPow_def using subset_Finite[of ?Tk Tk]
        by auto
      have tX:"t\<in>X" using t(1) A(1) unfolding FinPow_def by auto
      then have EE:"X-(?Tk)=(X-Tk)\<union>{t}" using t(1) by auto
      {
        assume as:"Tk-{t}\<noteq>0"
        with t have BB:"t\<in>Tk" "Tk-{t}\<noteq>0" "\<forall>AAk\<in>X\<rightarrow>R. \<forall>Bk\<in>X\<rightarrow>G. (r\<cdot>\<^sub>M(\<Sum>[Tk-{t};{AAk,Bk}])=\<Sum>[Tk-{t};{{\<langle>k,r\<cdot>\<^sub>R(AAk`k)\<rangle>. k\<in>X},Bk}])" by auto
        from BB(3) have A3:"\<forall>AAk\<in>X\<rightarrow>R. \<forall>Bk\<in>X\<rightarrow>G. (r\<cdot>\<^sub>M(\<Sum>[?Tk;{AAk,Bk}])=\<Sum>[?Tk;{{\<langle>k,r\<cdot>\<^sub>R(AAk`k)\<rangle>. k\<in>X},Bk}])" by auto
        {
          fix AAt Bt assume B:"AAt:X\<rightarrow>R" "Bt:X\<rightarrow>G"
          then have af:"{\<langle>k,(AAt`k)\<cdot>\<^sub>M(Bt`k)\<rangle>. k\<in>X}:X\<rightarrow>G" using fun_aux by auto
          have comm:"commsemigr(G, f, X, {\<langle>k,(AAt`k)\<cdot>\<^sub>M(Bt`k)\<rangle>. k\<in>X})"
            unfolding commsemigr_def
            using ab_group.abelian_group_axioms 
            unfolding abelian_group_def abelian_group_axioms_def
            group0_def IsAgroup_def IsAmonoid_def using af by auto
          then have "CommSetFold(f,{\<langle>k,(AAt`k)\<cdot>\<^sub>M(Bt`k)\<rangle>. k\<in>X},Tk)=CommSetFold(f,{\<langle>k,(AAt`k)\<cdot>\<^sub>M(Bt`k)\<rangle>. k\<in>X},?Tk)
            \<ra>\<^sub>G({\<langle>k,(AAt`k)\<cdot>\<^sub>M(Bt`k)\<rangle>. k\<in>X}`t)" using commsemigr.sum_over_set_add_point(2)[of G f X "{\<langle>k,(AAt`k)\<cdot>\<^sub>M(Bt`k)\<rangle>. k\<in>X}" "Tk-{t}"] DD BB(2) 
            A(1-2) EE CC by auto
          also have "\<dots>=CommSetFold(f,{\<langle>k,(AAt`k)\<cdot>\<^sub>M(Bt`k)\<rangle>. k\<in>X},?Tk)
            \<ra>\<^sub>G((AAt`t)\<cdot>\<^sub>M(Bt`t))" using apply_equality[OF _ af, of t "(AAt`t)\<cdot>\<^sub>M(Bt`t)"] tX by auto
          ultimately have "CommSetFold(f,{\<langle>k,(AAt`k)\<cdot>\<^sub>M(Bt`k)\<rangle>. k\<in>X},Tk)=CommSetFold(f,{\<langle>k,(AAt`k)\<cdot>\<^sub>M(Bt`k)\<rangle>. k\<in>X},?Tk)
            \<ra>\<^sub>G((AAt`t)\<cdot>\<^sub>M(Bt`t))" by auto moreover
          have "domain(AAt)=X" using B(1) Pi_def by auto ultimately
          have "(\<Sum>[Tk;{AAt,Bt}])=(\<Sum>[?Tk;{AAt,Bt}])\<ra>\<^sub>G((AAt`t)\<cdot>\<^sub>M(Bt`t))" unfolding LinearComb_def[OF B(1,2) A(1)]
            LinearComb_def[OF B(1,2) DD] using as A(2) by auto
          then have eq:"r\<cdot>\<^sub>M(\<Sum>[Tk;{AAt,Bt}])=r\<cdot>\<^sub>M((\<Sum>[?Tk;{AAt,Bt}])\<ra>\<^sub>G((AAt`t)\<cdot>\<^sub>M(Bt`t)))" by auto
          moreover have "S`r\<in>End(G,f)" using S_fun assms(3) apply_type by auto
          then have "\<forall>g\<in>G. \<forall>h\<in>G. (S`r)`(g\<ra>\<^sub>Gh)=((S`r)`g)\<ra>\<^sub>G((S`r)`h)" unfolding End_def
            unfolding Homomor_def[OF Ggroup Ggroup] by auto
          moreover have AR:"AAt`t\<in>R" using B(1) tX apply_type by auto
          then have "S`(AAt`t):G\<rightarrow>G" using apply_type[OF S_fun] unfolding End_def by auto
          from apply_type[OF this] have "(AAt`t)\<cdot>\<^sub>M(Bt`t)\<in>G" using apply_type[OF B(2)] tX by auto moreover
          have mr:"{\<langle>m,r\<cdot>\<^sub>R(AAt`m)\<rangle>. m\<in>X}:X\<rightarrow>R" unfolding Pi_def function_def domain_def
            using apply_type[OF B(1)] assms(3) ring.Ring_ZF_1_L4(3) by auto
          then have fff:"{\<langle>m,({\<langle>m,r\<cdot>\<^sub>R(AAt`m)\<rangle>. m\<in>X}`m)\<cdot>\<^sub>M(Bt`m)\<rangle>. m\<in>X}:X\<rightarrow>G" using fun_aux[OF mr B(2)] apply_equality[OF _ mr] by auto
          with tX have pff:"\<langle>t,({\<langle>m,r\<cdot>\<^sub>R(AAt`m)\<rangle>. m\<in>X}`t)\<cdot>\<^sub>M(Bt`t)\<rangle>\<in>{\<langle>m,({\<langle>m,r\<cdot>\<^sub>R(AAt`m)\<rangle>. m\<in>X}`m)\<cdot>\<^sub>M(Bt`m)\<rangle>. m\<in>X}"
            by auto
          have dom:"domain({\<langle>m,(r\<cdot>\<^sub>R(AAt`m))\<rangle>. m\<in>X})=X" by auto
          have comm2:"commsemigr(G, f, X, {\<langle>m, ({\<langle>x,r \<cdot>\<^sub>R(AAt`x)\<rangle>. x\<in>X}`m)\<cdot>\<^sub>M(Bt`m)\<rangle>. m\<in>X})"
            unfolding commsemigr_def
            using ab_group.abelian_group_axioms 
            unfolding abelian_group_def abelian_group_axioms_def
            group0_def IsAgroup_def IsAmonoid_def using fff by auto
          have "\<Sum>[?Tk;{AAt,Bt}]\<in>G" using linComb_is_in_module[OF B(1,2) DD].
          ultimately have "r \<cdot>\<^sub>M ((\<Sum>[?Tk;{AAt,Bt}]) \<ra>\<^sub>G (AAt ` t \<cdot>\<^sub>M (Bt ` t)))=(r\<cdot>\<^sub>M(\<Sum>[?Tk;{AAt,Bt}]))\<ra>\<^sub>G(r\<cdot>\<^sub>M((AAt`t)\<cdot>\<^sub>M(Bt`t)))"
            by auto
          also have "\<dots>=(r\<cdot>\<^sub>M(\<Sum>[?Tk;{AAt,Bt}]))\<ra>\<^sub>G((r\<cdot>\<^sub>R(AAt`t))\<cdot>\<^sub>M(Bt`t))" using S_dist2
            assms(3) AR apply_type[OF B(2)] tX by auto
          also have "\<dots>=(\<Sum>[?Tk;{{\<langle>x,r\<cdot>\<^sub>R(AAt`x)\<rangle>. x\<in>X},Bt}])\<ra>\<^sub>G((r\<cdot>\<^sub>R(AAt`t))\<cdot>\<^sub>M(Bt`t))"
            using A3 B(1,2) by auto
          also have "\<dots>=(\<Sum>[?Tk;{{\<langle>x,r\<cdot>\<^sub>R(AAt`x)\<rangle>. x\<in>X},Bt}])\<ra>\<^sub>G(({\<langle>m, r \<cdot>\<^sub>R (AAt ` m)\<rangle> . m \<in> X} `t)\<cdot>\<^sub>M(Bt`t))"
            using apply_equality[OF _ mr] tX by auto
          also have "\<dots>=(\<Sum>[?Tk;{{\<langle>x,r\<cdot>\<^sub>R(AAt`x)\<rangle>. x\<in>X},Bt}])\<ra>\<^sub>G({\<langle>m, ({\<langle>x,(r \<cdot>\<^sub>R(AAt`x))\<rangle>. x\<in>X}`m)\<cdot>\<^sub>M(Bt`m)\<rangle>. m\<in>X}`t)"
            using apply_equality[OF pff fff] by auto
          also have "\<dots>=CommSetFold(f,{\<langle>m, ({\<langle>x,r \<cdot>\<^sub>R(AAt`x)\<rangle>. x\<in>X}`m)\<cdot>\<^sub>M(Bt`m)\<rangle>. m\<in>X},?Tk)\<ra>\<^sub>G({\<langle>m, ({\<langle>x,(r \<cdot>\<^sub>R(AAt`x))\<rangle>. x\<in>X}`m)\<cdot>\<^sub>M(Bt`m)\<rangle>. m\<in>X}`t)"
            unfolding LinearComb_def[OF mr B(2) DD] using dom as by auto
          also have "\<dots>=CommSetFold(f,{\<langle>m, ({\<langle>x,r \<cdot>\<^sub>R(AAt`x)\<rangle>. x\<in>X}`m)\<cdot>\<^sub>M(Bt`m)\<rangle>. m\<in>X},Tk)" using 
            commsemigr.sum_over_set_add_point(2)[OF comm2, of "Tk-{t}"] fff DD tX CC BB(2) by auto
          ultimately have "r \<cdot>\<^sub>M ((\<Sum>[?Tk;{AAt,Bt}]) \<ra>\<^sub>G (AAt ` t \<cdot>\<^sub>M (Bt ` t))) =CommSetFold(f,{\<langle>m, ({\<langle>x,r \<cdot>\<^sub>R(AAt`x)\<rangle>. x\<in>X}`m)\<cdot>\<^sub>M(Bt`m)\<rangle>. m\<in>X},Tk)"
            by auto
          with eq have "r \<cdot>\<^sub>M (\<Sum>[Tk;{AAt,Bt}]) =CommSetFold(f,{\<langle>m, ({\<langle>x,r \<cdot>\<^sub>R(AAt`x)\<rangle>. x\<in>X}`m)\<cdot>\<^sub>M(Bt`m)\<rangle>. m\<in>X},Tk)" by auto
          also have "\<dots>=\<Sum>[Tk;{{\<langle>x,r\<cdot>\<^sub>R(AAt`x)\<rangle>. x\<in>X},Bt}]" using A(2) unfolding LinearComb_def[OF mr B(2) A(1)] dom by auto
          ultimately have "r \<cdot>\<^sub>M (\<Sum>[Tk;{AAt,Bt}]) =\<Sum>[Tk;{{\<langle>x,r\<cdot>\<^sub>R(AAt`x)\<rangle>. x\<in>X},Bt}]" by auto
        }
        then have "\<forall>AA\<in>X\<rightarrow>R. \<forall>B\<in>X\<rightarrow>G. r \<cdot>\<^sub>M (\<Sum>[Tk;{AA,B}]) =\<Sum>[Tk;{{\<langle>x,r\<cdot>\<^sub>R(AA`x)\<rangle>. x\<in>X},B}]" using BB by auto
      }
      moreover
      {
        assume "Tk-{t}=0"
        then have sing:"Tk={t}" using A(2) by auto
        {
          fix AAt Bt assume B:"AAt:X\<rightarrow>R" "Bt:X\<rightarrow>G"
          have mr:"{\<langle>m,r\<cdot>\<^sub>R(AAt`m)\<rangle>. m\<in>X}:X\<rightarrow>R" unfolding Pi_def function_def domain_def
            using apply_type[OF B(1)] assms(3) ring.Ring_ZF_1_L4(3) by auto
          from sing have "\<Sum>[Tk;{AAt,Bt}]=(AAt`t)\<cdot>\<^sub>M(Bt`t)" using linComb_one_element[OF tX B]
            by auto
          then have "r \<cdot>\<^sub>M (\<Sum>[Tk;{AAt,Bt}])=r \<cdot>\<^sub>M ((AAt`t)\<cdot>\<^sub>M(Bt`t))" by auto
          also have "\<dots>=(r \<cdot>\<^sub>R (AAt`t))\<cdot>\<^sub>M(Bt`t)" using S_dist2 assms(3) apply_type[OF B(1) tX]
            apply_type[OF B(2) tX] by auto
          also have "\<dots>=({\<langle>m,(r \<cdot>\<^sub>R (AAt`m))\<rangle>. m\<in>X}`t)\<cdot>\<^sub>M(Bt`t)" using apply_equality[OF _ mr] tX by auto
          also have "\<dots>=\<Sum>[Tk;{{\<langle>m,(r \<cdot>\<^sub>R (AAt`m))\<rangle>. m\<in>X},Bt}]" using sing linComb_one_element[OF tX mr B(2)]
            by auto
          ultimately have "r \<cdot>\<^sub>M (\<Sum>[Tk;{AAt,Bt}])=\<Sum>[Tk;{{\<langle>m,(r \<cdot>\<^sub>R (AAt`m))\<rangle>. m\<in>X},Bt}]" by auto
        }
      }
      ultimately have " \<forall>AA\<in>X \<rightarrow> R. \<forall>B\<in>X \<rightarrow> G. r \<cdot>\<^sub>M (\<Sum>[Tk;{AA,B}]) = \<Sum>[Tk;{{\<langle>x, r \<cdot>\<^sub>R (AA ` x)\<rangle> . x \<in> X},B}]"
        by auto
    }
    with tt have "\<exists>t\<in>Tk. (\<forall>AAt\<in>X \<rightarrow> R.  \<forall>Bt\<in>X \<rightarrow> G.
                      r \<cdot>\<^sub>M (\<Sum>[Tk - {t};{AAt,Bt}]) =
                      \<Sum>[Tk - {t};{{\<langle>x, r \<cdot>\<^sub>R (AAt ` x)\<rangle> . x \<in> X},Bt}]) \<longrightarrow>
               (\<forall>AAt\<in>X \<rightarrow> R. \<forall>Bt\<in>X \<rightarrow> G.
                      r \<cdot>\<^sub>M (\<Sum>[Tk;{AAt,Bt}]) = \<Sum>[Tk;{{\<langle>x, r \<cdot>\<^sub>R (AAt ` x)\<rangle> . x \<in> X},Bt}])" by auto
  }
  then have caseStep:"\<forall>A\<in>FinPow(X). A\<noteq>0 \<longrightarrow> (\<exists>t\<in>A. (\<forall>AAt\<in>X \<rightarrow> R.
                   \<forall>Bt\<in>X \<rightarrow> G.
                      r \<cdot>\<^sub>M (\<Sum>[A - {t};{AAt,Bt}]) =
                      \<Sum>[A - {t};{{\<langle>x, r \<cdot>\<^sub>R (AAt ` x)\<rangle> . x \<in> X},Bt}]) \<longrightarrow>
               (\<forall>AAt\<in>X \<rightarrow> R.
                   \<forall>Bt\<in>X \<rightarrow> G.
                      r \<cdot>\<^sub>M (\<Sum>[A;{AAt,Bt}]) = \<Sum>[A;{{\<langle>x, r \<cdot>\<^sub>R (AAt ` x)\<rangle> . x \<in> X},Bt}]))" by auto
  have "\<forall>AAt\<in>X\<rightarrow>R. \<forall>Bt\<in>X\<rightarrow>G. r \<cdot>\<^sub>M(\<Sum>[D;{AAt,Bt}]) =\<Sum>[D;{{\<langle>x,r\<cdot>\<^sub>R(AAt`x)\<rangle>. x\<in>X},Bt}]" using
    FinPow_ind_rem_one[where P="\<lambda>D. (\<forall>AAt\<in>X\<rightarrow>R. \<forall>Bt\<in>X\<rightarrow>G. r \<cdot>\<^sub>M(\<Sum>[D;{AAt,Bt}]) =\<Sum>[D;{{\<langle>x,r\<cdot>\<^sub>R(AAt`x)\<rangle>. x\<in>X},Bt}])",
    OF case0 caseStep] assms(4) by auto
  with assms(1,2) show "r \<cdot>\<^sub>M(\<Sum>[D;{AA,B}]) =\<Sum>[D;{{\<langle>x,r\<cdot>\<^sub>R(AA`x)\<rangle>. x\<in>X},B}]" by auto
qed

text\<open>A linear combination can always be defined on a cardinal.\<close>

lemma(in module0) linComb_reorder_terms1:
  assumes "AA:X\<rightarrow>R" "B:X\<rightarrow>G" "D\<in>FinPow(X)" "g\<in>bij(|D|,D)"
  shows "(\<Sum>[D;{AA,B}])=\<Sum>[|D|;{AA O g,B O g}]"
proof-
  from assms(3,4) have funf:"g:|D|\<rightarrow>X" unfolding bij_def inj_def FinPow_def using func1_1_L1B by auto
  have ABfun:"AA O g:|D|\<rightarrow>R" "B O g:|D|\<rightarrow>G" using comp_fun[OF funf assms(1)] comp_fun[OF funf assms(2)] by auto
  then have domAg:"domain(AA O g)=|D|" unfolding Pi_def by auto
  from assms(1) have domA:"domain(AA)=X" unfolding Pi_def by auto
  have comm:"commsemigr(G, f, domain(AA), {\<langle>m,(AA`m)\<cdot>\<^sub>M (B`m)\<rangle>. m\<in>domain(AA)})"
    unfolding commsemigr_def using ab_group.abelian_group_axioms unfolding IsAgroup_def
    IsAmonoid_def abelian_group_def group0_def abelian_group_axioms_def
    using fun_aux[OF assms(1,2)] domA by auto
  {
    assume A:"D=0"
    then have D:"\<Sum>[D;{AA,B}]=\<zero>\<^sub>G" using LinearComb_def assms(1-3) by auto moreover
    from A assms(4) have "|D|=0" unfolding bij_def inj_def Pi_def by auto
    moreover then have "|D|\<in>FinPow(|D|)" unfolding FinPow_def by auto moreover
    note ABfun
    ultimately have ?thesis using LinearComb_def[of "AA O g" "|D|" "B O g", of "|D|"] by auto
  }
  moreover
  {
    assume A:"D\<noteq>0"
    then have eqD:"\<Sum>[D;{AA,B}]=CommSetFold(f,{\<langle>m,(AA`m)\<cdot>\<^sub>M (B`m)\<rangle>. m\<in>domain(AA)},D)" using LinearComb_def[OF assms(1-3)] by auto
    have eqD1:"CommSetFold(f,{\<langle>m,(AA`m)\<cdot>\<^sub>M (B`m)\<rangle>. m\<in>domain(AA)},D)=Fold1(f,{\<langle>m,(AA`m)\<cdot>\<^sub>M (B`m)\<rangle>. m\<in>domain(AA)} O g)" 
      using commsemigr.sum_over_set_bij[OF comm] assms(3) A
      domA assms(4) by blast
    {
      fix n assume n:"n\<in>|D|"
      then have T:"({\<langle>m,(AA`m)\<cdot>\<^sub>M (B`m)\<rangle>. m\<in>domain(AA)} O g)`n={\<langle>m,(AA`m)\<cdot>\<^sub>M (B`m)\<rangle>. m\<in>domain(AA)}`( g`n)"
        using comp_fun_apply funf unfolding bij_def inj_def by auto
      have "g`n\<in>D" using assms(4) unfolding bij_def inj_def using apply_type n by auto
      then have "g`n\<in>domain(AA)" using domA assms(3) unfolding FinPow_def by auto
      then have "{\<langle>m,(AA`m)\<cdot>\<^sub>M (B`m)\<rangle>. m\<in>domain(AA)}`( g`n)=(AA`(g`n))\<cdot>\<^sub>M (B`( g`n))" using apply_equality[OF _ fun_aux[OF assms(1,2)]]
        domA by auto
      also have "\<dots>=((AA O g)`n)\<cdot>\<^sub>M ((B O g)`n)" using comp_fun_apply funf n by auto
      also have "\<dots>={\<langle>m,((AA O g)`m)\<cdot>\<^sub>M ((B O g)`m)\<rangle>. m\<in>|D|}`n" using apply_equality[OF _ fun_aux[OF comp_fun[OF funf assms(1)] comp_fun[OF funf assms(2)]]]
        n by auto
      ultimately have "({\<langle>m,(AA`m)\<cdot>\<^sub>M (B`m)\<rangle>. m\<in>domain(AA)} O g)`n={\<langle>m,((AA O g)`m)\<cdot>\<^sub>M ((B O g)`m)\<rangle>. m\<in>|D|}`n" using T by auto
    }
    then have "\<forall>x\<in>|D|. ({\<langle>m,(AA`m)\<cdot>\<^sub>M (B`m)\<rangle>. m\<in>domain(AA)} O g)`x={\<langle>m,((AA O g)`m)\<cdot>\<^sub>M ((B O g)`m)\<rangle>. m\<in>|D|}`x" by auto
    then have eq:"{\<langle>m,(AA`m)\<cdot>\<^sub>M (B`m)\<rangle>. m\<in>domain(AA)} O g={\<langle>m,((AA O g)`m)\<cdot>\<^sub>M ((B O g)`m)\<rangle>. m\<in>|D|}" using func_eq[OF comp_fun[OF funf fun_aux[OF assms(1) assms(2)]]
      fun_aux[OF comp_fun[OF funf assms(1)] comp_fun[OF funf assms(2)]]] domA by auto
    have R1:"\<Sum>[D;{AA,B}]=Fold1(f,{\<langle>m,((AA O g)`m)\<cdot>\<^sub>M ((B O g)`m)\<rangle>. m\<in>|D|})"
      using trans[OF eqD eqD1] subst[OF eq, of "\<lambda>t. \<Sum>[D;{AA,B}] = Fold1(f,t)"] by blast
    from A have Dno:"|D|\<noteq>0" using assms(4) unfolding bij_def surj_def by auto
    have "||D||=|D|" using cardinal_cong assms(4) unfolding eqpoll_def by auto
    then have idf:"id(|D|)\<in>bij(||D||,|D|)" using id_bij by auto
    have comm:"commsemigr(G, f, |D|, {\<langle>m, (AA O g) ` m \<cdot>\<^sub>M ((B O g) ` m)\<rangle> . m \<in> |D|})"
      unfolding commsemigr_def using ab_group.abelian_group_axioms
      unfolding abelian_group_def group0_def IsAgroup_def IsAmonoid_def
      abelian_group_axioms_def using fun_aux[OF comp_fun[OF funf assms(1)] comp_fun[OF funf assms(2)]]
      by auto
    have sub:"{\<langle>m, (AA O g) ` m \<cdot>\<^sub>M ((B O g) ` m)\<rangle> . m \<in> |D|} \<subseteq> |D|\<times>G" using
      fun_aux[OF comp_fun[OF funf assms(1)] comp_fun[OF funf assms(2)]]
      unfolding Pi_def by auto
    have finE:"Finite(|D|)" using assms(4,3) eqpoll_imp_Finite_iff unfolding eqpoll_def FinPow_def by auto
    then have EFP:"|D|\<in>FinPow(|D|)" unfolding FinPow_def by auto
    then have eqE:"\<Sum>[|D|;{AA O g,B O g}]=CommSetFold(f,{\<langle>m,((AA O g)`m)\<cdot>\<^sub>M ((B O g)`m)\<rangle>. m\<in>domain(AA O g)},|D|)" using LinearComb_def[OF comp_fun[OF funf assms(1)]
      comp_fun[OF funf assms(2)]] Dno by auto
    also have "\<dots>=CommSetFold(f,{\<langle>m,((AA O g)`m)\<cdot>\<^sub>M ((B O g)`m)\<rangle>. m\<in>|D|},|D|)" using domAg by auto
    also have "\<dots>=Fold1(f,{\<langle>m,((AA O g)`m)\<cdot>\<^sub>M ((B O g)`m)\<rangle>. m\<in>|D|})" using commsemigr.sum_over_set_bij[OF comm
      EFP Dno idf]
      subst[OF right_comp_id[of "{\<langle>m,((AA O g)`m)\<cdot>\<^sub>M ((B O g)`m)\<rangle>. m\<in>|D|}" "|D|" "G", OF sub], 
        of "\<lambda>t. CommSetFold(f,{\<langle>m,((AA O g)`m)\<cdot>\<^sub>M ((B O g)`m)\<rangle>. m\<in>|D|},|D|) = Fold1(f,t)"]
      by blast
    ultimately have "\<Sum>[|D|;{AA O g,B O g}]=Fold1(f,{\<langle>m,((AA O g)`m)\<cdot>\<^sub>M ((B O g)`m)\<rangle>. m\<in>|D|})"
      by (simp only:trans)
    with R1 have ?thesis by (simp only:trans sym)
  }
  ultimately show ?thesis by blast
qed

text\<open>Actually a linear combination can be defined over any
bijective set.\<close>

lemma(in module0) linComb_reorder_terms2:
  assumes "AA:X\<rightarrow>R" "B:X\<rightarrow>G" "D\<in>FinPow(X)" "g\<in>bij(E,D)"
  shows "(\<Sum>[D;{AA,B}])=\<Sum>[E;{AA O g,B O g}]"
proof-
  from assms(3,4) have funf:"g:E\<rightarrow>X" unfolding bij_def inj_def FinPow_def using func1_1_L1B by auto
  have ABfun:"AA O g:E\<rightarrow>R" "B O g:E\<rightarrow>G" using comp_fun[OF funf assms(1)] comp_fun[OF funf assms(2)] by auto
  then have domAg:"domain(AA O g)=E" unfolding Pi_def by auto
  from assms(1) have domA:"domain(AA)=X" unfolding Pi_def by auto
  from assms(3-4) have finE:"Finite(E)" unfolding FinPow_def using eqpoll_imp_Finite_iff unfolding eqpoll_def by auto
  then have "|E|\<approx>E" using well_ord_cardinal_eqpoll Finite_imp_well_ord by blast
  then obtain h where h:"h\<in>bij(|E|,E)" unfolding eqpoll_def by auto
  then have "(g O h)\<in>bij(|E|,D)" using comp_bij assms(4) by auto moreover
  have ED:"|E|=|D|" using cardinal_cong assms(4) unfolding eqpoll_def by auto
  ultimately have "(g O h)\<in>bij(|D|,D)" by auto
  then have "(\<Sum>[D;{AA,B}])=(\<Sum>[|D|;{AA O (g O h),B O (g O h)}])" using linComb_reorder_terms1 assms(1-3) by auto moreover
  from h have "(\<Sum>[E;{AA O g,B O g}])=(\<Sum>[|E|;{(AA O g) O h,(B O g) O h}])" using linComb_reorder_terms1 comp_fun[OF funf assms(1)] comp_fun[OF funf assms(2)] 
    finE unfolding FinPow_def by auto
  moreover note ED ultimately
  show ?thesis using comp_assoc by auto
qed

text\<open>Restricting the defining functions to the domain set does nothing to
the linear combination\<close>

corollary(in module0) linComb_restrict_coord:
  assumes "AA:X\<rightarrow>R" "B:X\<rightarrow>G" "D\<in>FinPow(X)"
  shows "(\<Sum>[D;{AA,B}])=\<Sum>[D;{restrict(AA,D),restrict(B,D)}]"
  using linComb_reorder_terms2[OF assms id_bij] right_comp_id_any by auto

text\<open>A linear combination can by defined with a natural number
and functions with that number as domain.\<close>

corollary(in module0) linComb_nat:
  assumes "AA:X\<rightarrow>R" "B:X\<rightarrow>G" "D\<in>FinPow(X)"
  shows "\<exists>n\<in>nat. \<exists>A1\<in>n\<rightarrow>R. \<exists>B1\<in>n\<rightarrow>G. \<Sum>[D;{AA,B}]=\<Sum>[n;{A1,B1}] \<and> A1``n=AA``D \<and> B1``n=B``D"
proof
  from assms(3) have fin:"Finite(D)" unfolding FinPow_def by auto
  then obtain n where n:"n\<in>nat" "D\<approx>n" unfolding Finite_def by auto moreover
  from fin have "|D|\<approx>D" using well_ord_cardinal_eqpoll Finite_imp_well_ord by blast
  ultimately have "|D|\<approx>n" "n\<in>nat" using eqpoll_trans[of "|D|"] by auto
  then have "n\<in>nat" "||D||=|n|" using cardinal_cong by auto
  then have D:"|D|=n" "n\<in>nat" using Card_cardinal_eq[OF Card_cardinal] Card_cardinal_eq[OF nat_into_Card] by auto
  then show "|D|\<in>nat" by auto
  from n(2) D(1) obtain g where g:"g\<in>bij(|D|,D)" using eqpoll_sym unfolding eqpoll_def by auto
  show "\<exists>A1\<in>|D|\<rightarrow>R. \<exists>B1\<in>|D|\<rightarrow>G. \<Sum>[D;{AA,B}]=\<Sum>[|D|;{A1,B1}] \<and> A1``|D|=AA``D \<and> B1``|D|=B``D"
  proof
    from g have gX:"g:|D|\<rightarrow>X" unfolding bij_def inj_def using assms(3) unfolding FinPow_def using func1_1_L1B by auto
    then show "(AA O g):|D|\<rightarrow>R" using comp_fun assms(1) by auto
    show "\<exists>B1\<in>|D|\<rightarrow>G. \<Sum>[D;{AA,B}]=\<Sum>[|D|;{AA O g,B1}] \<and> (AA O g)``|D|=AA``D \<and> B1``|D|=B``D"
    proof
      show "(B O g):|D|\<rightarrow>G" using comp_fun assms(2) gX by auto
      have "\<Sum>[D;{AA,B}]=\<Sum>[|D|;{AA O g,B O g}]" using g linComb_reorder_terms1 assms func1_1_L1B by auto
      moreover have "(AA O g)``|D|=AA``(g``|D|)" using image_comp by auto
      then have "(AA O g)``|D|=AA``D" using g unfolding bij_def using surj_range_image_domain by auto
      moreover have "(B O g)``|D|=B``(g``|D|)" using image_comp by auto
      then have "(B O g)``|D|=B``D" using g unfolding bij_def using surj_range_image_domain by auto
      ultimately show "\<Sum>[D;{AA,B}]=\<Sum>[|D|;{AA O g,B O g}] \<and> (AA O g)``|D|=AA``D \<and> (B O g)``|D|=B``D" by auto
    qed
  qed
qed

text\<open>Any natural number is finite subset of itself\<close>

lemma(in module0) auxiliar_nat:
  assumes "n\<in>nat"
  shows "n\<in>FinPow(n)" unfolding FinPow_def Finite_def using assms eqpoll_refl by blast

text \<open>Next, we'll prove that the addition of two linear combinations
is a linear combination. The proof is done by induction.\<close>

text \<open>Adding a linear combination defined over $\emptyset$ leaves it as is\<close>

lemma(in module0) linComb_sum_base_induct1:
  assumes "AA:X\<rightarrow>R" "B:X\<rightarrow>G" "D\<in>FinPow(X)" "AA1:Y\<rightarrow>R" "B1:Y\<rightarrow>G"
  shows "(\<Sum>[D;{AA,B}])\<ra>\<^sub>G(\<Sum>[0;{AA1,B1}])=\<Sum>[D;{AA,B}]"
proof-
  from assms(1-3) have "\<Sum>[D;{AA,B}]\<in>G" using linComb_is_in_module by auto
  then have eq:"(\<Sum>[D;{AA,B}])\<ra>\<^sub>G(\<zero>\<^sub>G)=\<Sum>[D;{AA,B}]" using ab_group.group0_2_L2
    by auto moreover
  have ff:"0\<in>FinPow(Y)" unfolding FinPow_def by auto
  from eq show ?thesis using LinearComb_def[OF assms(4-5) ff] by auto
qed

text\<open>Applying a product of $1\times$ to the defining set computes the same linear combination\<close>

lemma(in module0) linComb_sum_base_induct2:
  assumes "AA:X\<rightarrow>R" "B:X\<rightarrow>G" "D\<in>FinPow(X)"
  shows "(\<Sum>[D;{AA,B}])=\<Sum>[{0}\<times>D;{{\<langle>\<langle>0,x\<rangle>,AA`x\<rangle>. x\<in>X},{\<langle>\<langle>0,x\<rangle>,B`x\<rangle>. x\<in>X}}]" and
  "(\<Sum>[D;{AA,B}])=\<Sum>[{0}\<times>D;{restrict({\<langle>\<langle>0,x\<rangle>,AA`x\<rangle>. x\<in>X},{0}\<times>D),restrict({\<langle>\<langle>0,x\<rangle>,B`x\<rangle>. x\<in>X},{0}\<times>D)}]"
proof-
  let ?g="{\<langle>\<langle>0,d\<rangle>,d\<rangle>. d\<in>D}"
  from assms(3) have sub:"D\<subseteq>X" unfolding FinPow_def by auto
  have gfun:"?g:{0}\<times>D\<rightarrow>D" unfolding Pi_def function_def by blast
  then have gfunX:"?g:{0}\<times>D\<rightarrow>X" using sub func1_1_L1B by auto
  from gfun have "?g\<in>surj({0}\<times>D,D)" unfolding surj_def using apply_equality[OF _ gfun] by blast moreover
  {
    fix w y assume "?g`w=?g`y" "w\<in>{0}\<times>D" "y\<in>{0}\<times>D"
    then obtain dw dy where "w=\<langle>0,dw\<rangle>" "y=\<langle>0,dy\<rangle>" "?g`w=?g`y" "dw\<in>D" "dy\<in>D" by auto
    then have "dw=dy" "w=\<langle>0,dw\<rangle>" "y=\<langle>0,dy\<rangle>" using apply_equality[OF _ gfun, of w dw] apply_equality[OF _ gfun, of y dy] by auto
    then have "w=y" by auto
  }
  then have "?g\<in>inj({0}\<times>D,D)" unfolding inj_def using gfun by auto ultimately
  have gbij:"?g\<in>bij({0}\<times>D,D)" unfolding bij_def by auto
  with assms have A1:"(\<Sum>[D;{AA,B}])=\<Sum>[{0}\<times>D;{AA O ?g,B O ?g}]" using linComb_reorder_terms2 by auto
  from gbij have "Finite({0}\<times>D)" using assms(3) eqpoll_imp_Finite_iff unfolding FinPow_def eqpoll_def by auto
  then have fin:"{0}\<times>D\<in>FinPow({0}\<times>X)" unfolding FinPow_def using sub by auto
  have A0:"{\<langle>\<langle>0,x\<rangle>,AA`x\<rangle>. x\<in>X}:{0}\<times>X\<rightarrow>R" unfolding Pi_def function_def using apply_type[OF assms(1)] by auto
  have B0:"{\<langle>\<langle>0,x\<rangle>,B`x\<rangle>. x\<in>X}:{0}\<times>X\<rightarrow>G" unfolding Pi_def function_def using apply_type[OF assms(2)] by auto
  {
    fix r assume "r\<in>{0}\<times>D"
    then obtain rd where rd:"r=\<langle>0,rd\<rangle>" "rd\<in>D" by auto
    then have "(AA O ?g)`r=AA`rd" using comp_fun_apply gfun apply_equality by auto
    also have "\<dots>={\<langle>\<langle>0,x\<rangle>,AA`x\<rangle>. x\<in>X}`\<langle>0,rd\<rangle>" using apply_equality[OF _ A0] sub rd(2) by auto
    also have "\<dots>=restrict({\<langle>\<langle>0,x\<rangle>,AA`x\<rangle>. x\<in>X},{0}\<times>D)`\<langle>0,rd\<rangle>" using restrict rd(2) by auto
    ultimately have "(AA O ?g)`r=restrict({\<langle>\<langle>0,x\<rangle>,AA`x\<rangle>. x\<in>X},{0}\<times>D)`r" using rd(1) by auto
  }
  then have "\<forall>r\<in>{0}\<times>D. (AA O ?g)`r=restrict({\<langle>\<langle>0,x\<rangle>,AA`x\<rangle>. x\<in>X},{0}\<times>D)`r" by auto moreover
  have "AA O ?g:{0}\<times>D\<rightarrow>R" using gfunX assms(1) comp_fun by auto moreover
  have "{0}\<times>D\<subseteq>{0}\<times>X" using sub by auto
  then have "restrict({\<langle>\<langle>0,x\<rangle>,AA`x\<rangle>. x\<in>X},{0}\<times>D):{0}\<times>D\<rightarrow>R" using A0 restrict_fun by auto ultimately
  have f1:"(AA O ?g)=restrict({\<langle>\<langle>0,x\<rangle>,AA`x\<rangle>. x\<in>X},{0}\<times>D)" using func_eq[of "AA O ?g" "{0}\<times>D" R "restrict({\<langle>\<langle>0, x\<rangle>, AA ` x\<rangle> . x \<in> X}, {0} \<times> D)"]
    by auto
  {
    fix r assume "r\<in>{0}\<times>D"
    then obtain rd where rd:"r=\<langle>0,rd\<rangle>" "rd\<in>D" by auto
    then have "(B O ?g)`r=B`rd" using comp_fun_apply gfun apply_equality by auto
    also have "\<dots>={\<langle>\<langle>0,x\<rangle>,B`x\<rangle>. x\<in>X}`\<langle>0,rd\<rangle>" using apply_equality[OF _ B0] sub rd(2) by auto
    also have "\<dots>=restrict({\<langle>\<langle>0,x\<rangle>,B`x\<rangle>. x\<in>X},{0}\<times>D)`\<langle>0,rd\<rangle>" using restrict rd(2) by auto
    ultimately have "(B O ?g)`r=restrict({\<langle>\<langle>0,x\<rangle>,B`x\<rangle>. x\<in>X},{0}\<times>D)`r" using rd(1) by auto
  }
  then have "\<forall>r\<in>{0}\<times>D. (B O ?g)`r=restrict({\<langle>\<langle>0,x\<rangle>,B`x\<rangle>. x\<in>X},{0}\<times>D)`r" by auto moreover
  have "B O ?g:{0}\<times>D\<rightarrow>G" using gfunX assms(2) comp_fun by auto moreover
  have "{0}\<times>D\<subseteq>{0}\<times>X" using sub by auto
  then have "restrict({\<langle>\<langle>0,x\<rangle>,B`x\<rangle>. x\<in>X},{0}\<times>D):{0}\<times>D\<rightarrow>G" using B0 restrict_fun by auto ultimately
  have "(B O ?g)=restrict({\<langle>\<langle>0,x\<rangle>,B`x\<rangle>. x\<in>X},{0}\<times>D)" using func_eq[of "B O ?g" "{0}\<times>D" G "restrict({\<langle>\<langle>0, x\<rangle>, B ` x\<rangle> . x \<in> X}, {0} \<times> D)"]
    by auto
  with A1 f1 show "(\<Sum>[D;{AA,B}])=\<Sum>[{0}\<times>D;{restrict({\<langle>\<langle>0,x\<rangle>,AA`x\<rangle>. x\<in>X},{0}\<times>D),restrict({\<langle>\<langle>0,x\<rangle>,B`x\<rangle>. x\<in>X},{0}\<times>D)}]" by auto
  also have "\<dots>=\<Sum>[{0}\<times>D;{{\<langle>\<langle>0,x\<rangle>,AA`x\<rangle>. x\<in>X},{\<langle>\<langle>0,x\<rangle>,B`x\<rangle>. x\<in>X}}]" using linComb_restrict_coord[OF A0 B0 fin] by auto
  ultimately show "(\<Sum>[D;{AA,B}])=\<Sum>[{0}\<times>D;{{\<langle>\<langle>0,x\<rangle>,AA`x\<rangle>. x\<in>X},{\<langle>\<langle>0,x\<rangle>,B`x\<rangle>. x\<in>X}}]" by auto
qed

text\<open>Then, we can model adding a liner combination on the empty set
as a linear combination of the disjoint union of sets\<close>

lemma(in module0) linComb_sum_base_induct:
  assumes "AA:X\<rightarrow>R" "B:X\<rightarrow>G" "D\<in>FinPow(X)" "AA1:Y\<rightarrow>R" "B1:Y\<rightarrow>G"
  shows "(\<Sum>[D;{AA,B}])\<ra>\<^sub>G(\<Sum>[0;{AA1,B1}])=\<Sum>[D+0;{{\<langle>\<langle>0,x\<rangle>,AA`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,AA1`x\<rangle>. x\<in>Y},{\<langle>\<langle>0,x\<rangle>,B`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,B1`x\<rangle>. x\<in>Y}}]"
proof-
  from assms(3) have sub:"D\<subseteq>X" unfolding FinPow_def by auto
  then have sub2:"{0}\<times>D\<subseteq>{0}\<times>X" by auto
  then have sub3:"{0}\<times>D\<in>Pow(X+Y)" unfolding sum_def by auto
  let ?g="{\<langle>\<langle>0,x\<rangle>,x\<rangle>. x\<in>D}"
  have gfun:"?g:{0}\<times>D\<rightarrow>D" unfolding Pi_def function_def by blast
  then have "?g\<in>surj({0}\<times>D,D)" unfolding surj_def using apply_equality by auto moreover
  {
    fix w y assume "?g`w=?g`y" "w\<in>{0}\<times>D" "y\<in>{0}\<times>D"
    then obtain dw dy where "w=\<langle>0,dw\<rangle>" "y=\<langle>0,dy\<rangle>" "?g`w=?g`y" "dw\<in>D" "dy\<in>D" by auto
    then have "dw=dy" "w=\<langle>0,dw\<rangle>" "y=\<langle>0,dy\<rangle>" using apply_equality[OF _ gfun, of w dw] apply_equality[OF _ gfun, of y dy] by auto
    then have "w=y" by auto
  }
  then have "?g\<in>inj({0}\<times>D,D)" unfolding inj_def using gfun by auto ultimately
  have gbij:"?g\<in>bij({0}\<times>D,D)" unfolding bij_def by auto
  then have "Finite({0}\<times>D)" using assms(3) eqpoll_imp_Finite_iff unfolding FinPow_def eqpoll_def by auto
  with sub3 have finpow0D:"{0}\<times>D\<in>FinPow(X+Y)" unfolding FinPow_def by auto
  have A0:"{\<langle>\<langle>0,x\<rangle>,AA`x\<rangle>. x\<in>X}:{0}\<times>X\<rightarrow>R" unfolding Pi_def function_def using apply_type[OF assms(1)] by auto
  have A1:"{\<langle>\<langle>1,x\<rangle>,AA1`x\<rangle>. x\<in>Y}:{1}\<times>Y\<rightarrow>R" unfolding Pi_def function_def using apply_type[OF assms(4)] by auto
  have domA0:"domain({\<langle>\<langle>0,x\<rangle>,AA`x\<rangle>. x\<in>X})={0}\<times>X" by auto
  have domA1:"domain({\<langle>\<langle>1,x\<rangle>,AA1`x\<rangle>. x\<in>Y})={1}\<times>Y" by auto
  have A:"{\<langle>\<langle>0,x\<rangle>,AA`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,AA1`x\<rangle>. x\<in>Y}:X+Y\<rightarrow>R" using fun_disjoint_Un[OF A0 A1] unfolding sum_def by auto
  have B0:"{\<langle>\<langle>0,x\<rangle>,B`x\<rangle>. x\<in>X}:{0}\<times>X\<rightarrow>G" unfolding Pi_def function_def using apply_type[OF assms(2)] by auto
  have B1:"{\<langle>\<langle>1,x\<rangle>,B1`x\<rangle>. x\<in>Y}:{1}\<times>Y\<rightarrow>G" unfolding Pi_def function_def using apply_type[OF assms(5)] by auto
  then have domB0:"domain({\<langle>\<langle>0,x\<rangle>,B`x\<rangle>. x\<in>X})={0}\<times>X" unfolding Pi_def by auto
  then have domB1:"domain({\<langle>\<langle>1,x\<rangle>,B1`x\<rangle>. x\<in>Y})={1}\<times>Y" unfolding Pi_def by auto
  have B:"{\<langle>\<langle>0,x\<rangle>,B`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,B1`x\<rangle>. x\<in>Y}:X+Y\<rightarrow>G" using fun_disjoint_Un[OF B0 B1] unfolding sum_def by auto
  have "(\<Sum>[D;{AA,B}])\<ra>\<^sub>G(\<Sum>[0;{AA1,B1}])=\<Sum>[D;{AA,B}]" using linComb_sum_base_induct1 assms by auto
  also have "\<dots>=\<Sum>[{0}\<times>D;{restrict({\<langle>\<langle>0,x\<rangle>,AA`x\<rangle>. x\<in>X},{0}\<times>D),restrict({\<langle>\<langle>0,x\<rangle>,B`x\<rangle>. x\<in>X},{0}\<times>D)}]" using linComb_sum_base_induct2(2) assms(1-3) by auto
  ultimately have eq1:"(\<Sum>[D;{AA,B}])\<ra>\<^sub>G(\<Sum>[0;{AA1,B1}])=\<Sum>[{0}\<times>D;{restrict({\<langle>\<langle>0,x\<rangle>,AA`x\<rangle>. x\<in>X},{0}\<times>D),restrict({\<langle>\<langle>0,x\<rangle>,B`x\<rangle>. x\<in>X},{0}\<times>D)}]" by auto
  {
    fix s assume "s\<in>{0}\<times>D"
    then obtain ds where ds:"ds\<in>D" "s=\<langle>0,ds\<rangle>" by auto
    then have "restrict({\<langle>\<langle>0,x\<rangle>,AA`x\<rangle>. x\<in>X},{0}\<times>D)`s={\<langle>\<langle>0,x\<rangle>,AA`x\<rangle>. x\<in>X}`s" using restrict by auto
    also have "\<dots>=({\<langle>\<langle>0,x\<rangle>,AA`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,AA1`x\<rangle>. x\<in>Y})`s" using fun_disjoint_apply1 domA1 ds(2) by auto
    also have "\<dots>=restrict({\<langle>\<langle>0,x\<rangle>,AA`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,AA1`x\<rangle>. x\<in>Y},{0}\<times>D)`s" using restrict ds by auto
    ultimately have "restrict({\<langle>\<langle>0,x\<rangle>,AA`x\<rangle>. x\<in>X},{0}\<times>D)`s=restrict({\<langle>\<langle>0,x\<rangle>,AA`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,AA1`x\<rangle>. x\<in>Y},{0}\<times>D)`s" by auto
  }
  then have tot:"\<forall>s\<in>{0}\<times>D. restrict({\<langle>\<langle>0,x\<rangle>,AA`x\<rangle>. x\<in>X},{0}\<times>D)`s=restrict({\<langle>\<langle>0,x\<rangle>,AA`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,AA1`x\<rangle>. x\<in>Y},{0}\<times>D)`s" by auto moreover
  have f1:"restrict({\<langle>\<langle>0,x\<rangle>,AA`x\<rangle>. x\<in>X},{0}\<times>D):{0}\<times>D\<rightarrow>R" using restrict_fun A0 sub2 by auto moreover
  have f2:"restrict({\<langle>\<langle>0,x\<rangle>,AA`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,AA1`x\<rangle>. x\<in>Y},{0}\<times>D):{0}\<times>D\<rightarrow>R" using restrict_fun[OF fun_disjoint_Un[OF A0 A1]] sub2 by auto
  ultimately have fA:"restrict({\<langle>\<langle>0,x\<rangle>,AA`x\<rangle>. x\<in>X},{0}\<times>D)=restrict({\<langle>\<langle>0,x\<rangle>,AA`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,AA1`x\<rangle>. x\<in>Y},{0}\<times>D)" using func_eq[OF f1 f2] by auto
  {
    fix s assume "s\<in>{0}\<times>D"
    then obtain ds where ds:"ds\<in>D" "s=\<langle>0,ds\<rangle>" by auto
    then have "restrict({\<langle>\<langle>0,x\<rangle>,B`x\<rangle>. x\<in>X},{0}\<times>D)`s={\<langle>\<langle>0,x\<rangle>,B`x\<rangle>. x\<in>X}`s" using restrict by auto
    also have "\<dots>=({\<langle>\<langle>0,x\<rangle>,B`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,B1`x\<rangle>. x\<in>Y})`s" using fun_disjoint_apply1 domB1 ds(2) by auto
    also have "\<dots>=restrict({\<langle>\<langle>0,x\<rangle>,B`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,B1`x\<rangle>. x\<in>Y},{0}\<times>D)`s" using restrict ds by auto
    ultimately have "restrict({\<langle>\<langle>0,x\<rangle>,B`x\<rangle>. x\<in>X},{0}\<times>D)`s=restrict({\<langle>\<langle>0,x\<rangle>,B`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,B1`x\<rangle>. x\<in>Y},{0}\<times>D)`s" by auto
  }
  then have tot:"\<forall>s\<in>{0}\<times>D. restrict({\<langle>\<langle>0,x\<rangle>,B`x\<rangle>. x\<in>X},{0}\<times>D)`s=restrict({\<langle>\<langle>0,x\<rangle>,B`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,B1`x\<rangle>. x\<in>Y},{0}\<times>D)`s" by auto moreover
  have f1:"restrict({\<langle>\<langle>0,x\<rangle>,B`x\<rangle>. x\<in>X},{0}\<times>D):{0}\<times>D\<rightarrow>G" using restrict_fun B0 sub2 by auto moreover
  have f2:"restrict({\<langle>\<langle>0,x\<rangle>,B`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,B1`x\<rangle>. x\<in>Y},{0}\<times>D):{0}\<times>D\<rightarrow>G" using restrict_fun[OF fun_disjoint_Un[OF B0 B1]] sub2 by auto
  ultimately have fB:"restrict({\<langle>\<langle>0,x\<rangle>,B`x\<rangle>. x\<in>X},{0}\<times>D)=restrict({\<langle>\<langle>0,x\<rangle>,B`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,B1`x\<rangle>. x\<in>Y},{0}\<times>D)" using func_eq[OF f1 f2] by auto
  with fA eq1 have "(\<Sum>[D;{AA,B}])\<ra>\<^sub>G(\<Sum>[0;{AA1,B1}])=\<Sum>[{0}\<times>D;{restrict({\<langle>\<langle>0,x\<rangle>,AA`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,AA1`x\<rangle>. x\<in>Y},{0}\<times>D),restrict({\<langle>\<langle>0,x\<rangle>,B`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,B1`x\<rangle>. x\<in>Y},{0}\<times>D)}]"
    by auto
  also have "\<dots>=\<Sum>[{0}\<times>D;{{\<langle>\<langle>0,x\<rangle>,AA`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,AA1`x\<rangle>. x\<in>Y},{\<langle>\<langle>0,x\<rangle>,B`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,B1`x\<rangle>. x\<in>Y}}]" using linComb_restrict_coord[OF A B finpow0D]
    by auto
  also have "\<dots>=\<Sum>[D+0;{{\<langle>\<langle>0,x\<rangle>,AA`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,AA1`x\<rangle>. x\<in>Y},{\<langle>\<langle>0,x\<rangle>,B`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,B1`x\<rangle>. x\<in>Y}}]" unfolding sum_def by auto
  ultimately show ?thesis by auto
qed

text\<open>An element of the set for the linear combination
can be removed and add it using group addition.\<close>

lemma(in module0) sum_one_element:
  assumes "AA:X\<rightarrow>R" "B:X\<rightarrow>G" "D\<in>FinPow(X)" "t\<in>D"
  shows "(\<Sum>[D;{AA,B}])=(\<Sum>[D-{t};{AA,B}])\<ra>\<^sub>G({\<langle>k,(AA`k)\<cdot>\<^sub>M(B`k)\<rangle>. k\<in>X}`t)"
proof-
  from assms(1,2) have af:"{\<langle>k,(AA`k)\<cdot>\<^sub>M(B`k)\<rangle>. k\<in>X}:X\<rightarrow>G" using fun_aux by auto  
  from assms(3) have sub:"D\<subseteq>X" unfolding FinPow_def by auto
  then have tX:"t\<in>X" using assms(4) by auto
  have dom:"domain(AA)=X" using assms(1) Pi_def by auto
  {
    assume A:"D-{t}=0"
    with assms(4) have "D={t}" by auto
    then have "(\<Sum>[D;{AA,B}])=\<Sum>[{t};{AA,B}]" by auto
    also have "\<dots>=(AA`t)\<cdot>\<^sub>M(B`t)" using linComb_one_element sub assms(1,2,4) by auto
    also have "\<dots>={\<langle>k,(AA`k)\<cdot>\<^sub>M(B`k)\<rangle>. k\<in>X}`t" using af assms(4) sub apply_equality by auto
    also have "\<dots>=\<zero>\<^sub>G\<ra>\<^sub>G({\<langle>k,(AA`k)\<cdot>\<^sub>M(B`k)\<rangle>. k\<in>X}`t)" using ab_group.group0_2_L2
      apply_type[OF af] assms(4) sub by auto
    also have "\<dots>=(\<Sum>[D-{t};{AA,B}])\<ra>\<^sub>G({\<langle>k,(AA`k)\<cdot>\<^sub>M(B`k)\<rangle>. k\<in>X}`t)" using A LinearComb_def[OF assms(1,2), of "D-{t}"]
      unfolding FinPow_def by auto
    ultimately have ?thesis by auto
  }
  moreover
  {
    assume A:"D-{t}\<noteq>0"
    then have D:"D\<noteq>0" by auto
    have comm:"commsemigr(G, f, X, {\<langle>k,(AA`k)\<cdot>\<^sub>M(B`k)\<rangle>. k\<in>X})"
      unfolding commsemigr_def using ab_group.abelian_group_axioms
      unfolding abelian_group_def abelian_group_axioms_def group0_def
      IsAgroup_def IsAmonoid_def using af by auto
    have fin:"D-{t}\<in>FinPow(X)" using assms(3) unfolding FinPow_def using subset_Finite[of "D-{t}" D] by auto
    have "(D-{t})\<union>{t}=D" "X-(D-{t})=(X-D)\<union>{t}" using assms(4) sub by auto
    then have "CommSetFold(f,{\<langle>k,(AA`k)\<cdot>\<^sub>M(B`k)\<rangle>. k\<in>X},D)=CommSetFold(f,{\<langle>k,(AA`k)\<cdot>\<^sub>M(B`k)\<rangle>. k\<in>X},D-{t})
      \<ra>\<^sub>G({\<langle>k,(AA`k)\<cdot>\<^sub>M(B`k)\<rangle>. k\<in>X}`t)" using commsemigr.sum_over_set_add_point(2)[OF comm
      fin A] by auto
    also have "\<dots>=(\<Sum>[D-{t};{AA,B}])\<ra>\<^sub>G({\<langle>k,(AA`k)\<cdot>\<^sub>M(B`k)\<rangle>. k\<in>X}`t)" using LinearComb_def[OF assms(1,2) fin] A
      dom by auto
    ultimately have "CommSetFold(f,{\<langle>k,(AA`k)\<cdot>\<^sub>M(B`k)\<rangle>. k\<in>X},D)=(\<Sum>[D-{t};{AA,B}])\<ra>\<^sub>G({\<langle>k,(AA`k)\<cdot>\<^sub>M(B`k)\<rangle>. k\<in>X}`t)" by auto moreover
    then have ?thesis unfolding LinearComb_def[OF assms(1-3)] using D dom by auto
  }
  ultimately show ?thesis by blast
qed


text\<open>If the ring element is zero, then that summand is not necessary.\<close>

corollary(in module0) linComb_zero_coef:
  assumes "AA`t=\<zero>\<^sub>R" "AA:X\<rightarrow>R" "B:X\<rightarrow>G" "t\<in>D" "D\<in>FinPow(X)"
  shows "\<Sum>[D;{AA,B}]=\<Sum>[D-{t};{AA,B}]"
proof-
  from assms(2-5) have "\<Sum>[D;{AA,B}]=(\<Sum>[D-{t};{AA,B}])\<ra>\<^sub>G({\<langle>k,(AA`k)\<cdot>\<^sub>M(B`k)\<rangle>. k\<in>X}`t)" using sum_one_element
    by auto
  also have "\<dots>=(\<Sum>[D-{t};{AA,B}])\<ra>\<^sub>G((AA`t)\<cdot>\<^sub>M(B`t))" using assms(4,5) unfolding FinPow_def
    using apply_equality[OF _ fun_aux[OF assms(2,3)]] by auto
  also have "\<dots>=(\<Sum>[D-{t};{AA,B}])\<ra>\<^sub>G\<zero>\<^sub>G" using assms(1) mult_zeroR[OF apply_type[OF assms(3),of t]]
    assms(4,5) unfolding FinPow_def by auto
  ultimately have "\<Sum>[D;{AA,B}]=(\<Sum>[D-{t};{AA,B}])\<ra>\<^sub>G\<zero>\<^sub>G" by auto moreover
  have "D-{t}\<in>Pow(X)" using assms(5) unfolding FinPow_def by auto
  then have "D-{t}\<in>FinPow(X)" using assms(5) unfolding FinPow_def using subset_Finite[of "D-{t}" D]
    by blast ultimately
  show "\<Sum>[D;{AA,B}]=(\<Sum>[D-{t};{AA,B}])" using ab_group.group0_2_L2
    linComb_is_in_module[OF assms(2,3)] by auto
qed

text\<open>Any set of zero ring elements can be excluded
and the linear combination remains intact\<close>

corollary(in module0) linComb_zero_coef2:
  assumes "\<forall>t\<in>E. AA`t=\<zero>\<^sub>R" "AA:X\<rightarrow>R" "B:X\<rightarrow>G" "E\<subseteq>D" "D\<in>FinPow(X)"
  shows "\<Sum>[D;{AA,B}]=\<Sum>[D-E;{AA,B}]"
proof-
  have base:"\<forall>\<AA>\<in>X\<rightarrow>R. \<forall>\<BB>\<in>X\<rightarrow>G. ((\<forall>t\<in>0. \<AA>`t=\<zero>\<^sub>R \<and> 0\<subseteq>D) \<longrightarrow> \<Sum>[D;{\<AA>,\<BB>}]=\<Sum>[D-(0);{\<AA>,\<BB>}])" by auto
  {
    fix \<RR> assume R:"\<RR>\<in>FinPow(X)" "\<RR>\<noteq>0"
    then obtain r where r:"r\<in>\<RR>" by auto
    {
      fix \<AA> \<BB> \<AA>1 \<BB>1 assume fun:"\<AA>:X\<rightarrow>R" "\<BB>:X\<rightarrow>G" and 
        step:"\<forall>A1\<in>X\<rightarrow>R. \<forall>B1\<in>X\<rightarrow>G. ((\<forall>t\<in>\<RR>-{r}. A1`t=\<zero>\<^sub>R \<and> \<RR>-{r}\<subseteq>D) \<longrightarrow> \<Sum>[D;{A1,B1}]=\<Sum>[D-(\<RR>-{r});{A1,B1}])"
      {
        assume as:"\<forall>t\<in>\<RR>.  \<AA>`t=\<zero>\<^sub>R" "\<RR>\<subseteq>D"
        with fun step have "\<Sum>[D;{\<AA>,\<BB>}]=\<Sum>[D-(\<RR>-{r});{\<AA>,\<BB>}]" by auto moreover
        from as(2) r have "D-(\<RR>-{r})=(D-\<RR>)\<union>{r}" by auto ultimately
        have "\<Sum>[D;{\<AA>,\<BB>}]=\<Sum>[(D-\<RR>)\<union>{r};{\<AA>,\<BB>}]" by auto moreover
        have "((D-\<RR>)\<union>{r})-{r}=D-\<RR>" using r by auto
        moreover from as(1) r have "\<AA>`r=\<zero>\<^sub>R" by auto moreover
        have "r\<in>(D-\<RR>)\<union>{r}" by auto moreover
        have "Finite(D-\<RR>)" using subset_Finite[of "D-\<RR>" D] assms(5) unfolding FinPow_def by auto
        then have "Finite((D-\<RR>)\<union>{r})" using Finite_cons by auto
        then have "(D-\<RR>)\<union>{r}\<in>FinPow(X)" using r assms(5) R(1) unfolding FinPow_def by auto ultimately
        have "\<Sum>[D;{\<AA>,\<BB>}]=\<Sum>[(D-\<RR>);{\<AA>,\<BB>}]" using linComb_zero_coef[OF _ fun] by auto
      }
      then have "(\<forall>t\<in>\<RR>. \<AA>`t=\<zero>\<^sub>R \<and> \<RR>\<subseteq>D) \<longrightarrow> \<Sum>[D;{\<AA>,\<BB>}]=\<Sum>[D-(\<RR>);{\<AA>,\<BB>}]" by auto
    }
    then have "(\<forall>A1\<in>X\<rightarrow>R. \<forall>B1\<in>X\<rightarrow>G. ((\<forall>t\<in>\<RR>-{r}. A1`t=\<zero>\<^sub>R \<and> \<RR>-{r}\<subseteq>D) \<longrightarrow> \<Sum>[D;{A1,B1}]=\<Sum>[D-(\<RR>-{r});{A1,B1}])) 
      \<longrightarrow> (\<forall>\<AA>\<in>X\<rightarrow>R. \<forall>\<BB>\<in>X\<rightarrow>G. (\<forall>t\<in>\<RR>. \<AA>`t=\<zero>\<^sub>R \<and> \<RR>\<subseteq>D) \<longrightarrow> \<Sum>[D;{\<AA>,\<BB>}]=\<Sum>[D-(\<RR>);{\<AA>,\<BB>}])" by auto
    then have "\<exists>r\<in>\<RR>. (\<forall>A1\<in>X\<rightarrow>R. \<forall>B1\<in>X\<rightarrow>G. ((\<forall>t\<in>\<RR>-{r}. A1`t=\<zero>\<^sub>R \<and> \<RR>-{r}\<subseteq>D) \<longrightarrow> \<Sum>[D;{A1,B1}]=\<Sum>[D-(\<RR>-{r});{A1,B1}])) 
      \<longrightarrow> (\<forall>\<AA>\<in>X\<rightarrow>R. \<forall>\<BB>\<in>X\<rightarrow>G. (\<forall>t\<in>\<RR>. \<AA>`t=\<zero>\<^sub>R \<and> \<RR>\<subseteq>D) \<longrightarrow> \<Sum>[D;{\<AA>,\<BB>}]=\<Sum>[D-(\<RR>);{\<AA>,\<BB>}])" using r by auto
  }
  then have ind:"\<forall>\<RR>\<in>FinPow(X). \<RR>\<noteq>0 \<longrightarrow> (\<exists>r\<in>\<RR>. (\<forall>A1\<in>X\<rightarrow>R. \<forall>B1\<in>X\<rightarrow>G. ((\<forall>t\<in>\<RR>-{r}. A1`t=\<zero>\<^sub>R \<and> \<RR>-{r}\<subseteq>D) \<longrightarrow> \<Sum>[D;{A1,B1}]=\<Sum>[D-(\<RR>-{r});{A1,B1}])) 
      \<longrightarrow> (\<forall>\<AA>\<in>X\<rightarrow>R. \<forall>\<BB>\<in>X\<rightarrow>G. (\<forall>t\<in>\<RR>. \<AA>`t=\<zero>\<^sub>R \<and> \<RR>\<subseteq>D) \<longrightarrow> \<Sum>[D;{\<AA>,\<BB>}]=\<Sum>[D-(\<RR>);{\<AA>,\<BB>}]))" by auto
  from assms(4,5) have Efin:"E\<in>FinPow(X)" using subset_Finite unfolding FinPow_def by auto
  show ?thesis using FinPow_ind_rem_one[OF base ind Efin] assms(1-4) by auto
qed

text \<open>A small technical lemma to proof by induction on finite sets that the addition of linear combinations
is a linear combination\<close>

lemma(in module0) linComb_sum_ind_step:
  assumes "AA:X\<rightarrow>R" "B:X\<rightarrow>G" "D\<in>FinPow(X)" "E\<in>FinPow(Y)" "AA1:Y\<rightarrow>R" "B1:Y\<rightarrow>G" "t\<in>E" "D\<noteq>0"
    "(\<Sum>[D;{AA,B}])\<ra>\<^sub>G(\<Sum>[E-{t};{AA1,B1}])=\<Sum>[D+(E-{t});{{\<langle>\<langle>0,x\<rangle>,AA`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,AA1`x\<rangle>. x\<in>Y},{\<langle>\<langle>0,x\<rangle>,B`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,B1`x\<rangle>. x\<in>Y}}]"
  shows "(\<Sum>[D;{AA,B}])\<ra>\<^sub>G(\<Sum>[E;{AA1,B1}])=\<Sum>[D+E;{{\<langle>\<langle>0,x\<rangle>,AA`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,AA1`x\<rangle>. x\<in>Y},{\<langle>\<langle>0,x\<rangle>,B`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,B1`x\<rangle>. x\<in>Y}}]"
proof-
  have a1f:"{\<langle>k,(AA1`k)\<cdot>\<^sub>M(B1`k)\<rangle>. k\<in>Y}:Y\<rightarrow>G" using fun_aux assms(5,6) by auto
  with assms(4,7) have p1:"({\<langle>k,(AA1`k)\<cdot>\<^sub>M(B1`k)\<rangle>. k\<in>Y}`t)\<in>G" unfolding FinPow_def using apply_type by auto
  have p2:"\<Sum>[D;{AA,B}]\<in>G" using linComb_is_in_module assms(1-3) by auto
  have "E-{t}\<in>FinPow(Y)" using assms(4,7) unfolding FinPow_def using subset_Finite[of "E-{t}" E] by auto
  then have p3:"\<Sum>[E-{t};{AA1,B1}]\<in>G" using linComb_is_in_module assms(5,6) by auto
  have "\<Sum>[E;{AA1,B1}]=(\<Sum>[E-{t};{AA1,B1}])\<ra>\<^sub>G({\<langle>k,(AA1`k)\<cdot>\<^sub>M(B1`k)\<rangle>. k\<in>Y}`t)" using sum_one_element[OF assms(5,6,4,7)].
  then have "(\<Sum>[D;{AA,B}])\<ra>\<^sub>G(\<Sum>[E;{AA1,B1}])=(\<Sum>[D;{AA,B}])\<ra>\<^sub>G((\<Sum>[E-{t};{AA1,B1}])\<ra>\<^sub>G({\<langle>k,(AA1`k)\<cdot>\<^sub>M(B1`k)\<rangle>. k\<in>Y}`t))" by auto
  also have "\<dots>=((\<Sum>[D;{AA,B}])\<ra>\<^sub>G(\<Sum>[E-{t};{AA1,B1}]))\<ra>\<^sub>G({\<langle>k,(AA1`k)\<cdot>\<^sub>M(B1`k)\<rangle>. k\<in>Y}`t)"
    using p1 p2 p3 ab_group.group_oper_assoc by auto
  also have "\<dots>=(\<Sum>[D+(E-{t});{{\<langle>\<langle>0,x\<rangle>,AA`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,AA1`x\<rangle>. x\<in>Y},{\<langle>\<langle>0,x\<rangle>,B`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,B1`x\<rangle>. x\<in>Y}}])\<ra>\<^sub>G({\<langle>k,(AA1`k)\<cdot>\<^sub>M(B1`k)\<rangle>. k\<in>Y}`t)"
    using assms(9) by auto
  ultimately have "(\<Sum>[D;{AA,B}])\<ra>\<^sub>G(\<Sum>[E;{AA1,B1}])=(\<Sum>[D+(E-{t});{{\<langle>\<langle>0,x\<rangle>,AA`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,AA1`x\<rangle>. x\<in>Y},{\<langle>\<langle>0,x\<rangle>,B`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,B1`x\<rangle>. x\<in>Y}}])\<ra>\<^sub>G({\<langle>k,(AA1`k)\<cdot>\<^sub>M(B1`k)\<rangle>. k\<in>Y}`t)" by auto
  moreover have "{\<langle>k,(AA1`k)\<cdot>\<^sub>M(B1`k)\<rangle>. k\<in>Y}`t=(AA1`t)\<cdot>\<^sub>M(B1`t)" using apply_equality[OF _ a1f] assms(7,4) unfolding FinPow_def by auto moreover
  {
    have dA:"domain({\<langle>\<langle>0,x\<rangle>,AA`x\<rangle>. x\<in>X})={\<langle>0,x\<rangle>. x\<in>X}" unfolding domain_def by auto
    have dA1:"domain({\<langle>\<langle>1,x\<rangle>,AA1`x\<rangle>. x\<in>Y})={\<langle>1,x\<rangle>. x\<in>Y}" unfolding domain_def by auto
    have "\<langle>1,t\<rangle>\<notin>domain({\<langle>\<langle>0,x\<rangle>,AA`x\<rangle>. x\<in>X})" by auto
    then have "({\<langle>\<langle>1,x\<rangle>,AA1`x\<rangle>. x\<in>Y}\<union>{\<langle>\<langle>0,x\<rangle>,AA`x\<rangle>. x\<in>X})`\<langle>1,t\<rangle>={\<langle>\<langle>1,x\<rangle>,AA1`x\<rangle>. x\<in>Y}`\<langle>1,t\<rangle>" using fun_disjoint_apply1[of "\<langle>1,t\<rangle>" "{\<langle>\<langle>0,x\<rangle>,AA`x\<rangle>. x\<in>X}"] by auto
    moreover have "{\<langle>\<langle>1,x\<rangle>,AA1`x\<rangle>. x\<in>Y}\<union>{\<langle>\<langle>0,x\<rangle>,AA`x\<rangle>. x\<in>X}={\<langle>\<langle>0,x\<rangle>,AA`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,AA1`x\<rangle>. x\<in>Y}" by auto
    ultimately have "({\<langle>\<langle>0,x\<rangle>,AA`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,AA1`x\<rangle>. x\<in>Y})`\<langle>1,t\<rangle>={\<langle>\<langle>1,x\<rangle>,AA1`x\<rangle>. x\<in>Y}`\<langle>1,t\<rangle>" by auto moreover
    have "{\<langle>\<langle>1,x\<rangle>,AA1`x\<rangle>. x\<in>Y}:{1}\<times>Y\<rightarrow>R" unfolding Pi_def function_def using apply_type[OF assms(5)] by auto
    then have "{\<langle>\<langle>1,x\<rangle>,AA1`x\<rangle>. x\<in>Y}`\<langle>1,t\<rangle>=(AA1`t)" using apply_equality assms(7,4) unfolding FinPow_def by auto
    ultimately have e1:"({\<langle>\<langle>0,x\<rangle>,AA`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,AA1`x\<rangle>. x\<in>Y})`\<langle>1,t\<rangle>=(AA1`t)" by auto
    have dB:"domain({\<langle>\<langle>0,x\<rangle>,B`x\<rangle>. x\<in>X})={\<langle>0,x\<rangle>. x\<in>X}" unfolding domain_def by auto
    have dB1:"domain({\<langle>\<langle>1,x\<rangle>,B1`x\<rangle>. x\<in>Y})={\<langle>1,x\<rangle>. x\<in>Y}" unfolding domain_def by auto
    have "\<langle>1,t\<rangle>\<notin>domain({\<langle>\<langle>0,x\<rangle>,B`x\<rangle>. x\<in>X})" by auto
    then have "({\<langle>\<langle>1,x\<rangle>,B1`x\<rangle>. x\<in>Y}\<union>{\<langle>\<langle>0,x\<rangle>,B`x\<rangle>. x\<in>X})`\<langle>1,t\<rangle>={\<langle>\<langle>1,x\<rangle>,B1`x\<rangle>. x\<in>Y}`\<langle>1,t\<rangle>" using fun_disjoint_apply1[of "\<langle>1,t\<rangle>" "{\<langle>\<langle>0,x\<rangle>,B`x\<rangle>. x\<in>X}"] by auto
    moreover have "{\<langle>\<langle>1,x\<rangle>,B1`x\<rangle>. x\<in>Y}\<union>{\<langle>\<langle>0,x\<rangle>,B`x\<rangle>. x\<in>X}={\<langle>\<langle>0,x\<rangle>,B`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,B1`x\<rangle>. x\<in>Y}" by auto
    ultimately have "({\<langle>\<langle>0,x\<rangle>,B`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,B1`x\<rangle>. x\<in>Y})`\<langle>1,t\<rangle>={\<langle>\<langle>1,x\<rangle>,B1`x\<rangle>. x\<in>Y}`\<langle>1,t\<rangle>" by auto moreover
    have "{\<langle>\<langle>1,x\<rangle>,B1`x\<rangle>. x\<in>Y}:{1}\<times>Y\<rightarrow>G" unfolding Pi_def function_def using apply_type[OF assms(6)] by auto
    then have "{\<langle>\<langle>1,x\<rangle>,B1`x\<rangle>. x\<in>Y}`\<langle>1,t\<rangle>=(B1`t)" using apply_equality assms(7,4) unfolding FinPow_def by auto
    ultimately have e2:"({\<langle>\<langle>0,x\<rangle>,B`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,B1`x\<rangle>. x\<in>Y})`\<langle>1,t\<rangle>=(B1`t)" by auto
    with e1 have "(({\<langle>\<langle>0,x\<rangle>,AA`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,AA1`x\<rangle>. x\<in>Y})`\<langle>1,t\<rangle>)\<cdot>\<^sub>M(({\<langle>\<langle>0,x\<rangle>,B`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,B1`x\<rangle>. x\<in>Y})`\<langle>1,t\<rangle>)=(AA1`t)\<cdot>\<^sub>M(B1`t)" by auto
    moreover have tXY:"\<langle>1,t\<rangle>\<in>X+Y" unfolding sum_def using assms(7,4) unfolding FinPow_def by auto
    {
      fix s w assume as:"\<langle>s,w\<rangle>\<in>{\<langle>s,(({\<langle>\<langle>0,x\<rangle>,AA`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,AA1`x\<rangle>. x\<in>Y})`s)\<cdot>\<^sub>M(({\<langle>\<langle>0,x\<rangle>,B`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,B1`x\<rangle>. x\<in>Y})`s)\<rangle>. s\<in>X+Y}"
      then have s:"s\<in>X+Y" and w:"w=(({\<langle>\<langle>0,x\<rangle>,AA`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,AA1`x\<rangle>. x\<in>Y})`s)\<cdot>\<^sub>M(({\<langle>\<langle>0,x\<rangle>,B`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,B1`x\<rangle>. x\<in>Y})`s)" by auto
      then have ss:"s\<in>{0}\<times>X \<union> {1}\<times>Y" unfolding sum_def by auto
      {
        assume "s\<in>{0}\<times>X"
        then obtain r where r:"r\<in>X" "s=\<langle>0,r\<rangle>" by auto
        with s have a:"\<langle>s,(({\<langle>\<langle>0,x\<rangle>,AA`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,AA1`x\<rangle>. x\<in>Y})`\<langle>0,r\<rangle>)\<cdot>\<^sub>M(({\<langle>\<langle>0,x\<rangle>,B`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,B1`x\<rangle>. x\<in>Y})`\<langle>0,r\<rangle>)\<rangle>\<in>
          {\<langle>s,(({\<langle>\<langle>0,x\<rangle>,AA`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,AA1`x\<rangle>. x\<in>Y})`s)\<cdot>\<^sub>M(({\<langle>\<langle>0,x\<rangle>,B`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,B1`x\<rangle>. x\<in>Y})`s)\<rangle>. s\<in>X+Y}" by auto
        have "({\<langle>\<langle>0,x\<rangle>,AA`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,AA1`x\<rangle>. x\<in>Y})`\<langle>0,r\<rangle>={\<langle>\<langle>0,x\<rangle>,AA`x\<rangle>. x\<in>X}`\<langle>0,r\<rangle>" using fun_disjoint_apply1[of "\<langle>0,r\<rangle>"
          "{\<langle>\<langle>1,x\<rangle>,AA1`x\<rangle>. x\<in>Y}"] by auto
        also have "\<dots>=AA`r" using r(1) apply_equality[of "\<langle>0,r\<rangle>" "AA`r" "{\<langle>\<langle>0,x\<rangle>,AA`x\<rangle>. x\<in>X}" "{0}\<times>X" "\<lambda>p. R"] unfolding Pi_def function_def
          using apply_type[OF assms(1)] by auto
        ultimately have AAr:"({\<langle>\<langle>0,x\<rangle>,AA`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,AA1`x\<rangle>. x\<in>Y})`\<langle>0,r\<rangle>=AA`r" by auto
        with a have a1:"\<langle>s,(AA`r)\<cdot>\<^sub>M(({\<langle>\<langle>0,x\<rangle>,B`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,B1`x\<rangle>. x\<in>Y})`\<langle>0,r\<rangle>)\<rangle>\<in>
          {\<langle>s,(({\<langle>\<langle>0,x\<rangle>,AA`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,AA1`x\<rangle>. x\<in>Y})`s)\<cdot>\<^sub>M(({\<langle>\<langle>0,x\<rangle>,B`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,B1`x\<rangle>. x\<in>Y})`s)\<rangle>. s\<in>X+Y}" by auto
        have "({\<langle>\<langle>0,x\<rangle>,B`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,B1`x\<rangle>. x\<in>Y})`\<langle>0,r\<rangle>={\<langle>\<langle>0,x\<rangle>,B`x\<rangle>. x\<in>X}`\<langle>0,r\<rangle>" using fun_disjoint_apply1[of "\<langle>0,r\<rangle>"
          "{\<langle>\<langle>1,x\<rangle>,B1`x\<rangle>. x\<in>Y}"] by auto
        also have "\<dots>=B`r" using r(1) apply_equality[of "\<langle>0,r\<rangle>" "B`r" "{\<langle>\<langle>0,x\<rangle>,B`x\<rangle>. x\<in>X}" "{0}\<times>X" "\<lambda>p. G"] unfolding Pi_def function_def
          using apply_type[OF assms(2)] by auto
        ultimately have Br:"({\<langle>\<langle>0,x\<rangle>,B`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,B1`x\<rangle>. x\<in>Y})`\<langle>0,r\<rangle>=B`r" by auto
        with a1 have "\<langle>s,(AA`r)\<cdot>\<^sub>M(B`r)\<rangle>\<in>
          {\<langle>s,(({\<langle>\<langle>0,x\<rangle>,AA`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,AA1`x\<rangle>. x\<in>Y})`s)\<cdot>\<^sub>M(({\<langle>\<langle>0,x\<rangle>,B`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,B1`x\<rangle>. x\<in>Y})`s)\<rangle>. s\<in>X+Y}" by auto moreover
        have "(AA`r)\<cdot>\<^sub>M(B`r)\<in>G" using apply_type[OF fun_aux[OF assms(1,2)] r(1)] apply_equality[OF _ fun_aux[OF assms(1,2)]] r(1) by auto
        ultimately have "\<langle>s,(AA`r)\<cdot>\<^sub>M(B`r)\<rangle>\<in>(X+Y)\<times>G" using s by auto moreover
        from w r(2) AAr Br have "w=(AA`r)\<cdot>\<^sub>M(B`r)" by auto
        ultimately have "\<langle>s,w\<rangle>\<in>(X+Y)\<times>G" by auto
      }
      moreover
      {
        assume "s\<notin>{0}\<times>X"
        with ss have "s\<in>{1}\<times>Y" by auto
        then obtain r where r:"r\<in>Y" "s=\<langle>1,r\<rangle>" by auto
        with s have a:"\<langle>s,(({\<langle>\<langle>0,x\<rangle>,AA`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,AA1`x\<rangle>. x\<in>Y})`\<langle>1,r\<rangle>)\<cdot>\<^sub>M(({\<langle>\<langle>0,x\<rangle>,B`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,B1`x\<rangle>. x\<in>Y})`\<langle>1,r\<rangle>)\<rangle>\<in>
          {\<langle>s,(({\<langle>\<langle>0,x\<rangle>,AA`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,AA1`x\<rangle>. x\<in>Y})`s)\<cdot>\<^sub>M(({\<langle>\<langle>0,x\<rangle>,B`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,B1`x\<rangle>. x\<in>Y})`s)\<rangle>. s\<in>X+Y}" by auto
        have "({\<langle>\<langle>0,x\<rangle>,AA`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,AA1`x\<rangle>. x\<in>Y})`\<langle>1,r\<rangle>={\<langle>\<langle>1,x\<rangle>,AA1`x\<rangle>. x\<in>Y}`\<langle>1,r\<rangle>" using fun_disjoint_apply2[of "\<langle>1,r\<rangle>"
          "{\<langle>\<langle>0,x\<rangle>,AA`x\<rangle>. x\<in>X}"] by auto
        also have "\<dots>=AA1`r" using r(1) apply_equality[of "\<langle>1,r\<rangle>" "AA1`r" "{\<langle>\<langle>1,x\<rangle>,AA1`x\<rangle>. x\<in>Y}" "{1}\<times>Y" "\<lambda>p. R"] unfolding Pi_def function_def
          using apply_type[OF assms(5)] by auto
        ultimately have AAr:"({\<langle>\<langle>0,x\<rangle>,AA`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,AA1`x\<rangle>. x\<in>Y})`\<langle>1,r\<rangle>=AA1`r" by auto
        with a have a1:"\<langle>s,(AA1`r)\<cdot>\<^sub>M(({\<langle>\<langle>0,x\<rangle>,B`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,B1`x\<rangle>. x\<in>Y})`\<langle>1,r\<rangle>)\<rangle>\<in>
          {\<langle>s,(({\<langle>\<langle>0,x\<rangle>,AA`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,AA1`x\<rangle>. x\<in>Y})`s)\<cdot>\<^sub>M(({\<langle>\<langle>0,x\<rangle>,B`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,B1`x\<rangle>. x\<in>Y})`s)\<rangle>. s\<in>X+Y}" by auto
        have "({\<langle>\<langle>0,x\<rangle>,B`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,B1`x\<rangle>. x\<in>Y})`\<langle>1,r\<rangle>={\<langle>\<langle>1,x\<rangle>,B1`x\<rangle>. x\<in>Y}`\<langle>1,r\<rangle>" using fun_disjoint_apply2[of "\<langle>1,r\<rangle>"
          "{\<langle>\<langle>0,x\<rangle>,B`x\<rangle>. x\<in>X}"] by auto
        also have "\<dots>=B1`r" using r(1) apply_equality[of "\<langle>1,r\<rangle>" "B1`r" "{\<langle>\<langle>1,x\<rangle>,B1`x\<rangle>. x\<in>Y}" "{1}\<times>Y" "\<lambda>p. G"] unfolding Pi_def function_def
          using apply_type[OF assms(6)] by auto
        ultimately have Br:"({\<langle>\<langle>0,x\<rangle>,B`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,B1`x\<rangle>. x\<in>Y})`\<langle>1,r\<rangle>=B1`r" by auto
        with a1 have "\<langle>s,(AA1`r)\<cdot>\<^sub>M(B1`r)\<rangle>\<in>
          {\<langle>s,(({\<langle>\<langle>0,x\<rangle>,AA`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,AA1`x\<rangle>. x\<in>Y})`s)\<cdot>\<^sub>M(({\<langle>\<langle>0,x\<rangle>,B`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,B1`x\<rangle>. x\<in>Y})`s)\<rangle>. s\<in>X+Y}" by auto moreover
        have "(AA1`r)\<cdot>\<^sub>M(B1`r)\<in>G" using apply_type[OF fun_aux[OF assms(5,6)] r(1)] apply_equality[OF _ fun_aux[OF assms(5,6)]] r(1) by auto
        ultimately have "\<langle>s,(AA1`r)\<cdot>\<^sub>M(B1`r)\<rangle>\<in>(X+Y)\<times>G" using s by auto moreover
        from w r(2) AAr Br have "w=(AA1`r)\<cdot>\<^sub>M(B1`r)" by auto
        ultimately have "\<langle>s,w\<rangle>\<in>(X+Y)\<times>G" by auto
      }
      ultimately have "\<langle>s,w\<rangle>\<in>(X+Y)\<times>G" by auto
    }
    then have "{\<langle>s,(({\<langle>\<langle>0,x\<rangle>,AA`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,AA1`x\<rangle>. x\<in>Y})`s)\<cdot>\<^sub>M(({\<langle>\<langle>0,x\<rangle>,B`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,B1`x\<rangle>. x\<in>Y})`s)\<rangle>. s\<in>X+Y}\<subseteq>(X+Y)\<times>G" by auto
    then have fun:"{\<langle>s,(({\<langle>\<langle>0,x\<rangle>,AA`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,AA1`x\<rangle>. x\<in>Y})`s)\<cdot>\<^sub>M(({\<langle>\<langle>0,x\<rangle>,B`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,B1`x\<rangle>. x\<in>Y})`s)\<rangle>. s\<in>X+Y}:X+Y\<rightarrow>G"
      unfolding Pi_def function_def by auto
    from tXY have pp:"\<langle>\<langle>1,t\<rangle>,(({\<langle>\<langle>0,x\<rangle>,AA`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,AA1`x\<rangle>. x\<in>Y})`\<langle>1,t\<rangle>)\<cdot>\<^sub>M(({\<langle>\<langle>0,x\<rangle>,B`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,B1`x\<rangle>. x\<in>Y})`\<langle>1,t\<rangle>)\<rangle>\<in>
      {\<langle>s,(({\<langle>\<langle>0,x\<rangle>,AA`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,AA1`x\<rangle>. x\<in>Y})`s)\<cdot>\<^sub>M(({\<langle>\<langle>0,x\<rangle>,B`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,B1`x\<rangle>. x\<in>Y})`s)\<rangle>. s\<in>X+Y}" by auto
    have "{\<langle>s,(({\<langle>\<langle>0,x\<rangle>,AA`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,AA1`x\<rangle>. x\<in>Y})`s)\<cdot>\<^sub>M(({\<langle>\<langle>0,x\<rangle>,B`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,B1`x\<rangle>. x\<in>Y})`s)\<rangle>. s\<in>X+Y}`\<langle>1,t\<rangle>=
      (({\<langle>\<langle>0,x\<rangle>,AA`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,AA1`x\<rangle>. x\<in>Y})`\<langle>1,t\<rangle>)\<cdot>\<^sub>M(({\<langle>\<langle>0,x\<rangle>,B`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,B1`x\<rangle>. x\<in>Y})`\<langle>1,t\<rangle>)" using apply_equality[OF pp fun] by auto
    ultimately have "{\<langle>s,(({\<langle>\<langle>0,x\<rangle>,AA`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,AA1`x\<rangle>. x\<in>Y})`s)\<cdot>\<^sub>M(({\<langle>\<langle>0,x\<rangle>,B`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,B1`x\<rangle>. x\<in>Y})`s)\<rangle>. s\<in>X+Y}`\<langle>1,t\<rangle>=(AA1`t)\<cdot>\<^sub>M(B1`t)"
      by auto
  }
  ultimately have "(\<Sum>[D;{AA,B}]) \<ra>\<^sub>G (\<Sum>[E;{AA1,B1}]) =
    (\<Sum>[D+(E-{t});{{\<langle>\<langle>0,x\<rangle>,AA`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,AA1`x\<rangle>. x\<in>Y},{\<langle>\<langle>0,x\<rangle>,B`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,B1`x\<rangle>. x\<in>Y}}]) \<ra>\<^sub>G
    (({\<langle>s, ((({\<langle>\<langle>0, x\<rangle>, AA ` x\<rangle> . x \<in> X} \<union> {\<langle>\<langle>1, x\<rangle>, AA1 ` x\<rangle> . x \<in> Y}) ` s) \<cdot>\<^sub>M (({\<langle>\<langle>0, x\<rangle>, B ` x\<rangle> . x \<in> X} \<union> {\<langle>\<langle>1, x\<rangle>, B1 ` x\<rangle> . x \<in> Y}) ` s))\<rangle> .
     s \<in> X + Y}) ` \<langle>1, t\<rangle>)" by auto moreover
  have "D+(E-{t})=(D+E)-{\<langle>1,t\<rangle>}" unfolding sum_def by auto ultimately
  have A1:"(\<Sum>[D;{AA,B}]) \<ra>\<^sub>G (\<Sum>[E;{AA1,B1}]) =
    (\<Sum>[(D+E)-{\<langle>1,t\<rangle>};{{\<langle>\<langle>0,x\<rangle>,AA`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,AA1`x\<rangle>. x\<in>Y},{\<langle>\<langle>0,x\<rangle>,B`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,B1`x\<rangle>. x\<in>Y}}]) \<ra>\<^sub>G
    (({\<langle>s, ((({\<langle>\<langle>0, x\<rangle>, AA ` x\<rangle> . x \<in> X} \<union> {\<langle>\<langle>1, x\<rangle>, AA1 ` x\<rangle> . x \<in> Y}) ` s) \<cdot>\<^sub>M (({\<langle>\<langle>0, x\<rangle>, B ` x\<rangle> . x \<in> X} \<union> {\<langle>\<langle>1, x\<rangle>, B1 ` x\<rangle> . x \<in> Y}) ` s))\<rangle> .
     s \<in> X + Y}) ` \<langle>1, t\<rangle>)" by auto
  have f1:"{\<langle>\<langle>0, x\<rangle>, AA ` x\<rangle> . x \<in> X}:{0}\<times>X\<rightarrow>R" using apply_type[OF assms(1)] unfolding Pi_def function_def by auto
  have f2:"{\<langle>\<langle>1, x\<rangle>, AA1 ` x\<rangle> . x \<in> Y}:{1}\<times>Y\<rightarrow>R" using apply_type[OF assms(5)] unfolding Pi_def function_def by auto
  have "({0}\<times>X)\<inter>({1}\<times>Y)=0" by auto
  then have ffA:"({\<langle>\<langle>0, x\<rangle>, AA ` x\<rangle> . x \<in> X} \<union> {\<langle>\<langle>1, x\<rangle>, AA1 ` x\<rangle> . x \<in> Y}):X+Y\<rightarrow>R" unfolding sum_def using fun_disjoint_Un[OF f1 f2] by auto 
  have f1:"{\<langle>\<langle>0, x\<rangle>, B ` x\<rangle> . x \<in> X}:{0}\<times>X\<rightarrow>G" using apply_type[OF assms(2)] unfolding Pi_def function_def by auto
  have f2:"{\<langle>\<langle>1, x\<rangle>, B1 ` x\<rangle> . x \<in> Y}:{1}\<times>Y\<rightarrow>G" using apply_type[OF assms(6)] unfolding Pi_def function_def by auto
  have "({0}\<times>X)\<inter>({1}\<times>Y)=0" by auto
  then have ffB:"({\<langle>\<langle>0, x\<rangle>, B ` x\<rangle> . x \<in> X} \<union> {\<langle>\<langle>1, x\<rangle>, B1 ` x\<rangle> . x \<in> Y}):X+Y\<rightarrow>G" unfolding sum_def using fun_disjoint_Un[OF f1 f2] by auto
  have "D+E\<subseteq>X+Y" using assms(3,4) unfolding FinPow_def sum_def by auto moreover
  obtain nd ne where "nd\<in>nat" "D\<approx>nd" "ne\<in>nat" "E\<approx>ne" using assms(3,4) unfolding FinPow_def Finite_def by auto
  then have "D+E\<approx>nd+ne" "nd\<in>nat" "ne\<in>nat" using sum_eqpoll_cong by auto
  then have "D+E\<approx>nd #+ ne" using nat_sum_eqpoll_sum eqpoll_trans by auto
  then have "\<exists>n\<in>nat. D+E\<approx>n" using add_type by auto
  then have "Finite(D+E)" unfolding Finite_def by auto
  ultimately have fin:"D+E\<in>FinPow(X+Y)" unfolding FinPow_def by auto
  from assms(7) have "\<langle>1,t\<rangle>\<in>D+E" unfolding sum_def by auto
  with A1 show ?thesis using sum_one_element[OF ffA ffB fin] by auto
qed

text\<open>The addition of two linear combinations is a linear combination\<close>

theorem(in module0) linComb_sum:
  assumes "AA:X\<rightarrow>R" "AA1:Y\<rightarrow>R" "B:X\<rightarrow>G" "B1:Y\<rightarrow>G" "D\<noteq>0" "D\<in>FinPow(X)" "E\<in>FinPow(Y)"
  shows "(\<Sum>[D;{AA,B}])\<ra>\<^sub>G(\<Sum>[E;{AA1,B1}])=\<Sum>[D+E;{{\<langle>\<langle>0,x\<rangle>,AA`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,AA1`x\<rangle>. x\<in>Y},{\<langle>\<langle>0,x\<rangle>,B`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,B1`x\<rangle>. x\<in>Y}}]"
proof-
  {
    fix \<AA> \<BB> \<AA>1 \<BB>1 assume fun:"\<AA>:X\<rightarrow>R" "\<BB>:X\<rightarrow>G" "\<AA>1:Y\<rightarrow>R" "\<BB>1:Y\<rightarrow>G"
    have "((\<Sum>[D;{\<AA>,\<BB>}]) \<ra>\<^sub>G(\<Sum>[0;{\<AA>1,\<BB>1}])=\<Sum>[D+0;{{\<langle>\<langle>0,x\<rangle>,\<AA>`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,\<AA>1`x\<rangle>. x\<in>Y},{\<langle>\<langle>0,x\<rangle>,\<BB>`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,\<BB>1`x\<rangle>. x\<in>Y}}])" using linComb_sum_base_induct[OF fun(1,2) assms(6) fun(3,4)]
      by auto
  }
  then have base:"\<forall>AA\<in>X \<rightarrow> R.
       \<forall>B\<in>X \<rightarrow> G.
          \<forall>AA1\<in>Y \<rightarrow> R.
             \<forall>B1\<in>Y \<rightarrow> G.
                (\<Sum>[D;{AA,B}]) \<ra>\<^sub>G (\<Sum>[0;{AA1,B1}]) =
                \<Sum>[D + 0;{{\<langle>\<langle>0, x\<rangle>, AA ` x\<rangle> . x \<in> X} \<union> {\<langle>\<langle>1, x\<rangle>, AA1 ` x\<rangle> . x \<in> Y},{\<langle>\<langle>0, x\<rangle>, B ` x\<rangle> . x \<in> X} \<union> {\<langle>\<langle>1, x\<rangle>, B1 ` x\<rangle> . x \<in> Y}}]" by auto
  {
    fix \<RR> assume R:"\<RR>\<in>FinPow(Y)" "\<RR>\<noteq>0"
    then obtain r where r:"r\<in>\<RR>" by auto
    {
      fix \<AA> \<BB> \<AA>1 \<BB>1 assume fun:"\<AA>:X\<rightarrow>R" "\<BB>:X\<rightarrow>G" "\<AA>1:Y\<rightarrow>R" "\<BB>1:Y\<rightarrow>G" and 
        step:"\<forall>AA\<in>X\<rightarrow>R. \<forall>B\<in>X\<rightarrow>G. \<forall>AA1\<in>Y\<rightarrow>R. \<forall>B1\<in>Y\<rightarrow>G. (\<Sum>[D;{AA,B}]) \<ra>\<^sub>G (\<Sum>[\<RR> - {r};{AA1,B1}])=(\<Sum>[D+(\<RR> - {r});{{\<langle>\<langle>0, x\<rangle>, AA ` x\<rangle> . x \<in> X} \<union> {\<langle>\<langle>1, x\<rangle>, AA1 ` x\<rangle> . x \<in> Y},{\<langle>\<langle>0, x\<rangle>, B ` x\<rangle> . x \<in> X} \<union> {\<langle>\<langle>1, x\<rangle>, B1 ` x\<rangle> . x \<in> Y}}])"
      then have "(\<Sum>[D;{\<AA>,\<BB>}]) \<ra>\<^sub>G (\<Sum>[\<RR>;{\<AA>1,\<BB>1}])=(\<Sum>[D+\<RR>;{{\<langle>\<langle>0, x\<rangle>, \<AA> ` x\<rangle> . x \<in> X} \<union> {\<langle>\<langle>1, x\<rangle>, \<AA>1 ` x\<rangle> . x \<in> Y},{\<langle>\<langle>0, x\<rangle>, \<BB> ` x\<rangle> . x \<in> X} \<union> {\<langle>\<langle>1, x\<rangle>, \<BB>1 ` x\<rangle> . x \<in> Y}}])" using linComb_sum_ind_step[OF fun(1,2) assms(6) R(1) fun(3,4) r assms(5)]
        by auto
    }
    then have "(\<forall>AA\<in>X\<rightarrow>R. \<forall>B\<in>X\<rightarrow>G. \<forall>AA1\<in>Y\<rightarrow>R. \<forall>B1\<in>Y\<rightarrow>G. (\<Sum>[D;{AA,B}]) \<ra>\<^sub>G (\<Sum>[\<RR> - {r};{AA1,B1}])=(\<Sum>[D+(\<RR> - {r});{{\<langle>\<langle>0, x\<rangle>, AA ` x\<rangle> . x \<in> X} \<union> {\<langle>\<langle>1, x\<rangle>, AA1 ` x\<rangle> . x \<in> Y},{\<langle>\<langle>0, x\<rangle>, B ` x\<rangle> . x \<in> X} \<union> {\<langle>\<langle>1, x\<rangle>, B1 ` x\<rangle> . x \<in> Y}}])) \<longrightarrow> 
      (\<forall>AA\<in>X\<rightarrow>R. \<forall>B\<in>X\<rightarrow>G. \<forall>AA1\<in>Y\<rightarrow>R. \<forall>B1\<in>Y\<rightarrow>G. ((\<Sum>[D;{AA,B}]) \<ra>\<^sub>G(\<Sum>[\<RR>;{AA1,B1}])=\<Sum>[D+\<RR>;{{\<langle>\<langle>0,x\<rangle>,AA`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,AA1`x\<rangle>. x\<in>Y},{\<langle>\<langle>0,x\<rangle>,B`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,B1`x\<rangle>. x\<in>Y}}]))" by auto
    then have "\<exists>r\<in>\<RR>. (\<forall>AA\<in>X\<rightarrow>R. \<forall>B\<in>X\<rightarrow>G. \<forall>AA1\<in>Y\<rightarrow>R. \<forall>B1\<in>Y\<rightarrow>G. (\<Sum>[D;{AA,B}]) \<ra>\<^sub>G (\<Sum>[\<RR> - {r};{AA1,B1}])=(\<Sum>[D+(\<RR> - {r});{{\<langle>\<langle>0, x\<rangle>, AA ` x\<rangle> . x \<in> X} \<union> {\<langle>\<langle>1, x\<rangle>, AA1 ` x\<rangle> . x \<in> Y},{\<langle>\<langle>0, x\<rangle>, B ` x\<rangle> . x \<in> X} \<union> {\<langle>\<langle>1, x\<rangle>, B1 ` x\<rangle> . x \<in> Y}}])) \<longrightarrow> 
      (\<forall>AA\<in>X\<rightarrow>R. \<forall>B\<in>X\<rightarrow>G. \<forall>AA1\<in>Y\<rightarrow>R. \<forall>B1\<in>Y\<rightarrow>G. ((\<Sum>[D;{AA,B}]) \<ra>\<^sub>G(\<Sum>[\<RR>;{AA1,B1}])=\<Sum>[D+\<RR>;{{\<langle>\<langle>0,x\<rangle>,AA`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,AA1`x\<rangle>. x\<in>Y},{\<langle>\<langle>0,x\<rangle>,B`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,B1`x\<rangle>. x\<in>Y}}]))" using r by auto
  }
  then have indstep:"\<forall>\<RR>\<in>FinPow(Y). \<RR>\<noteq>0 \<longrightarrow> (\<exists>r\<in>\<RR>. (\<forall>AA\<in>X\<rightarrow>R. \<forall>B\<in>X\<rightarrow>G. \<forall>AA1\<in>Y\<rightarrow>R. \<forall>B1\<in>Y\<rightarrow>G. (\<Sum>[D;{AA,B}]) \<ra>\<^sub>G (\<Sum>[\<RR> - {r};{AA1,B1}])=(\<Sum>[D+(\<RR> - {r});{{\<langle>\<langle>0, x\<rangle>, AA ` x\<rangle> . x \<in> X} \<union> {\<langle>\<langle>1, x\<rangle>, AA1 ` x\<rangle> . x \<in> Y},{\<langle>\<langle>0, x\<rangle>, B ` x\<rangle> . x \<in> X} \<union> {\<langle>\<langle>1, x\<rangle>, B1 ` x\<rangle> . x \<in> Y}}])) \<longrightarrow> 
    (\<forall>AA\<in>X\<rightarrow>R. \<forall>B\<in>X\<rightarrow>G. \<forall>AA1\<in>Y\<rightarrow>R. \<forall>B1\<in>Y\<rightarrow>G. ((\<Sum>[D;{AA,B}]) \<ra>\<^sub>G(\<Sum>[\<RR>;{AA1,B1}])=\<Sum>[D+\<RR>;{{\<langle>\<langle>0,x\<rangle>,AA`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,AA1`x\<rangle>. x\<in>Y},{\<langle>\<langle>0,x\<rangle>,B`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,B1`x\<rangle>. x\<in>Y}}])))" by auto
  have "\<forall>AA\<in>X\<rightarrow>R. \<forall>B\<in>X\<rightarrow>G. \<forall>AA1\<in>Y\<rightarrow>R. \<forall>B1\<in>Y\<rightarrow>G. ((\<Sum>[D;{AA,B}]) \<ra>\<^sub>G(\<Sum>[E;{AA1,B1}])=\<Sum>[D+E;{{\<langle>\<langle>0,x\<rangle>,AA`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,AA1`x\<rangle>. x\<in>Y},{\<langle>\<langle>0,x\<rangle>,B`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,B1`x\<rangle>. x\<in>Y}}])" 
    using FinPow_ind_rem_one[where P="\<lambda>E. (\<forall>AA\<in>X\<rightarrow>R. \<forall>B\<in>X\<rightarrow>G. \<forall>AA1\<in>Y\<rightarrow>R. \<forall>B1\<in>Y\<rightarrow>G. ((\<Sum>[D;{AA,B}]) \<ra>\<^sub>G(\<Sum>[E;{AA1,B1}])=\<Sum>[D+E;{{\<langle>\<langle>0,x\<rangle>,AA`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,AA1`x\<rangle>. x\<in>Y},{\<langle>\<langle>0,x\<rangle>,B`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,B1`x\<rangle>. x\<in>Y}}]))",
    OF base indstep assms(7)].
  with assms(1-4) show ?thesis by auto
qed

subsection\<open>Linear depen\<close>

text \<open>Now, we have the conditions to define what linear independence means:\<close>

definition(in module0)
  LinInde ("_{is linearly independent}" 89)
  where "T\<subseteq>G \<Longrightarrow> T{is linearly independent} \<equiv> (\<forall>X\<in>nat. \<forall>AA\<in>X\<rightarrow>R. \<forall>B\<in>inj(X,T). ((\<Sum>[X;{AA,B}] = \<zero>\<^sub>G ) ) \<longrightarrow> (\<forall>m\<in>X. AA`m=\<zero>\<^sub>R))"

text\<open>If a set has the zero element, then it is not linearly independent.\<close>

theorem(in module0) zero_set_dependent:
  assumes "\<zero>\<^sub>G\<in>T" "T\<subseteq>G" "R\<noteq>{\<zero>\<^sub>R}"
  shows "\<not>(T{is linearly independent})"
proof
  assume "T{is linearly independent}"
  then have reg:"\<forall>n\<in>nat. \<forall>AA\<in>n\<rightarrow>R. \<forall>B\<in>inj(n,T).(\<Sum>[n;{AA,B}] =\<zero>\<^sub>G ) \<longrightarrow> (\<forall>m\<in>n. AA`m=\<zero>\<^sub>R)"
    unfolding LinInde_def[OF assms(2)] by auto
  from assms(3) obtain r where r:"r\<in>R" "r\<noteq>\<zero>\<^sub>R" using ring.Ring_ZF_1_L2(1) by auto
  let ?A="{\<langle>0,r\<rangle>}"
  let ?B="{\<langle>0,\<zero>\<^sub>G\<rangle>}"
  have A:"?A:succ(0)\<rightarrow>R" using `r\<in>R` unfolding Pi_def function_def domain_def by auto
  have B:"?B:succ(0)\<rightarrow>T" using assms(1) unfolding Pi_def function_def domain_def by auto
  with assms(2) have B2:"?B:succ(0)\<rightarrow>G" unfolding Pi_def by auto
  have C:"succ(0)\<in>nat" by auto
  have fff:"{\<langle>m, ?A ` m \<cdot>\<^sub>M (?B ` m)\<rangle> . m \<in> 1}:1\<rightarrow>G" using fun_aux[OF A B2] by auto
  have "?B\<in>inj(succ(0),T)" unfolding inj_def using apply_equality B by auto
  with A C reg have "\<Sum>[succ(0);{?A,?B}] =\<zero>\<^sub>G \<longrightarrow> (\<forall>m\<in>succ(0). ?A`m=\<zero>\<^sub>R)" by blast
  then have "\<Sum>[succ(0);{?A,?B}] =\<zero>\<^sub>G \<longrightarrow> (?A`0=\<zero>\<^sub>R)" by blast
  then have "\<Sum>[succ(0);{?A,?B}] =\<zero>\<^sub>G \<longrightarrow> (r=\<zero>\<^sub>R)" using apply_equality[OF _ A,of 0 r] by auto
  with r(2) have "\<Sum>[succ(0);{?A,?B}] \<noteq>\<zero>\<^sub>G" by auto
  moreover have "\<Sum>[succ(0);{?A,?B}]=?A`0 \<cdot>\<^sub>M (?B ` 0)" using linComb_one_element[OF _ A B2] unfolding succ_def by auto
  also have "\<dots>=r\<cdot>\<^sub>M\<zero>\<^sub>G" using apply_equality A B by auto
  also have "\<dots>=\<zero>\<^sub>G" using mult_zeroG r(1) by auto
  ultimately show False by auto
qed
  
section\<open>Submodule\<close>

text\<open>A submodule is a subgroup that is invariant by the action\<close>

definition(in module0)
  IsAsubmodule
  where "IsAsubmodule(H) \<equiv> (\<forall>r\<in>R. \<forall>h\<in>H. r\<cdot>\<^sub>M h\<in>H) \<and> IsAsubgroup(H,f)"

lemma(in module0) sumodule_is_subgroup:
  assumes "IsAsubmodule(H)"
  shows "IsAsubgroup(H,f)"
  using assms unfolding IsAsubmodule_def by auto

lemma(in module0) sumodule_is_subaction:
  assumes "IsAsubmodule(H)" "r\<in>R" "h\<in>H"
  shows "r\<cdot>\<^sub>M h\<in>H"
  using assms unfolding IsAsubmodule_def by auto

text\<open>For groups, we need to prove that the inverse function
is closed in a set to prove that set to be a subgroup. In module, that is not necessary.\<close>

lemma(in module0) inverse_in_set:
  assumes "\<forall>r\<in>R. \<forall>h\<in>H. r\<cdot>\<^sub>M h\<in>H" "H\<subseteq>G"
  shows "\<forall>h\<in>H. (\<rm>\<^sub>Gh)\<in>H"
proof
  fix h assume "h\<in>H" moreover
  then have "h\<in>G" using assms(2) by auto
  then have "(\<rm>\<^sub>R\<one>\<^sub>R)\<cdot>\<^sub>M h=(\<rm>\<^sub>Gh)" using inv_module by auto moreover
  have "(\<rm>\<^sub>R\<one>\<^sub>R)\<in>R" using ring.Ring_ZF_1_L2(2) ring.Ring_ZF_1_L3(1) by auto ultimately
  show "(\<rm>\<^sub>Gh)\<in>H" using assms(1) by force
qed

corollary(in module0) submoduleI:
  assumes "H\<subseteq>G" "H\<noteq>0" "H{is closed under}f"  "\<forall>r\<in>R. \<forall>h\<in>H. r\<cdot>\<^sub>M h\<in>H"
  shows "IsAsubmodule(H)" unfolding IsAsubmodule_def
  using inverse_in_set[OF assms(4,1)] assms ab_group.group0_3_T3
    by auto

text\<open>Every module has at least two submodules: the whole module and the trivial module.\<close>

corollary(in module0) trivial_submodules:
  shows "IsAsubmodule(G)" and "IsAsubmodule({\<zero>\<^sub>G})"
  unfolding IsAsubmodule_def
proof(safe)
  have "f:G\<times>G\<rightarrow>G" using ab_group.group_oper_fun by auto
  then have "f\<subseteq>((G\<times>G)\<times>G)" unfolding Pi_def by auto
  then have "restrict(f,G\<times>G)=f" unfolding restrict_def by blast
  then show "IsAsubgroup(G,f)" using Ggroup unfolding IsAsubgroup_def by auto
next
  fix r h assume A:"r\<in>R" "h\<in>G"
  from A(1) have "S`r:G\<rightarrow>G" using S_fun apply_type[of S R "\<lambda>t. End(G,f)"] unfolding End_def by auto
  with A(2) show "r\<cdot>\<^sub>Mh\<in>G" using apply_type[of "S`r" G "\<lambda>t. G"] by auto
next
  fix r assume "r\<in>R"
  with mult_zeroG show "r \<cdot>\<^sub>M \<zero>\<^sub>G = \<zero>\<^sub>G" by auto
next
  have "{\<zero>\<^sub>G}\<noteq>0" by auto moreover
  have "{\<zero>\<^sub>G}\<subseteq>G" using ab_group.group0_2_L2 by auto moreover
  {
    fix x y assume "x\<in>{\<zero>\<^sub>G}" "y\<in>{\<zero>\<^sub>G}"
    then have "f`\<langle>x,y\<rangle>=\<zero>\<^sub>G" using ab_group.group0_2_L2 by auto
  }
  then have "{\<zero>\<^sub>G}{is closed under}f" unfolding IsOpClosed_def by auto moreover
  {
    fix x assume "x\<in>{\<zero>\<^sub>G}"
    then have "GroupInv(G, f) `(x)= \<zero>\<^sub>G" using ab_group.group_inv_of_one by auto
  }
  then have "\<forall>x\<in>{\<zero>\<^sub>G}. GroupInv(G, f) `(x)\<in>{\<zero>\<^sub>G}" by auto ultimately
  show "IsAsubgroup({\<zero>\<^sub>G},f)" using ab_group.group0_3_T3 by auto
qed 


text\<open>An auxiliary lemma.\<close>

lemma(in module0) action_submodule:
  assumes "IsAsubmodule(H)"
  shows "{\<langle>r,restrict(S`r,H)\<rangle>. r\<in>R}:R\<rightarrow>End(H,restrict(f,H\<times>H))"
proof-
  have sub:"H\<subseteq>G" using ab_group.group0_3_L2[OF sumodule_is_subgroup[OF assms]] by auto
  {
    fix t assume "t\<in>{\<langle>r,restrict(S`r,H)\<rangle>. r\<in>R}"
    then obtain r where t:"r\<in>R" "t=\<langle>r,restrict(S`r,H)\<rangle>" by auto
    then have E:"S`r\<in>End(G,f)" using S_fun apply_type by auto
    then have "S`r:G\<rightarrow>G" unfolding End_def by auto
    then have "restrict(S`r,H):H\<rightarrow>G" using restrict_fun sub by auto moreover
    have "\<forall>h\<in>H. restrict(S`r,H)`h\<in>H" using restrict sumodule_is_subaction[OF assms `r\<in>R`] by auto
    ultimately have HH:"restrict(S`r,H):H\<rightarrow>H" using func1_1_L1A by auto
    {
      fix g1 g2 assume H:"g1\<in>H""g2\<in>H"
      with sub have G:"g1\<in>G""g2\<in>G" by auto
      from H have AA:"f`\<langle>g1,g2\<rangle>=restrict(f,H\<times>H)`\<langle>g1,g2\<rangle>" using restrict by auto
      then have "(S`r)`(f`\<langle>g1,g2\<rangle>)=(S`r)`(restrict(f,H\<times>H)`\<langle>g1,g2\<rangle>)" by auto
      then have "f`\<langle>(S`r)`g1,(S`r)`g2\<rangle>=(S`r)`(restrict(f,H\<times>H)`\<langle>g1,g2\<rangle>)" using E G
        unfolding End_def Homomor_def[OF Ggroup Ggroup] by auto
      with H have "restrict(f,H\<times>H)`\<langle>(S`r)`g1,(S`r)`g2\<rangle>=(S`r)`(restrict(f,H\<times>H)`\<langle>g1,g2\<rangle>)" using sumodule_is_subaction[OF assms `r\<in>R`]
        by auto moreover
      from H have "f`\<langle>g1,g2\<rangle>\<in>H" using sumodule_is_subgroup[OF assms] ab_group.group0_3_L6 by auto
      then have "restrict(S`r,H)`(f`\<langle>g1,g2\<rangle>)=(S`r)`(f`\<langle>g1,g2\<rangle>)" by auto
      with AA have "restrict(S`r,H)`(restrict(f,H\<times>H)`\<langle>g1,g2\<rangle>)=(S`r)`(restrict(f,H\<times>H)`\<langle>g1,g2\<rangle>)" by auto moreover
      from H have "(S`r)`g1=restrict(S`r,H)`g1""(S`r)`g2=restrict(S`r,H)`g2" by auto ultimately
      have "restrict(f,H\<times>H)`\<langle>restrict(S`r,H)`g1,restrict(S`r,H)`g2\<rangle>=restrict(S`r,H)`(restrict(f,H\<times>H)`\<langle>g1,g2\<rangle>)" by auto
    }
    then have "\<forall>g1\<in>H. \<forall>g2\<in>H. restrict(f,H\<times>H)`\<langle>restrict(S`r,H)`g1,restrict(S`r,H)`g2\<rangle>=restrict(S`r,H)`(restrict(f,H\<times>H)`\<langle>g1,g2\<rangle>)" by auto
    then have "Homomor(restrict(S`r,H),H,restrict(f,H\<times>H),H,restrict(f,H\<times>H))" using Homomor_def sumodule_is_subgroup[OF assms]
      unfolding IsAsubgroup_def by auto
    with HH have "restrict(S`r,H)\<in>End(H,restrict(f,H\<times>H))" unfolding End_def by auto
    then have "t\<in>R\<times>End(H,restrict(f,H\<times>H))" using t by auto
  }
  then have "{\<langle>r,restrict(S`r,H)\<rangle>. r\<in>R}\<subseteq>R\<times>End(H,restrict(f,H\<times>H))" by auto moreover
  {
    fix x y assume "\<langle>x,y\<rangle>\<in>{\<langle>r,restrict(S`r,H)\<rangle>. r\<in>R}"
    then have y:"x\<in>R""y=restrict(S`x,H)" by auto
    {
      fix y' assume "\<langle>x,y'\<rangle>\<in>{\<langle>r,restrict(S`r,H)\<rangle>. r\<in>R}"
      then have "y'=restrict(S`x,H)" by auto
      with y(2) have "y=y'" by auto
    }
    then have "\<forall>y'. \<langle>x,y'\<rangle>\<in>{\<langle>r,restrict(S`r,H)\<rangle>. r\<in>R} \<longrightarrow> y=y'" by auto
  }
  then have "\<forall>x y. \<langle>x,y\<rangle>\<in>{\<langle>r,restrict(S`r,H)\<rangle>. r\<in>R} \<longrightarrow> (\<forall>y'. \<langle>x,y'\<rangle>\<in>{\<langle>r,restrict(S`r,H)\<rangle>. r\<in>R} \<longrightarrow> y=y')" by auto
  moreover
  have "domain({\<langle>r,restrict(S`r,H)\<rangle>. r\<in>R})\<subseteq>R" unfolding domain_def by auto
  ultimately show fun:"{\<langle>r,restrict(S`r,H)\<rangle>. r\<in>R}:R\<rightarrow>End(H,restrict(f,H\<times>H))" unfolding Pi_def function_def by auto
qed

text\<open>A submodule is a module with the restricted operation.\<close>

lemma(in module0) submodule: 
  assumes "IsAsubmodule(H)"
  shows "IsAmodule(R,A,M,H,restrict(f,H\<times>H),{\<langle>r,restrict(S`r,H)\<rangle>. r\<in>R})"
  unfolding IsAmodule_def
proof(safe)
  show "IsAring(R, A, M)" using ringAssum by auto
  show "IsAgroup(H, restrict(f, H \<times> H))" using sumodule_is_subgroup assms unfolding IsAsubgroup_def
    by auto
  have sub:"H\<subseteq>G" using ab_group.group0_3_L2[OF sumodule_is_subgroup[OF assms]] by auto
  then show "restrict(f, H \<times> H) {is commutative on} H" using Gabelian
    using func_ZF_4_L1[OF ab_group.group_oper_fun] by auto
  show fun:"{\<langle>r,restrict(S`r,H)\<rangle>. r\<in>R}:R\<rightarrow>End(H,restrict(f,H\<times>H))" using action_submodule assms by auto
  then have "{\<langle>r,restrict(S`r,H)\<rangle>. r\<in>R}`\<one>\<^sub>R=restrict(S`\<one>\<^sub>R,H)" using apply_equality ring.Ring_ZF_1_L2(2)
    by auto
  with S_one have "{\<langle>r,restrict(S`r,H)\<rangle>. r\<in>R}`\<one>\<^sub>R=restrict(id(G),H)" by auto moreover
  moreover have "\<forall>h\<in>H. restrict(id(G),H)`h=id(G)`h" using restrict by auto
  with sub have "\<forall>h\<in>H. restrict(id(G),H)`h=h" by auto
  then have "restrict(id(G),H)=id(H)" using fun_extension[OF id_type restrict_fun[OF id_type]] sub by auto
  ultimately have "{\<langle>r,restrict(S`r,H)\<rangle>. r\<in>R}`\<one>\<^sub>R=id(H)" by auto
  also have "\<dots>=TheNeutralElement(End(H, restrict(f, H \<times> H)), restrict(Composition(H), End(H, restrict(f, H \<times> H)) \<times> End(H, restrict(f, H \<times> H))))" 
    using group0.end_comp_monoid(2) sumodule_is_subgroup[OF assms] unfolding group0_def IsAsubgroup_def
    by auto
  ultimately show "{\<langle>r,restrict(S`r,H)\<rangle>. r\<in>R}`TheNeutralElement(R, M)=TheNeutralElement(End(H, restrict(f, H \<times> H)), restrict(Composition(H), End(H, restrict(f, H \<times> H)) \<times> End(H, restrict(f, H \<times> H))))"
    by auto
  have GRA:"IsAgroup(R,A)" using ringAssum unfolding IsAring_def by auto
  have GEndG:"IsAgroup(End(G,f),restrict(f {lifted to function space over} G, End(G, f) \<times> End(G, f)))" using assms ab_group.end_addition_group(1) by auto
  have GH:"group0(H,restrict(f,H \<times> H))" using sumodule_is_subgroup[OF assms] unfolding IsAsubgroup_def group0_def. 
  have ss:"restrict(f {lifted to function space over} G, End(G, f) \<times> End(G, f))=restrict(f {lifted to function space over} G, End(G, f) \<times> End(G, f))" by auto
  fix r s assume AS:"r\<in>R""s\<in>R"
  then have "restrict(S ` r, H)\<in>End(H,restrict(f,H \<times> H))""restrict(S ` s, H)\<in>End(H,restrict(f,H \<times> H))" using apply_type[OF fun]
    apply_equality[OF _ fun] by auto
  then have funf:"restrict(S ` r, H):H\<rightarrow>H""restrict(S ` s, H):H\<rightarrow>H" unfolding End_def by auto
  from AS have rs:"r\<ra>\<^sub>Rs\<in>R""r\<cdot>\<^sub>Rs\<in>R" using ring.Ring_ZF_1_L4(1,3) by auto
  then have EE:"{\<langle>r, restrict(S ` r, H)\<rangle> . r \<in> R} ` (r\<ra>\<^sub>Rs)=restrict(S ` (r\<ra>\<^sub>Rs), H)" using apply_equality fun by auto
  have f1:"{\<langle>r, restrict(S ` r, H)\<rangle> . r \<in> R} ` (r\<ra>\<^sub>Rs):H\<rightarrow>H" using apply_type[OF fun rs(1)] unfolding End_def by auto
  have mH:"monoid0(H,restrict(f,H \<times> H))" using GH unfolding group0_def IsAgroup_def monoid0_def by auto
  have f2:"(restrict(f, H \<times> H) {lifted to function space over} H) `
          \<langle>{\<langle>r, restrict(S ` r, H)\<rangle> . r \<in> R} ` r, {\<langle>r, restrict(S ` r, H)\<rangle> . r \<in> R} ` s\<rangle>:H\<rightarrow>H" using monoid0.Group_ZF_2_1_L0[OF mH _ funf]
          AS apply_equality[OF _ fun] by auto
  {
    fix g assume gh:"g\<in>H"
    have "((restrict(f, H \<times> H) {lifted to function space over} H) `
          \<langle>{\<langle>r, restrict(S ` r, H)\<rangle> . r \<in> R} ` r, {\<langle>r, restrict(S ` r, H)\<rangle> . r \<in> R} ` s\<rangle>)`g=((restrict(f, H \<times> H) {lifted to function space over} H) `
          \<langle>restrict(S ` r, H), restrict(S ` s, H)\<rangle>)`g" using apply_equality[OF _ fun] AS by auto
    also have "\<dots>=restrict(f,H \<times> H)`\<langle>restrict(S ` r, H)`g, restrict(S ` s, H)`g\<rangle>" using group0.Group_ZF_2_1_L3[OF GH _ funf gh]
      by auto
    also have "\<dots>=f`\<langle>restrict(S ` r, H)`g, restrict(S ` s, H)`g\<rangle>" using apply_type[OF funf(1) gh] apply_type[OF funf(2) gh]
      by auto
    also have "\<dots>=f`\<langle>(S ` r)`g, (S ` s)`g\<rangle>" using gh by auto
    also have "\<dots>=(S`(r\<ra>\<^sub>Rs))`g" using S_dist1 AS gh sub by auto
    also have "\<dots>=restrict(S`(r\<ra>\<^sub>Rs),H)`g" using gh by auto  
    also have "\<dots>=({\<langle>r, restrict(S ` r, H)\<rangle> . r \<in> R} ` (r\<ra>\<^sub>Rs))`g" using EE by auto
    ultimately have "((restrict(f, H \<times> H) {lifted to function space over} H) `
          \<langle>{\<langle>r, restrict(S ` r, H)\<rangle> . r \<in> R} ` r, {\<langle>r, restrict(S ` r, H)\<rangle> . r \<in> R} ` s\<rangle>)`g=({\<langle>r, restrict(S ` r, H)\<rangle> . r \<in> R} ` (r\<ra>\<^sub>Rs))`g" by auto
  }
  then have "\<forall>g\<in>H. ((restrict(f, H \<times> H) {lifted to function space over} H) `
          \<langle>{\<langle>r, restrict(S ` r, H)\<rangle> . r \<in> R} ` r, {\<langle>r, restrict(S ` r, H)\<rangle> . r \<in> R} ` s\<rangle>)`g=({\<langle>r, restrict(S ` r, H)\<rangle> . r \<in> R} ` (r\<ra>\<^sub>Rs))`g" by auto
  then show "{\<langle>r, restrict(S ` r, H)\<rangle> . r \<in> R} ` (A ` \<langle>r, s\<rangle>) =
          (restrict(f, H \<times> H) {lifted to function space over} H) `
          \<langle>{\<langle>r, restrict(S ` r, H)\<rangle> . r \<in> R} ` r, {\<langle>r, restrict(S ` r, H)\<rangle> . r \<in> R} ` s\<rangle>" using fun_extension[OF f1 f2] by auto
  have f1:"({\<langle>r, restrict(S ` r, H)\<rangle> . r \<in> R} `(r\<cdot>\<^sub>Rs)):H\<rightarrow>H" using apply_type[OF fun rs(2)] unfolding End_def by auto
  have ff1:"{\<langle>r, restrict(S ` r, H)\<rangle> . r \<in> R} ` r:H\<rightarrow>H""{\<langle>r, restrict(S ` r, H)\<rangle> . r \<in> R} ` s:H\<rightarrow>H" using apply_type[OF fun] AS unfolding End_def by auto
  then have "({\<langle>r, restrict(S ` r, H)\<rangle> . r \<in> R} ` r)O({\<langle>r, restrict(S ` r, H)\<rangle> . r \<in> R} ` s):H\<rightarrow>H" using comp_fun by auto
  then have f2:"(Composition(H) ` \<langle>{\<langle>r, restrict(S ` r, H)\<rangle> . r \<in> R} ` r, {\<langle>r, restrict(S ` r, H)\<rangle> . r \<in> R} ` s\<rangle>):H\<rightarrow>H" using func_ZF_5_L2
    [OF ff1] by auto
  {
    fix g assume gh:"g\<in>H"
    have "(Composition(H) ` \<langle>{\<langle>r, restrict(S ` r, H)\<rangle> . r \<in> R} ` r, {\<langle>r, restrict(S ` r, H)\<rangle> . r \<in> R} ` s\<rangle>)`g=
      (Composition(H) ` \<langle>restrict(S ` r, H), restrict(S ` s, H)\<rangle>)`g" using apply_equality[OF _ fun] AS by auto
    also have "\<dots>=(restrict(S ` r, H)O restrict(S ` s, H))`g" using func_ZF_5_L2[OF funf] by auto
    also have "\<dots>=restrict(S ` r, H)`( restrict(S ` s, H)`g)" using comp_fun_apply[OF funf(2) gh] by auto
    also have "\<dots>=(S ` r)`((S ` s)`g)" using gh apply_type[OF funf(2) gh] by auto
    also have "\<dots>=(S`(r\<cdot>\<^sub>Rs))`g" using S_dist2 gh sub AS by auto
    also have "\<dots>=restrict(S ` (r\<cdot>\<^sub>Rs), H)`g" using gh by auto
    also have "\<dots>=({\<langle>r, restrict(S ` r, H)\<rangle> . r \<in> R} `(r\<cdot>\<^sub>Rs))`g" using apply_equality[OF _ fun] rs(2) by auto
    ultimately have "({\<langle>r, restrict(S ` r, H)\<rangle> . r \<in> R} `(r\<cdot>\<^sub>Rs))`g =(Composition(H) ` \<langle>{\<langle>r, restrict(S ` r, H)\<rangle> . r \<in> R} ` r, {\<langle>r, restrict(S ` r, H)\<rangle> . r \<in> R} ` s\<rangle>)`g"
      by auto
  }
  then have "\<forall>g\<in>H. ({\<langle>r, restrict(S ` r, H)\<rangle> . r \<in> R} `(r\<cdot>\<^sub>Rs))`g =(Composition(H) ` \<langle>{\<langle>r, restrict(S ` r, H)\<rangle> . r \<in> R} ` r, {\<langle>r, restrict(S ` r, H)\<rangle> . r \<in> R} ` s\<rangle>)`g" by auto
  then show "{\<langle>r, restrict(S ` r, H)\<rangle> . r \<in> R} ` (M ` \<langle>r, s\<rangle>) =
          Composition(H) ` \<langle>{\<langle>r, restrict(S ` r, H)\<rangle> . r \<in> R} ` r, {\<langle>r, restrict(S ` r, H)\<rangle> . r \<in> R} ` s\<rangle>" using fun_extension[OF f1 f2] by auto
qed


text\<open>Being a submodule is a transitive relation.\<close>

lemma(in module0) submodule_of_submodule:
  assumes "IsAsubmodule(H)" "module0.IsAsubmodule(R,restrict(f,H\<times>H),{\<langle>r,restrict(S`r,H)\<rangle>. r\<in>R},K)"
  shows "IsAsubmodule(K)" unfolding IsAsubmodule_def
proof
  have mod0:"module0(R,A,M,H,restrict(f,H\<times>H),{\<langle>r,restrict(S`r,H)\<rangle>. r\<in>R})" using submodule[OF assms(1)] isAmodule_imp_module0 by auto
  then have "group0(H,restrict(f,H\<times>H))" unfolding module0_def IsAsubgroup_def group0_def by auto
  then have sub:"K\<subseteq>H" using group0.group0_3_L2 module0.sumodule_is_subgroup[OF mod0 assms(2)] by auto
  {
    fix r h assume A:"r\<in>R" "h\<in>K"
    then have "({\<langle>r, restrict(S ` r, H)\<rangle> . r \<in> R}`r)` h \<in> K" using module0.sumodule_is_subaction[OF mod0] assms(2) by auto moreover
    with A(1) have "restrict(S ` r, H)` h\<in> K" using apply_equality[OF _ action_submodule[OF assms(1)], of r] by auto
    with sub A(2) have "(S ` r)`h\<in> K" using restrict by auto
    then have "r\<cdot>\<^sub>Mh\<in> K" by auto
  }
  then show "\<forall>r\<in>R. \<forall>h\<in>K. r \<cdot>\<^sub>M h \<in> K" by auto
  from restrict_restrict have "restrict(restrict(f,H\<times>H),K\<times>K) =restrict(f,(H\<times>H)\<inter>(K\<times>K))" by auto moreover
  from sub have "(H\<times>H)\<inter>(K\<times>K) =(K\<times>K)" by auto
  ultimately have "restrict(restrict(f,H\<times>H),K\<times>K) =restrict(f,K\<times>K)" by auto
  with module0.sumodule_is_subgroup[OF mod0 assms(2)] show "IsAsubgroup(K,f)" unfolding IsAsubgroup_def by auto
qed

text\<open>If we consider linear combinations of elements in a submodule, then
the linear combination is also in the submodule.\<close>

lemma(in module0) linear_comb_submod:
  assumes "IsAsubmodule(H)" "D\<in>FinPow(X)" "AA:X\<rightarrow>R" "B:X\<rightarrow>H"
  shows "\<Sum>[D;{AA,B}]\<in>H"
proof-
  have fun:"f:G\<times>G\<rightarrow>G" using ab_group.group_oper_fun.
  from assms(4) have BB:"B:X\<rightarrow>G" using ab_group.group0_3_L2[OF sumodule_is_subgroup[OF assms(1)]] func1_1_L1B by auto
  {
    fix A1 B1 assume fun:"A1:X\<rightarrow>R" "B1:X\<rightarrow>H"
    from fun(2) have fun2:"B1:X\<rightarrow>G" using ab_group.group0_3_L2[OF sumodule_is_subgroup[OF assms(1)]] func1_1_L1B by auto
    have "0\<in>FinPow(X)" unfolding FinPow_def by auto
    then have "\<Sum>[0;{A1,B1}]=\<zero>\<^sub>G" using LinearComb_def[OF fun(1) fun2] by auto
    then have "\<Sum>[0;{A1,B1}]\<in>H" using assms(1) ab_group.group0_3_L5 unfolding IsAsubmodule_def by auto
  }
  then have base:"\<forall>A1\<in>X\<rightarrow>R. \<forall>B1\<in>X\<rightarrow>H. \<Sum>[0;{A1,B1}]\<in>H" by auto
  {
    fix RR assume a:"RR\<noteq>0" "RR\<in>FinPow(X)"
    then obtain d where d:"d\<in>RR" by auto
    {
      fix A1 B1 assume fun:"A1:X\<rightarrow>R" "B1:X\<rightarrow>H" and step:"\<forall>A1\<in>X\<rightarrow>R. \<forall>B1\<in>X\<rightarrow>H. \<Sum>[RR-{d};{A1,B1}]\<in>H"
      have F:"{\<langle>m, ({\<langle>r, restrict(S ` r, H)\<rangle> . r \<in> R} ` (A1 ` m)) ` (B1 ` m)\<rangle> . m \<in> X} : X \<rightarrow> H" using module0.fun_aux[OF isAmodule_imp_module0[OF submodule[OF assms(1)]] fun].
      {
        fix m assume mx:"m\<in>X"
        then have bh:"B1`m\<in>H" using fun(2) apply_type by auto
        from mx have ar:"A1`m\<in>R" using fun(1) apply_type by auto
        then have A:"{\<langle>r, restrict(S ` r, H)\<rangle> . r \<in> R}`(A1`m)=restrict(S ` (A1`m), H)" using apply_equality action_submodule[OF assms(1)]
          by auto
        have B:"(restrict(S ` (A1`m), H)) ` (B1 ` m)=(S ` (A1`m))`(B1 ` m)"  using bh restrict by auto
        with A have "({\<langle>r, restrict(S ` r, H)\<rangle> . r \<in> R} ` (A1 ` m)) ` (B1 ` m)=(S ` (A1`m))`(B1 ` m)" by auto
      }
      then have eq1:"{\<langle>m, ({\<langle>r, restrict(S ` r, H)\<rangle> . r \<in> R} ` (A1 ` m)) ` (B1 ` m)\<rangle> . m \<in> X} ={\<langle>m, (S ` (A1`m))`(B1 ` m)\<rangle> . m \<in> X} " by auto
      then have pd:"{\<langle>m, (S ` (A1`m))`(B1 ` m)\<rangle> . m \<in> X}`d\<in>H" using d apply_type[OF F] a(2) unfolding FinPow_def by auto
      from fun(2) have fun2:"B1:X\<rightarrow>G" using ab_group.group0_3_L2[OF sumodule_is_subgroup[OF assms(1)]] func1_1_L1B by auto
      have "\<Sum>[RR;{A1,B1}]=(\<Sum>[RR-{d};{A1,B1}])\<ra>\<^sub>G({\<langle>k, A1 ` k \<cdot>\<^sub>M (B1 ` k)\<rangle> . k \<in> X} ` d)" using sum_one_element[OF fun(1) fun2 a(2) d].
      also have "\<dots>\<in>H" using pd step fun ab_group.group0_3_L6[OF sumodule_is_subgroup[OF assms(1)]] by auto
      ultimately have "\<Sum>[RR;{A1,B1}]\<in>H" by auto
    }
    then have "(\<forall>AA1\<in>X\<rightarrow>R. \<forall>BB1\<in>X\<rightarrow>H. \<Sum>[RR-{d};{AA1,BB1}]\<in>H)\<longrightarrow>(\<forall>AA1\<in>X\<rightarrow>R. \<forall>BB1\<in>X\<rightarrow>H. \<Sum>[RR;{AA1,BB1}]\<in>H)" by auto
    with d have "\<exists>d\<in>RR. ((\<forall>AA1\<in>X\<rightarrow>R. \<forall>BB1\<in>X\<rightarrow>H. \<Sum>[RR-{d};{AA1,BB1}]\<in>H)\<longrightarrow>(\<forall>AA1\<in>X\<rightarrow>R. \<forall>BB1\<in>X\<rightarrow>H. \<Sum>[RR;{AA1,BB1}]\<in>H))" by auto
  }
  then have step:"\<forall>RR\<in>FinPow(X). RR\<noteq>0 \<longrightarrow> (\<exists>d\<in>RR. ((\<forall>AA1\<in>X\<rightarrow>R. \<forall>BB1\<in>X\<rightarrow>H. \<Sum>[RR-{d};{AA1,BB1}]\<in>H)\<longrightarrow>(\<forall>AA1\<in>X\<rightarrow>R. \<forall>BB1\<in>X\<rightarrow>H. \<Sum>[RR;{AA1,BB1}]\<in>H)))" by auto
  show ?thesis using FinPow_ind_rem_one[OF base step] assms(2-4) by auto
qed

text\<open>The terms of a linear combination can be reordered so 
that they are indexed by the elements of the module.\<close>

lemma(in module0) index_module:
  assumes "AAA:X\<rightarrow>R" "BB:X\<rightarrow>G" "D\<in>FinPow(X)"
  shows "\<exists>AA\<in>G\<rightarrow>R. \<Sum>[D;{AAA,BB}]=\<Sum>[BB``D;{AA,id(G)}] \<and> (\<forall>x\<in>G-BB``D. AA`x=\<zero>\<^sub>R)"
proof-
  let ?F="{\<langle>d,CommSetFold(A,AAA,D\<inter>(BB-``({BB`d})))\<rangle>. d\<in>D}"
  let ?f1="{\<langle>d,D\<inter>(BB-``({BB`d}))\<rangle>. d\<in>D}"
  have "?f1:D\<rightarrow>{D\<inter>(BB-``({BB`d})). d\<in>D}" unfolding Pi_def function_def by auto
  then have "RepFun(D,\<lambda>t. ?f1`t)={D\<inter>(BB-``({BB`d})). d\<in>D}" using apply_equality by auto
  with assms(3) have "Finite({D\<inter>(BB-``({BB`d})). d\<in>D})" using Finite_RepFun unfolding FinPow_def by auto
  then obtain n where "{D\<inter>(BB-``({BB`d})). d\<in>D}\<approx>n" and n:"n\<in>nat" unfolding Finite_def by auto
  then have n2:"{D\<inter>(BB-``({BB`d})). d\<in>D}\<lesssim>n" using eqpoll_imp_lepoll by auto
  {
    fix T assume "T\<in>{D\<inter>(BB-``({BB`d})). d\<in>D}"
    then obtain d where d:"d\<in>D" "T=D\<inter>(BB-``({BB`d}))" by auto
    {
      assume "d\<notin>T"
      with d have "d\<notin>(BB-``({BB`d}))" by auto
      then have "\<langle>d,BB`d\<rangle>\<notin>BB" using vimage_iff by auto
      with d(1) assms(2,3) have "False" unfolding FinPow_def Pi_def using function_apply_Pair[of BB d] by auto
    }
    then have "T\<noteq>0" by auto
  }
  then have n3:"\<forall>t\<in>{D\<inter>(BB-``({BB`d})). d\<in>D}. id({D\<inter>(BB-``({BB`d})). d\<in>D}) ` t \<noteq> 0" using id_def by auto
  from n have "\<forall>M N. M \<lesssim> n \<and> (\<forall>t\<in>M. N ` t \<noteq> 0) \<longrightarrow> (\<exists>f. f \<in> Pi(M,\<lambda>t. N ` t) \<and> (\<forall>t\<in>M. f ` t \<in> N ` t))" using finite_choice[of n] unfolding AxiomCardinalChoiceGen_def
    by auto
  with n2 have "\<forall>N. (\<forall>t\<in>{D\<inter>(BB-``({BB`d})). d\<in>D}. N ` t \<noteq> 0) \<longrightarrow> (\<exists>f. f \<in> Pi({D\<inter>(BB-``({BB`d})). d\<in>D},\<lambda>t. N ` t) \<and> (\<forall>t\<in>{D\<inter>(BB-``({BB`d})). d\<in>D}. f ` t \<in> N ` t))"
    by blast
  with n3 have "\<exists>f. f \<in> Pi({D\<inter>(BB-``({BB`d})). d\<in>D},\<lambda>t. id({D\<inter>(BB-``({BB`d})). d\<in>D}) ` t) \<and> (\<forall>t\<in>{D\<inter>(BB-``({BB`d})). d\<in>D}. f ` t \<in> id({D\<inter>(BB-``({BB`d})). d\<in>D}) ` t)"
    by auto
  then obtain ff where ff:"ff\<in>Pi({D\<inter>(BB-``({BB`d})). d\<in>D},\<lambda>t. id({D\<inter>(BB-``({BB`d})). d\<in>D}) ` t)" "(\<forall>t\<in>{D\<inter>(BB-``({BB`d})). d\<in>D}. ff ` t \<in> id({D\<inter>(BB-``({BB`d})). d\<in>D}) ` t)" by force
  {
    fix t assume as:"t\<in>{D\<inter>(BB-``({BB`d})). d\<in>D}"
    with ff(2) have "ff`t\<in>id({D\<inter>(BB-``({BB`d})). d\<in>D}) ` t" by blast
    with as have "ff`t\<in>t" using id_def by auto
  }
  then have ff2:"\<forall>t\<in>{D\<inter>(BB-``({BB`d})). d\<in>D}. ff ` t \<in>t" by auto
  have "\<forall>x\<in>{D\<inter>(BB-``({BB`d})). d\<in>D}. id({D\<inter>(BB-``({BB`d})). d\<in>D})`x=x" using id_def by auto
  with ff(1) have ff1:"ff\<in>Pi({D\<inter>(BB-``({BB`d})). d\<in>D},\<lambda>t. t)" unfolding Pi_def Sigma_def by auto
  have case0:"\<exists>AA\<in>G\<rightarrow>R. \<Sum>[0;{AAA,BB}]=\<Sum>[BB``0;{AA,id(G)}] \<and> (\<forall>x\<in>G-BB``0. AA`x=\<zero>\<^sub>R)"
    proof
      have "\<Sum>[0;{AAA,BB}]=\<zero>\<^sub>G" using LinearComb_def[OF assms(1,2)] unfolding FinPow_def by auto moreover
      let ?A="ConstantFunction(G,\<zero>\<^sub>R)"
      have "\<Sum>[0;{?A,id(G)}]=\<zero>\<^sub>G" using LinearComb_def[OF func1_3_L1[OF 
              ring.Ring_ZF_1_L2(1)], of "id(G)" G 0]
        unfolding id_def FinPow_def by auto moreover
      have "BB``0=0" by auto ultimately
      show "\<Sum>[0;{AAA,BB}]=\<Sum>[BB``0;{?A,id(G)}] \<and> (\<forall>x\<in>G-BB``0. ?A`x=\<zero>\<^sub>R)" using func1_3_L2 by auto
      then show "?A:G\<rightarrow>R" using func1_3_L1[OF ring.Ring_ZF_1_L2(1), of G] by auto
    qed
  {
    fix E assume E:"E\<in>FinPow(X)" "E\<noteq>0"
    {
      fix d assume d:"d\<in>E"
      {
        assume hyp:"\<exists>AA\<in>G\<rightarrow>R. \<Sum>[E-{d};{AAA,BB}]=\<Sum>[BB``(E-{d});{AA,id(G)}] \<and> (\<forall>x\<in>G-BB``(E-{d}). AA`x=\<zero>\<^sub>R)"
        from hyp obtain AA where AA:"AA\<in>G\<rightarrow>R" "\<Sum>[E-{d};{AAA,BB}]=\<Sum>[BB``(E-{d});{AA,id(G)}]" "\<forall>x\<in>G-BB``(E-{d}). AA`x=\<zero>\<^sub>R" by auto
        have "\<Sum>[E;{AAA,BB}] = (\<Sum>[E-{d};{AAA,BB}])\<ra>\<^sub>G({\<langle>e,(AAA`e)\<cdot>\<^sub>M(BB`e)\<rangle>. e\<in>X}`d)" using sum_one_element[OF assms(1,2) E(1) d].
        with AA(2) also have "\<dots>=(\<Sum>[BB``(E-{d});{AA,id(G)}])\<ra>\<^sub>G((AAA`d)\<cdot>\<^sub>M(BB`d))" using d E(1) unfolding FinPow_def using apply_equality[OF _
          fun_aux[OF assms(1,2)]] by auto
        ultimately have eq:"\<Sum>[E;{AAA,BB}] =(\<Sum>[BB``(E-{d});{AA,id(G)}])\<ra>\<^sub>G((AAA`d)\<cdot>\<^sub>M(BB`d))" by auto
        have btype:"BB`d\<in>G" using apply_type assms(2) d E(1) unfolding FinPow_def by auto
        have "(E-{d})\<in>FinPow(X)" using E(1) unfolding FinPow_def using subset_Finite[of "E-{d}" E] by auto moreover
        then have "{BB`x. x\<in>E-{d}}=BB``(E-{d})" using func_imagedef[OF assms(2), of "E-{d}"] unfolding FinPow_def
          by auto
        ultimately have fin:"Finite(BB``(E-{d}))" using Finite_RepFun[of "E-{d}" "\<lambda>t. BB`t"] unfolding FinPow_def by auto
        then have "Finite(BB``(E-{d})\<union>{BB`d})" using Finite_cons[of "BB``(E-{d})" "BB`d"] by auto
        with btype have finpow:"BB``(E-{d})\<union>{BB`d}\<in>FinPow(G)" using func1_1_L6(2)[OF assms(2)] unfolding FinPow_def by auto
        {
          assume as:"BB`d\<notin>BB``(E-{d})"
          then have T_def:"BB``(E-{d})=(BB``(E-{d})\<union>{BB`d})-{BB`d}" by auto
          from as have sub:"BB``(E-{d})\<subseteq>G-{BB`d}" using func1_1_L6(2)[OF assms(2)] by auto
          let ?A="restrict(AA,G-{BB`d})\<union>ConstantFunction({BB`d},AAA`d)"
          have res:"restrict(AA,G-{BB`d}):G-{BB`d}\<rightarrow>R" using restrict_fun[OF AA(1)] by auto
          moreover have "AAA`d\<in>R" using apply_type assms(1) d E(1) unfolding FinPow_def by auto
          then have con:"ConstantFunction({BB`d},AAA`d):{BB`d}\<rightarrow>R" using func1_3_L1 by auto
          moreover have "(G-{BB`d})\<inter>{BB`d}=0" by auto moreover
          have "R\<union>R=R" by auto moreover
          have "(G-{BB`d})\<union>{BB`d}=G" using apply_type[OF assms(2)] d E(1) unfolding FinPow_def by auto ultimately
          have A_fun:"?A:G\<rightarrow>R" using fun_disjoint_Un[of "restrict(AA,G-{BB`d})" "G-{BB`d}" R "ConstantFunction({BB`d},AAA`d)" "{BB`d}" R] by auto
          have "?A`(BB`d)=ConstantFunction({BB`d},AAA`d)`(BB`d)" using as fun_disjoint_apply2 by auto moreover note btype
          ultimately have A_app:"?A`(BB`d)=AAA`d" using as func1_3_L2 by auto
          {
            fix z assume "z\<in>restrict(?A,BB``(E-{d}))"
            then have z:"z\<in>?A" "\<exists>x\<in>BB `` (E - {d}). \<exists>y. z = \<langle>x, y\<rangle>" using restrict_iff by auto
            then have "\<exists>x\<in>BB `` (E - {d}). \<exists>y. z = \<langle>x, y\<rangle>" "z\<in>ConstantFunction({BB`d},AAA`d) \<or> z\<in>restrict(AA,G-{BB`d})" by auto
            then have "\<exists>x\<in>BB `` (E - {d}). \<exists>y. z = \<langle>x, y\<rangle>" "z\<in>{BB`d}\<times>{AAA`d} \<or> z\<in>restrict(AA,G-{BB`d})" using ConstantFunction_def by auto
            then have "fst(z)\<in>BB `` (E - {d})" "z=\<langle>BB`d,AAA`d\<rangle> \<or> z\<in>restrict(AA,G-{BB`d})"  by auto
            with as have "z\<in>restrict(AA,G-{BB`d})" by auto
            with z(2) have "z\<in>AA" "\<exists>x\<in>BB `` (E - {d}). \<exists>y. z = \<langle>x, y\<rangle>" using restrict_iff by auto
            then have "z\<in>restrict(AA,BB``(E-{d}))" using restrict_iff by auto
          }
          then have "restrict(?A,BB``(E-{d}))\<subseteq>restrict(AA,BB``(E-{d}))" by auto moreover
          {
            fix z assume z:"z\<in>restrict(AA,BB``(E-{d}))" "z\<notin>restrict(?A,BB``(E-{d}))"
            then have disj:"z\<notin>?A \<or> (\<forall>x\<in>BB``(E-{d}). \<forall>y. z \<noteq> \<langle>x, y\<rangle>)" using restrict_iff[of z ?A "BB``(E-{d})"] by auto moreover
            with z(1) have z:"z\<in>AA" "\<exists>x\<in>BB``(E-{d}). \<exists>y. z=\<langle>x, y\<rangle>" using restrict_iff[of _ AA "BB``(E-{d})"] by auto moreover
            from z(2) sub have "\<exists>x\<in>G-{BB`d}. \<exists>y. z=\<langle>x, y\<rangle>" by auto
            with z(1) have "z\<in>restrict(AA,G-{BB`d})" using restrict_iff by auto
            then have "z\<in>?A" by auto
            with disj have "\<forall>x\<in>BB``(E-{d}). \<forall>y. z \<noteq> \<langle>x, y\<rangle>" by auto
            with z(2) have "False" by auto
          }
          then have "restrict(AA,BB``(E-{d}))\<subseteq>restrict(?A,BB``(E-{d}))" by auto ultimately
          have resA:"restrict(AA,BB``(E-{d}))=restrict(?A,BB``(E-{d}))" by auto
          have "\<Sum>[BB``(E-{d});{AA,id(G)}]=\<Sum>[BB``(E-{d});{restrict(AA,BB``(E-{d})),restrict(id(G), BB``(E-{d}))}]" using linComb_restrict_coord[OF AA(1) id_type, of "BB``(E-{d})"]
            fin func1_1_L6(2)[OF assms(2)] unfolding FinPow_def by auto
          also have "\<dots>=\<Sum>[BB``(E-{d});{restrict(?A,BB``(E-{d})),restrict(id(G), BB``(E-{d}))}]" using resA by auto
          also have "\<dots>=\<Sum>[BB``(E-{d});{?A,id(G)}]" using linComb_restrict_coord[OF A_fun id_type, of "BB``(E-{d})"] fin func1_1_L6(2)[OF assms(2)] unfolding FinPow_def by auto
          ultimately have "\<Sum>[BB``(E-{d});{AA,id(G)}]=\<Sum>[(BB``(E-{d})\<union>{BB`d})-{BB`d};{?A,id(G)}]" using T_def by auto
          then have "(\<Sum>[BB``(E-{d});{AA,id(G)}])\<ra>\<^sub>G((AAA`d)\<cdot>\<^sub>M(BB`d))=(\<Sum>[(BB``(E-{d})\<union>{BB`d})-{BB`d};{?A,id(G)}])\<ra>\<^sub>G((?A`(BB`d))\<cdot>\<^sub>M(BB`d))" using A_app by auto
          also have "\<dots>=(\<Sum>[(BB``(E-{d})\<union>{BB`d})-{BB`d};{?A,id(G)}])\<ra>\<^sub>G((?A`(BB`d))\<cdot>\<^sub>M(id(G)`(BB`d)))" using id_conv[OF btype] by auto
          also have "\<dots>=(\<Sum>[(BB``(E-{d})\<union>{BB`d})-{BB`d};{?A,id(G)}])\<ra>\<^sub>G({\<langle>g,(?A`g)\<cdot>\<^sub>M(id(G)`g)\<rangle>. g\<in>G}`(BB`d))" using apply_equality[OF _ fun_aux[OF A_fun id_type]
            ,of "BB`d" "(?A`(BB`d))\<cdot>\<^sub>M(id(G)`(BB`d))"] btype by auto
          also have "\<dots>=(\<Sum>[(BB``(E-{d})\<union>{BB`d});{?A,id(G)}])" using sum_one_element[OF A_fun id_type finpow, of "BB`d"] by auto
          ultimately have "(\<Sum>[BB``(E-{d});{AA,id(G)}])\<ra>\<^sub>G((AAA`d)\<cdot>\<^sub>M(BB`d))=\<Sum>[(BB``(E-{d})\<union>{BB`d});{?A,id(G)}]" by auto
          with eq have eq:"\<Sum>[E;{AAA,BB}] =\<Sum>[(BB``(E-{d})\<union>{BB`d});{?A,id(G)}]" by auto
          have "BB``(E-{d})\<union>{BB`d}={BB`x. x\<in>E-{d}}\<union>{BB`d}" using func_imagedef[OF assms(2), of "E-{d}"]
            E(1) unfolding FinPow_def by force
          also have "\<dots>={BB`x. x\<in>E}" using d by auto ultimately
          have set:"BB``(E-{d})\<union>{BB`d}=BB``E" using func_imagedef[OF assms(2), of "E"] E(1) unfolding FinPow_def by auto
          {
            fix x assume x:"x\<in>G-BB``E"
            then have x1:"x\<noteq>BB`d" using d func_imagedef[OF assms(2), of E] E(1) unfolding FinPow_def by auto
            then have "?A`x=restrict(AA,G-{BB`d})`x" using fun_disjoint_apply1[of x "ConstantFunction({BB`d},AAA`d)"] unfolding
              ConstantFunction_def by blast
            with x x1 have "?A`x=AA`x" using restrict by auto moreover
            from x set have "x\<in>G-BB``(E-{d})" by auto ultimately
            have "?A`x=\<zero>\<^sub>R" using AA(3) by auto
          }
          with set eq A_fun have "\<exists>AA\<in>G\<rightarrow>R. \<Sum>[E;{AAA,BB}]=\<Sum>[BB``E;{AA,id(G)}] \<and> (\<forall>x\<in>G-(BB``E). AA`x=\<zero>\<^sub>R)" by auto
        }
        moreover
        {
          assume as:"BB`d\<in>BB``(E-{d})"
          then have "BB``(E-{d})\<union>{BB`d}=BB``(E-{d})" by auto
          then have finpow:"BB``(E-{d})\<in>FinPow(G)" using finpow by auto
          have sub:"E-{d}\<subseteq>X" using E(1) unfolding FinPow_def by force
          with as have "BB`d\<in>{BB`f. f\<in>E-{d}}" using func_imagedef[OF assms(2), of "E-{d}"] by auto
          then have "{BB`f. f\<in>E-{d}}={BB`f. f\<in>E}" by auto
          then have im_eq:"BB``(E-{d})=BB``E" using func_imagedef[OF assms(2),of "E-{d}"] func_imagedef[OF assms(2),of E] sub E(1) unfolding FinPow_def
            by auto
          from as have "\<Sum>[BB``(E-{d});{AA,id(G)}]=(\<Sum>[BB``(E-{d})-{BB`d};{AA,id(G)}])\<ra>\<^sub>G({\<langle>g,(AA`g)\<cdot>\<^sub>M(id(G)`g)\<rangle>. g\<in>G}`(BB`d))" using sum_one_element[OF AA(1) id_type]
            finpow by auto
          also have "\<dots>=(\<Sum>[BB``(E-{d})-{BB`d};{AA,id(G)}])\<ra>\<^sub>G((AA`(BB`d))\<cdot>\<^sub>M(id(G)`(BB`d)))" using apply_equality[OF _ fun_aux[OF AA(1) id_type]]
            btype by auto
          also have "\<dots>=(\<Sum>[BB``(E-{d})-{BB`d};{AA,id(G)}])\<ra>\<^sub>G((AA`(BB`d))\<cdot>\<^sub>M(BB`d))" using id_conv btype by auto
          ultimately have "\<Sum>[BB``(E-{d});{AA,id(G)}]=(\<Sum>[BB``(E-{d})-{BB`d};{AA,id(G)}])\<ra>\<^sub>G((AA`(BB`d))\<cdot>\<^sub>M(BB`d))" by auto
          then have "\<Sum>[E;{AAA,BB}] =((\<Sum>[BB``(E-{d})-{BB`d};{AA,id(G)}])\<ra>\<^sub>G((AA`(BB`d))\<cdot>\<^sub>M(BB`d)))\<ra>\<^sub>G(AAA ` d \<cdot>\<^sub>M (BB ` d))" using eq by auto
          moreover have "\<Sum>[BB``(E-{d})-{BB`d};{AA,id(G)}]\<in>G" using linComb_is_in_module[OF AA(1) id_type, of "BB``(E-{d})-{BB`d}"] finpow subset_Finite[of "BB``(E-{d})-{BB`d}" "BB``(E-{d})"] unfolding FinPow_def
            by auto moreover
          have "(AA`(BB`d))\<cdot>\<^sub>M(BB`d)\<in>G" using apply_type[OF S_fun apply_type[OF AA(1) btype]] unfolding End_def using apply_type[of "S ` (AA ` (BB ` d))"
            G "\<lambda>t. G" "BB`d"] btype by auto  moreover
          have "(AAA`d)\<cdot>\<^sub>M(BB`d)\<in>G" using apply_type[OF S_fun apply_type[OF assms(1), of d]] unfolding End_def using apply_type[of "S ` (AAA ` d)"
            G "\<lambda>t. G" "BB`d"] btype d E(1) unfolding FinPow_def  by auto ultimately
          have "\<Sum>[E;{AAA,BB}] =(\<Sum>[BB``(E-{d})-{BB`d};{AA,id(G)}])\<ra>\<^sub>G(((AA`(BB`d))\<cdot>\<^sub>M(BB`d))\<ra>\<^sub>G(AAA ` d \<cdot>\<^sub>M (BB ` d)))" 
            using ab_group.group_oper_assoc by auto moreover
          have "((AA`(BB`d))\<cdot>\<^sub>M(BB`d))\<ra>\<^sub>G(AAA ` d \<cdot>\<^sub>M (BB ` d))=((AA`(BB`d))\<ra>\<^sub>R(AAA ` d))\<cdot>\<^sub>M(BB`d)" using S_dist1 btype apply_type[OF assms(1), of d]
            apply_type[OF AA(1) btype] d E(1) unfolding FinPow_def by auto
          ultimately have eq:"\<Sum>[E;{AAA,BB}] =(\<Sum>[BB``(E-{d})-{BB`d};{AA,id(G)}])\<ra>\<^sub>G(((AA`(BB`d))\<ra>\<^sub>R(AAA ` d))\<cdot>\<^sub>M(BB`d))" by auto
          let ?A="restrict(AA,G-{BB`d})\<union>ConstantFunction({BB`d},(AA`(BB`d))\<ra>\<^sub>R(AAA ` d))"
          have "(G-{BB`d})\<inter>({BB`d})=0" by auto moreover
          have "(G-{BB`d})\<union>({BB`d})=G" using finpow as unfolding FinPow_def by auto moreover
          have "restrict(AA,G-{BB`d}):(G-{BB`d})\<rightarrow>R" using restrict_fun[OF AA(1), of "G-{BB`d}"] finpow unfolding FinPow_def by auto moreover
          have "AAA`d\<in>R" "AA`(BB`d)\<in>R" using apply_type assms(1) AA(1) btype d E(1) unfolding FinPow_def by auto
          then have "(AA`(BB`d))\<ra>\<^sub>R(AAA ` d)\<in>R" using ring.Ring_ZF_1_L4(1) by auto
          then have "ConstantFunction({BB`d},(AA`(BB`d))\<ra>\<^sub>R(AAA ` d)):{BB`d}\<rightarrow>R" using func1_3_L1 by auto
          ultimately have A_fun:"?A:G\<rightarrow>R" using fun_disjoint_Un[of "restrict(AA,G-{BB`d})" "G-{BB`d}" R "ConstantFunction({BB`d},(AA`(BB`d))\<ra>\<^sub>R(AAA ` d))" "{BB`d}" R] by auto
          have "?A`(BB`d)=ConstantFunction({BB`d},(AA`(BB`d))\<ra>\<^sub>R(AAA ` d))`(BB`d)" using as fun_disjoint_apply2 by auto moreover note btype
          ultimately have A_app:"?A`(BB`d)=(AA`(BB`d))\<ra>\<^sub>R(AAA ` d)" using as func1_3_L2 by auto
          {
            fix z assume "z\<in>restrict(?A,BB``(E-{d})-{BB`d})"
            then have z:"\<exists>x\<in>BB``(E-{d})-{BB`d}. \<exists>y. z=\<langle>x,y\<rangle>" "z\<in>?A" using restrict_iff by auto
            then have "\<exists>x\<in>BB `` (E - {d})-{BB`d}. \<exists>y. z = \<langle>x, y\<rangle>" "z\<in>ConstantFunction({BB`d},(AA`(BB`d))\<ra>\<^sub>R(AAA ` d)) \<or> z\<in>restrict(AA,G-{BB`d})" by auto
            then have "\<exists>x\<in>BB `` (E - {d})-{BB`d}. \<exists>y. z = \<langle>x, y\<rangle>" "z\<in>{BB`d}\<times>{(AA`(BB`d))\<ra>\<^sub>R(AAA ` d)} \<or> z\<in>restrict(AA,G-{BB`d})" using ConstantFunction_def by auto
            then have "fst(z)\<in>BB `` (E - {d})-{BB`d}" "z=\<langle>BB`d,AAA`d\<rangle> \<or> z\<in>restrict(AA,G-{BB`d})"  by auto
            then have "z\<in>restrict(AA,G-{BB`d})" by auto
            with z(1) have "z\<in>AA" "\<exists>x\<in>BB `` (E - {d})-{BB`d}. \<exists>y. z = \<langle>x, y\<rangle>" using restrict_iff by auto
            then have "z\<in>restrict(AA,BB``(E-{d})-{BB`d})" using restrict_iff by auto
          }
          then have "restrict(?A,BB``(E-{d})-{BB`d})\<subseteq>restrict(AA,BB``(E-{d})-{BB`d})" by auto moreover
          {
            fix z assume z:"z\<in>restrict(AA,BB``(E-{d})-{BB`d})" "z\<notin>restrict(?A,BB``(E-{d})-{BB`d})"
            then have disj:"z\<notin>?A \<or> (\<forall>x\<in>BB``(E-{d})-{BB`d}. \<forall>y. z \<noteq> \<langle>x, y\<rangle>)" using restrict_iff[of z ?A "BB``(E-{d})-{BB`d}"] by auto moreover
            with z(1) have z:"z\<in>AA" "\<exists>x\<in>BB``(E-{d})-{BB`d}. \<exists>y. z=\<langle>x, y\<rangle>" using restrict_iff[of _ AA "BB``(E-{d})-{BB`d}"] by auto moreover
            from z(2) func1_1_L6(2)[OF assms(2)] have "\<exists>x\<in>G-{BB`d}. \<exists>y. z=\<langle>x, y\<rangle>" by auto
            with z(1) have "z\<in>restrict(AA,G-{BB`d})" using restrict_iff by auto
            then have "z\<in>?A" by auto
            with disj have "\<forall>x\<in>BB``(E-{d})-{BB`d}. \<forall>y. z \<noteq> \<langle>x, y\<rangle>" by auto
            with z(2) have "False" by auto
          }
          then have "restrict(AA,BB``(E-{d})-{BB`d})\<subseteq>restrict(?A,BB``(E-{d})-{BB`d})" by auto ultimately
          have resA:"restrict(AA,BB``(E-{d})-{BB`d})=restrict(?A,BB``(E-{d})-{BB`d})" by auto
          have "Finite(BB``(E-{d})-{BB`d})" using finpow unfolding FinPow_def using subset_Finite[of "BB``(E-{d}) -{BB`d}"] by auto
          with finpow have finpow2:"BB``(E-{d})-{BB`d}\<in>FinPow(G)" unfolding FinPow_def by auto
          have "\<Sum>[BB``(E-{d})-{BB`d};{AA,id(G)}]=\<Sum>[BB``(E-{d})-{BB`d};{restrict(AA,BB``(E-{d})-{BB`d}),restrict(id(G), BB``(E-{d})-{BB`d})}]" using linComb_restrict_coord[OF AA(1) id_type finpow2]
            by auto
          also have "\<dots>=\<Sum>[BB``(E-{d})-{BB`d};{restrict(?A,BB``(E-{d})-{BB`d}),restrict(id(G), BB``(E-{d})-{BB`d})}]" using resA by auto
          also have "\<dots>=\<Sum>[BB``(E-{d})-{BB`d};{?A,id(G)}]" using linComb_restrict_coord[OF A_fun id_type finpow2] by auto
          ultimately have "\<Sum>[BB``(E-{d})-{BB`d};{AA,id(G)}]=\<Sum>[BB``(E-{d})-{BB`d};{?A,id(G)}]" by auto
          then have "(\<Sum>[BB``(E-{d})-{BB`d};{AA,id(G)}])\<ra>\<^sub>G(((AA`(BB`d))\<ra>\<^sub>R(AAA ` d))\<cdot>\<^sub>M(BB`d))=(\<Sum>[BB``(E-{d})-{BB`d};{?A,id(G)}])\<ra>\<^sub>G((?A`(BB`d))\<cdot>\<^sub>M(BB`d))" using A_app by auto
          also have "\<dots>=(\<Sum>[BB``(E-{d})-{BB`d};{?A,id(G)}])\<ra>\<^sub>G((?A`(BB`d))\<cdot>\<^sub>M(id(G)`(BB`d)))" using id_conv[OF btype] by auto
          also have "\<dots>=(\<Sum>[BB``(E-{d})-{BB`d};{?A,id(G)}])\<ra>\<^sub>G({\<langle>g,(?A`g)\<cdot>\<^sub>M(id(G)`g)\<rangle>. g\<in>G}`(BB`d))" using apply_equality[OF _ fun_aux[OF A_fun id_type]
            ,of "BB`d" "(?A`(BB`d))\<cdot>\<^sub>M(id(G)`(BB`d))"] btype by auto
          also have "\<dots>=(\<Sum>[BB``(E-{d});{?A,id(G)}])" using sum_one_element[OF A_fun id_type finpow as] by auto
          ultimately have "(\<Sum>[BB``(E-{d})-{BB`d};{AA,id(G)}])\<ra>\<^sub>G(((AA`(BB`d))\<ra>\<^sub>R(AAA ` d))\<cdot>\<^sub>M(BB`d))=(\<Sum>[BB``(E-{d});{?A,id(G)}])" by auto
          with eq have sol:"\<Sum>[E;{AAA,BB}] =\<Sum>[BB``(E-{d});{?A,id(G)}]" by auto
          {
            fix x assume x:"x\<in>G-BB``E"
            with as have x1:"x\<in>G-{BB`d}" by auto
            then have "?A`x=restrict(AA,G-{BB`d})`x" using fun_disjoint_apply1[of x "ConstantFunction({BB`d},(AA`(BB`d))\<ra>\<^sub>R(AAA ` d))"]
              unfolding ConstantFunction_def by blast
            with x1 have "?A`x=AA`x" using restrict by auto
            with x im_eq have "?A`x=\<zero>\<^sub>R" using AA(3) by auto
          }
          with sol A_fun im_eq have "\<exists>AA\<in>G\<rightarrow>R. \<Sum>[E;{AAA,BB}]=\<Sum>[BB``(E);{AA,id(G)}] \<and> (\<forall>x\<in>G-BB``E. AA`x=\<zero>\<^sub>R)" by auto
        }
        ultimately have "\<exists>AA\<in>G\<rightarrow>R. \<Sum>[E;{AAA,BB}]=\<Sum>[BB``E;{AA,id(G)}] \<and> (\<forall>x\<in>G-BB``E. AA`x=\<zero>\<^sub>R)" by auto
      }
      then have "( \<exists>AA\<in>G\<rightarrow>R. (\<Sum>[E-{d};{AAA,BB}])=(\<Sum>[BB``(E-{d});{AA,id(G)}]) \<and> (\<forall>x\<in>G-BB``(E-{d}). AA`x=\<zero>\<^sub>R)) \<longrightarrow> (\<exists>AA\<in>G\<rightarrow>R. (\<Sum>[E;{AAA,BB}])=(\<Sum>[BB``E;{AA,id(G)}]) \<and> (\<forall>x\<in>G-BB``E. AA`x=\<zero>\<^sub>R))" by auto
    }
    then have "\<exists>d\<in>E. (( \<exists>AA\<in>G\<rightarrow>R. \<Sum>[E-{d};{AAA,BB}]=\<Sum>[BB``(E-{d});{AA,id(G)}] \<and> (\<forall>x\<in>G-BB``(E-{d}). AA`x=\<zero>\<^sub>R)) \<longrightarrow> (\<exists>AA\<in>G\<rightarrow>R. \<Sum>[E;{AAA,BB}]=\<Sum>[BB``(E);{AA,id(G)}] \<and> (\<forall>x\<in>G-BB``E. AA`x=\<zero>\<^sub>R)))"
      using E(2) by auto
  }
  then have "\<forall>E\<in>FinPow(X). E\<noteq>0 \<longrightarrow> (\<exists>d\<in>E. ((\<exists>AA\<in>G\<rightarrow>R. \<Sum>[E-{d};{AAA,BB}]=\<Sum>[BB``(E-{d});{AA,id(G)}]\<and> (\<forall>x\<in>G-BB``(E-{d}). AA`x=\<zero>\<^sub>R)) \<longrightarrow> (\<exists>AA\<in>G\<rightarrow>R. \<Sum>[E;{AAA,BB}]=\<Sum>[BB``(E);{AA,id(G)}]\<and> (\<forall>x\<in>G-BB``E. AA`x=\<zero>\<^sub>R))))"
    by auto
  then show ?thesis using FinPow_ind_rem_one[where ?P="\<lambda>E. \<exists>AA\<in>G\<rightarrow>R. \<Sum>[E;{AAA,BB}]=\<Sum>[BB``E;{AA,id(G)}]\<and> (\<forall>x\<in>G-BB``E. AA`x=\<zero>\<^sub>R)", OF case0 _ assms(3)] by auto
qed


text\<open>A linear combinations with zeros as coefficients is zero.\<close>


lemma(in module0) zero_coef:
  assumes "\<forall>m\<in>D. AAA`m=\<zero>\<^sub>R" "AAA:X\<rightarrow>R" "BB:X\<rightarrow>G" "D\<in>FinPow(X)"
  shows "\<Sum>[D;{AAA,BB}]=\<zero>\<^sub>G"
proof-
  {
    fix A1 B1 assume fun:"A1:X\<rightarrow>R" "B1:X\<rightarrow>G" moreover
    have "0\<in>FinPow(X)" unfolding FinPow_def by auto
    ultimately have "\<Sum>[0;{A1,B1}]=\<zero>\<^sub>G" using LinearComb_def by auto
  }
  then have base:"\<forall>AA1\<in>X\<rightarrow>R. \<forall>BB1\<in>X\<rightarrow>G. ((\<forall>m\<in>0. AA1`m=\<zero>\<^sub>R) \<longrightarrow> \<Sum>[0;{AA1,BB1}]=\<zero>\<^sub>G)" by auto
  {
    fix RR assume a:"RR\<noteq>0" "RR\<in>FinPow(X)"
    then obtain d where d:"d\<in>RR" by auto
    {
      fix A1 B1 assume fun:"A1:X\<rightarrow>R" "B1:X\<rightarrow>G" and step:"\<forall>A1\<in>X\<rightarrow>R. \<forall>B1\<in>X\<rightarrow>G. ((\<forall>m\<in>RR-{d}. A1`m=\<zero>\<^sub>R) \<longrightarrow> \<Sum>[RR-{d};{A1,B1}]=\<zero>\<^sub>G)" "\<forall>m\<in>RR. A1`m=\<zero>\<^sub>R"
      from fun step(1) have "(\<forall>m\<in>RR-{d}. A1`m=\<zero>\<^sub>R) \<longrightarrow> \<Sum>[RR-{d};{A1,B1}]=\<zero>\<^sub>G" by auto
      moreover
      {
        fix m assume "m\<in>RR-{d}"
        then have "m\<in>RR" by auto
        with step(2) have "A1`m=\<zero>\<^sub>R" by auto
      }
      then have "\<forall>m\<in>RR-{d}. A1`m=\<zero>\<^sub>R" by auto
      ultimately have step3:"\<Sum>[RR-{d};{A1,B1}]=\<zero>\<^sub>G" by auto
      from fun a(2) have "\<Sum>[RR;{A1,B1}]=(\<Sum>[RR-{d};{A1,B1}])\<ra>\<^sub>G({\<langle>k,(A1`k)\<cdot>\<^sub>M(B1`k)\<rangle>. k\<in>X}`d)" using sum_one_element d by auto
      also have "\<dots>=\<zero>\<^sub>G\<ra>\<^sub>G({\<langle>k,(A1`k)\<cdot>\<^sub>M(B1`k)\<rangle>. k\<in>X}`d)" using step3 by auto
      also have "\<dots>={\<langle>k,(A1`k)\<cdot>\<^sub>M(B1`k)\<rangle>. k\<in>X}`d" using fun_aux[OF fun] apply_type d a(2)
        unfolding FinPow_def using ab_group.group0_2_L2 by auto
      also have "\<dots>=(A1`d)\<cdot>\<^sub>M(B1`d)" using fun_aux[OF fun] apply_equality d a(2) unfolding FinPow_def by auto
      also have "\<dots>=\<zero>\<^sub>R\<cdot>\<^sub>M(B1`d)" using step(2) d by auto
      also have "\<dots>=\<zero>\<^sub>G" using mult_zeroR apply_type fun(2) d a(2) unfolding FinPow_def by auto
      ultimately have "\<Sum>[RR;{A1,B1}]=\<zero>\<^sub>G" by auto
    }
    then have "(\<forall>A1\<in>X\<rightarrow>R. \<forall>B1\<in>X\<rightarrow>G. ((\<forall>m\<in>RR-{d}. A1`m=\<zero>\<^sub>R) \<longrightarrow> \<Sum>[RR-{d};{A1,B1}]=\<zero>\<^sub>G))\<longrightarrow>(\<forall>A1\<in>X\<rightarrow>R. \<forall>B1\<in>X\<rightarrow>G. ((\<forall>m\<in>RR. A1`m=\<zero>\<^sub>R) \<longrightarrow> \<Sum>[RR;{A1,B1}]=\<zero>\<^sub>G))"
      by auto
    then have "\<exists>d\<in>RR. ((\<forall>A1\<in>X\<rightarrow>R. \<forall>B1\<in>X\<rightarrow>G. ((\<forall>m\<in>RR-{d}. A1`m=\<zero>\<^sub>R) \<longrightarrow> \<Sum>[RR-{d};{A1,B1}]=\<zero>\<^sub>G))\<longrightarrow>(\<forall>A1\<in>X\<rightarrow>R. \<forall>B1\<in>X\<rightarrow>G. ((\<forall>m\<in>RR. A1`m=\<zero>\<^sub>R) \<longrightarrow> \<Sum>[RR;{A1,B1}]=\<zero>\<^sub>G)))"
      using d by auto
  }
  then have step:"\<forall>RR\<in>FinPow(X). RR\<noteq>0 \<longrightarrow> (\<exists>d\<in>RR. ((\<forall>A1\<in>X\<rightarrow>R. \<forall>B1\<in>X\<rightarrow>G. ((\<forall>m\<in>RR-{d}. A1`m=\<zero>\<^sub>R) \<longrightarrow> \<Sum>[RR-{d};{A1,B1}]=\<zero>\<^sub>G))\<longrightarrow>(\<forall>A1\<in>X\<rightarrow>R. \<forall>B1\<in>X\<rightarrow>G. ((\<forall>m\<in>RR. A1`m=\<zero>\<^sub>R) \<longrightarrow> \<Sum>[RR;{A1,B1}]=\<zero>\<^sub>G))))" by auto
  show ?thesis using FinPow_ind_rem_one[OF base step] assms by auto
qed

text\<open>A very important concept in module theory is an irreducible module.\<close>

definition
Irr ("[_,_]{is irreducible for}[_,_,_|_]" 87)
where "IsAmodule(R,A,M,G,f,S)\<Longrightarrow>[G,f]{is irreducible for}[R,A,M|S] \<equiv> (\<forall>H. module0.IsAsubmodule(R,f,S,H) \<longrightarrow> H={TheNeutralElement(G,f)}\<or>H=G)\<and>G\<noteq>{TheNeutralElement(G,f)}"
      
definition(in module0) 
  IrrSub("_{is an irreducible submodule}")
  where  "H{is an irreducible submodule} \<equiv> IsAsubmodule(H) \<and> Irr(H,restrict(f,H\<times>H),R,A,M,{\<langle>r,restrict(S`r,H)\<rangle>. r\<in>R})"

text\<open>Since we know linear combinations, we can define the span of a subset
of a module as the linear combinations of elements in that subset. We have already
proven that the sum can be done only over finite numbers considering a bijection
between a finite number and the original finite set, and that the function can be
restricted to that finite number.\<close>

definition(in module0)
  Span("{span of}_")
  where "T\<subseteq>G \<Longrightarrow> {span of}T \<equiv> if T=0 then {\<zero>\<^sub>G} else {\<Sum>[F;{AA,id(T)}]. \<langle>F,AA\<rangle>\<in>{\<langle>FF,B\<rangle>\<in>FinPow(T)\<times>(T\<rightarrow>R). \<forall>m\<in>T-FF. B`m=\<zero>\<^sub>R}}"

text\<open>The span of a subset is then a submodule and contains the original set.\<close>

theorem(in module0) linear_ind_set_comb_submodule:
  assumes "T\<subseteq>G"
  shows "IsAsubmodule({span of}T)"
  and "T\<subseteq>{span of}T"
proof-
  have "id(T):T\<rightarrow>T" unfolding id_def by auto
  then have idG:"id(T):T\<rightarrow>G" using assms func1_1_L1B by auto
  {
    assume A:"T=0"
    from A assms have eq:"({span of}T)={\<zero>\<^sub>G}" using Span_def by auto
    have "\<forall>r\<in>R. r\<cdot>\<^sub>M\<zero>\<^sub>G=\<zero>\<^sub>G" using mult_zeroG by auto
    with eq have "\<forall>r\<in>R. \<forall>g\<in>({span of}T). r\<cdot>\<^sub>Mg\<in>({span of}T)" by auto moreover
    from eq have "IsAsubgroup(({span of}T),f)" using ab_group.trivial_normal_subgroup
      unfolding IsAnormalSubgroup_def by auto
    ultimately have "IsAsubmodule({span of}T)" unfolding IsAsubmodule_def by auto
    with A have "IsAsubmodule({span of}T)" "T\<subseteq>{span of}T" by auto
  }
  moreover
  {
    assume A:"T\<noteq>0"
    {
      fix t assume asT:"t\<in>T"
      then have "Finite({t})" by auto
      with asT have FP:"{t}\<in>FinPow(T)" unfolding FinPow_def by auto moreover
      from asT have Af:"{\<langle>t,\<one>\<^sub>R\<rangle>}\<union>{\<langle>r,\<zero>\<^sub>R\<rangle>. r\<in>T-{t}}:T\<rightarrow>R" unfolding Pi_def function_def using
        ring.Ring_ZF_1_L2(1,2) by auto moreover
      {
        fix m assume "m\<in>T-{t}"
        with Af have "({\<langle>t,\<one>\<^sub>R\<rangle>}\<union>{\<langle>r,\<zero>\<^sub>R\<rangle>. r\<in>T-{t}})`m=\<zero>\<^sub>R" using apply_equality by auto
      }
      ultimately have "\<Sum>[{t};{{\<langle>t,\<one>\<^sub>R\<rangle>}\<union>{\<langle>r,\<zero>\<^sub>R\<rangle>. r\<in>T-{t}},id(T)}]\<in>{span of}T" unfolding Span_def[OF assms(1)] using A
        by auto
      then have "(({\<langle>t,\<one>\<^sub>R\<rangle>}\<union>{\<langle>r,\<zero>\<^sub>R\<rangle>. r\<in>T-{t}})`t) \<cdot>\<^sub>M (id(T)`t) \<in>{span of}T" using linComb_one_element[OF asT
        Af idG] by auto
      then have "(({\<langle>t,\<one>\<^sub>R\<rangle>}\<union>{\<langle>r,\<zero>\<^sub>R\<rangle>. r\<in>T-{t}})`t) \<cdot>\<^sub>M t \<in>{span of}T" using asT by auto
      then have "(\<one>\<^sub>R) \<cdot>\<^sub>M t \<in>{span of}T" using apply_equality Af by auto moreover
      have "(\<one>\<^sub>R) \<cdot>\<^sub>M t=t" using S_one assms asT by auto ultimately
      have "t\<in>{span of}T" by auto
    }
    then have "T\<subseteq>{span of}T" by auto moreover
    with A have "({span of}T)\<noteq>0" by auto moreover
    {
      fix l assume "l\<in>{span of}T"
      with A obtain S AA where l:"l=\<Sum>[S;{AA,id(T)}]" "S\<in>FinPow(T)" "AA:T\<rightarrow>R" "\<forall>m\<in>T-S. AA`m=\<zero>\<^sub>R" unfolding Span_def[OF assms(1)]
        by auto
      from l(1) have "l\<in>G" using linComb_is_in_module[OF l(3) _ l(2), of "id(T)"] idG unfolding FinPow_def by auto
    }
    then have sub:"({span of}T)\<subseteq>G" by force moreover
    {
      fix T1 T2 assume as:"T1\<in>{span of}T"
        "T2\<in>{span of}T"
      with A obtain TT1 AA1 TT2 AA2 where T:"TT1\<in>FinPow(T)" "TT2\<in>FinPow(T)" "AA1:T\<rightarrow>R"
        "AA2:T\<rightarrow>R" "T1=\<Sum>[TT1;{AA1,id(T)}]" "T2=\<Sum>[TT2;{AA2,id(T)}]" "\<forall>m\<in>T-TT1. AA1`m=\<zero>\<^sub>R" "\<forall>m\<in>T-TT2. AA2`m=\<zero>\<^sub>R" unfolding Span_def[OF assms(1)] by auto
      {
        assume A:"TT1=0"
        then have "T1=\<Sum>[0;{AA1,id(T)}]" using T(5) by auto
        also have "\<dots>=\<zero>\<^sub>G" using LinearComb_def[OF T(3) idG T(1)] A by auto
        ultimately have "T1\<ra>\<^sub>GT2=\<zero>\<^sub>G\<ra>\<^sub>GT2" by auto
        also have "\<dots>\<in>{span of}T" using sub as(2) ab_group.group0_2_L2 by auto
        ultimately have "T1\<ra>\<^sub>GT2\<in>{span of}T" by auto
      }
      moreover
      {
        assume AA:"TT1\<noteq>0"
        have "T1\<ra>\<^sub>GT2=\<Sum>[TT1+TT2;{{\<langle>\<langle>0,x\<rangle>,AA1`x\<rangle>. x\<in>T}\<union>{\<langle>\<langle>1,x\<rangle>,AA2`x\<rangle>. x\<in>T},{\<langle>\<langle>0,x\<rangle>,id(T)`x\<rangle>. x\<in>T}\<union>{\<langle>\<langle>1,x\<rangle>,id(T)`x\<rangle>. x\<in>T}}]" using linComb_sum[OF T(3,4) idG idG 
          AA T(1,2)] T(5,6) by auto
        also have "\<dots>=\<Sum>[TT1+TT2;{{\<langle>\<langle>0,x\<rangle>,AA1`x\<rangle>. x\<in>T}\<union>{\<langle>\<langle>1,x\<rangle>,AA2`x\<rangle>. x\<in>T},{\<langle>\<langle>0,x\<rangle>,x\<rangle>. x\<in>T}\<union>{\<langle>\<langle>1,x\<rangle>,x\<rangle>. x\<in>T}}]" by auto
        ultimately have eq:"T1\<ra>\<^sub>GT2=\<Sum>[TT1+TT2;{{\<langle>\<langle>0,x\<rangle>,AA1`x\<rangle>. x\<in>T}\<union>{\<langle>\<langle>1,x\<rangle>,AA2`x\<rangle>. x\<in>T},{\<langle>\<langle>0,x\<rangle>,x\<rangle>. x\<in>T}\<union>{\<langle>\<langle>1,x\<rangle>,x\<rangle>. x\<in>T}}]" by auto
        from T(1,2) obtain n1 n2 where fin:"TT1\<approx>n1" "n1\<in>nat" "TT2\<approx>n2" "n2\<in>nat" unfolding FinPow_def Finite_def by auto
        then have "n1+n2\<approx>n1#+n2" using nat_sum_eqpoll_sum by auto moreover
        with fin(1,3) have "TT1+TT2\<approx>n1#+n2" using sum_eqpoll_cong[] eqpoll_trans[of "TT1+TT2" "n1+n2" "n1#+n2"] by auto
        then have "Finite(TT1+TT2)" unfolding Finite_def using add_type by auto
        then have fin:"TT1+TT2\<in>FinPow(T+T)" using T(1,2) unfolding FinPow_def by auto moreover
        have f1:"{\<langle>\<langle>0, x\<rangle>, AA1 ` x\<rangle> . x \<in> T}:{0}\<times>T\<rightarrow>R" using apply_type[OF T(3)] unfolding Pi_def function_def by auto
        have f2:"{\<langle>\<langle>1, x\<rangle>, AA2 ` x\<rangle> . x \<in> T}:{1}\<times>T\<rightarrow>R" using apply_type[OF T(4)] unfolding Pi_def function_def by auto
        have "({0}\<times>T)\<inter>({1}\<times>T)=0" by auto
        then have ffA:"({\<langle>\<langle>0, x\<rangle>, AA1 ` x\<rangle> . x \<in> T} \<union> {\<langle>\<langle>1, x\<rangle>, AA2 ` x\<rangle> . x \<in> T}):T+T\<rightarrow>R" unfolding sum_def using fun_disjoint_Un[OF f1 f2] by auto moreover
        have f1:"{\<langle>\<langle>0, x\<rangle>, x\<rangle> . x \<in> T}:{0}\<times>T\<rightarrow>G" using assms unfolding Pi_def function_def by blast
        have f2:"{\<langle>\<langle>1, x\<rangle>, x\<rangle> . x \<in> T}:{1}\<times>T\<rightarrow>G" using assms unfolding Pi_def function_def by blast
        have f1T:"{\<langle>\<langle>0, x\<rangle>, x\<rangle> . x \<in> T}:{0}\<times>T\<rightarrow>T" using assms unfolding Pi_def function_def by blast
        have f2T:"{\<langle>\<langle>1, x\<rangle>, x\<rangle> . x \<in> T}:{1}\<times>T\<rightarrow>T" using assms unfolding Pi_def function_def by blast
        have "({0}\<times>T)\<inter>({1}\<times>T)=0" by auto
        then have ffB:"({\<langle>\<langle>0, x\<rangle>, x\<rangle> . x \<in> T} \<union> {\<langle>\<langle>1, x\<rangle>, x\<rangle> . x \<in>T}):T+T\<rightarrow>G" and ffBT:"({\<langle>\<langle>0, x\<rangle>, x\<rangle> . x \<in> T} \<union> {\<langle>\<langle>1, x\<rangle>, x\<rangle> . x \<in>T}):T+T\<rightarrow>T" unfolding sum_def using fun_disjoint_Un[OF f1 f2]
          using fun_disjoint_Un[OF f1T f2T] by auto
        obtain AA where AA:"\<Sum>[TT1+TT2;{{\<langle>\<langle>0,x\<rangle>,AA1`x\<rangle>. x\<in>T}\<union>{\<langle>\<langle>1,x\<rangle>,AA2`x\<rangle>. x\<in>T},{\<langle>\<langle>0,x\<rangle>,x\<rangle>. x\<in>T}\<union>{\<langle>\<langle>1,x\<rangle>,x\<rangle>. x\<in>T}}]=
          \<Sum>[({\<langle>\<langle>0,x\<rangle>,x\<rangle>. x\<in>T}\<union>{\<langle>\<langle>1,x\<rangle>,x\<rangle>. x\<in>T})``(TT1+TT2);{AA,id(G)}]" "AA:G\<rightarrow>R" "\<forall>x\<in>G-({\<langle>\<langle>0,x\<rangle>,x\<rangle>. x\<in>T}\<union>{\<langle>\<langle>1,x\<rangle>,x\<rangle>. x\<in>T})``(TT1+TT2). AA`x=\<zero>\<^sub>R" 
          using index_module[OF ffA ffB fin] by auto
        from ffBT have sub:"({\<langle>\<langle>0,x\<rangle>,x\<rangle>. x\<in>T}\<union>{\<langle>\<langle>1,x\<rangle>,x\<rangle>. x\<in>T})``(TT1+TT2)\<subseteq>T" using func1_1_L6(2) by auto
        then have finpow:"({\<langle>\<langle>0,x\<rangle>,x\<rangle>. x\<in>T}\<union>{\<langle>\<langle>1,x\<rangle>,x\<rangle>. x\<in>T})``(TT1+TT2)\<in>FinPow(T)" using fin Finite_RepFun[of "TT1+TT2" "\<lambda>t. ({\<langle>\<langle>0,x\<rangle>,x\<rangle>. x\<in>T}\<union>{\<langle>\<langle>1,x\<rangle>,x\<rangle>. x\<in>T})`t"] 
          func_imagedef[OF ffBT, of "TT1+TT2"] unfolding FinPow_def by auto
        {
          fix R T assume "R\<in>Pow(T)"
          then have "id(R)\<subseteq>R*T" using func1_1_L1B[OF id_type] by auto
          then have "id(R)=restrict(id(T),R)" using right_comp_id_any[of "id(T)"] using left_comp_id[of "id(R)" R T] by force
        }
        then have reg:"\<forall>T. \<forall>R\<in>Pow(T). id(R)=restrict(id(T),R)" by blast
        then have "\<Sum>[({\<langle>\<langle>0,x\<rangle>,x\<rangle>. x\<in>T}\<union>{\<langle>\<langle>1,x\<rangle>,x\<rangle>. x\<in>T})``(TT1+TT2);{restrict(AA,T),id(T)}]=
          \<Sum>[({\<langle>\<langle>0,x\<rangle>,x\<rangle>. x\<in>T}\<union>{\<langle>\<langle>1,x\<rangle>,x\<rangle>. x\<in>T})``(TT1+TT2);{restrict(restrict(AA,T),({\<langle>\<langle>0,x\<rangle>,x\<rangle>. x\<in>T}\<union>{\<langle>\<langle>1,x\<rangle>,x\<rangle>. x\<in>T})``(TT1+TT2)),id(({\<langle>\<langle>0,x\<rangle>,x\<rangle>. x\<in>T}\<union>{\<langle>\<langle>1,x\<rangle>,x\<rangle>. x\<in>T})``(TT1+TT2))}]"
          using linComb_restrict_coord[OF restrict_fun[OF AA(2) assms] func1_1_L1B[OF id_type assms] finpow] sub by auto moreover
        from sub have " T \<inter> ({\<langle>\<langle>0, x\<rangle>, x\<rangle> . x \<in> T} \<union> {\<langle>\<langle>1, x\<rangle>, x\<rangle> . x \<in> T}) `` (TT1 + TT2)=({\<langle>\<langle>0, x\<rangle>, x\<rangle> . x \<in> T} \<union> {\<langle>\<langle>1, x\<rangle>, x\<rangle> . x \<in> T}) `` (TT1 + TT2)" by auto
        then have "restrict(restrict(AA,T),({\<langle>\<langle>0,x\<rangle>,x\<rangle>. x\<in>T}\<union>{\<langle>\<langle>1,x\<rangle>,x\<rangle>. x\<in>T})``(TT1+TT2))=restrict(AA,({\<langle>\<langle>0,x\<rangle>,x\<rangle>. x\<in>T}\<union>{\<langle>\<langle>1,x\<rangle>,x\<rangle>. x\<in>T})``(TT1+TT2))"
          using restrict_restrict[of AA T "({\<langle>\<langle>0,x\<rangle>,x\<rangle>. x\<in>T}\<union>{\<langle>\<langle>1,x\<rangle>,x\<rangle>. x\<in>T})``(TT1+TT2)"] by auto
        ultimately have "\<Sum>[({\<langle>\<langle>0,x\<rangle>,x\<rangle>. x\<in>T}\<union>{\<langle>\<langle>1,x\<rangle>,x\<rangle>. x\<in>T})``(TT1+TT2);{restrict(AA,T),id(T)}]=
          \<Sum>[({\<langle>\<langle>0,x\<rangle>,x\<rangle>. x\<in>T}\<union>{\<langle>\<langle>1,x\<rangle>,x\<rangle>. x\<in>T})``(TT1+TT2);{restrict(AA,({\<langle>\<langle>0,x\<rangle>,x\<rangle>. x\<in>T}\<union>{\<langle>\<langle>1,x\<rangle>,x\<rangle>. x\<in>T})``(TT1+TT2)),id(({\<langle>\<langle>0,x\<rangle>,x\<rangle>. x\<in>T}\<union>{\<langle>\<langle>1,x\<rangle>,x\<rangle>. x\<in>T})``(TT1+TT2))}]" by auto
        moreover have "({\<langle>\<langle>0,x\<rangle>,x\<rangle>. x\<in>T}\<union>{\<langle>\<langle>1,x\<rangle>,x\<rangle>. x\<in>T})``(TT1+TT2)\<subseteq>G" using sub assms by auto
        with reg have "id(({\<langle>\<langle>0,x\<rangle>,x\<rangle>. x\<in>T}\<union>{\<langle>\<langle>1,x\<rangle>,x\<rangle>. x\<in>T})``(TT1+TT2))=restrict(id(G),({\<langle>\<langle>0,x\<rangle>,x\<rangle>. x\<in>T}\<union>{\<langle>\<langle>1,x\<rangle>,x\<rangle>. x\<in>T})``(TT1+TT2))" by auto
        ultimately have "\<Sum>[({\<langle>\<langle>0,x\<rangle>,x\<rangle>. x\<in>T}\<union>{\<langle>\<langle>1,x\<rangle>,x\<rangle>. x\<in>T})``(TT1+TT2);{restrict(AA,T),id(T)}]=
          \<Sum>[({\<langle>\<langle>0,x\<rangle>,x\<rangle>. x\<in>T}\<union>{\<langle>\<langle>1,x\<rangle>,x\<rangle>. x\<in>T})``(TT1+TT2);{restrict(AA,({\<langle>\<langle>0,x\<rangle>,x\<rangle>. x\<in>T}\<union>{\<langle>\<langle>1,x\<rangle>,x\<rangle>. x\<in>T})``(TT1+TT2)),restrict(id(G),({\<langle>\<langle>0,x\<rangle>,x\<rangle>. x\<in>T}\<union>{\<langle>\<langle>1,x\<rangle>,x\<rangle>. x\<in>T})``(TT1+TT2))}]"
          by auto
        also have "\<dots>=\<Sum>[({\<langle>\<langle>0,x\<rangle>,x\<rangle>. x\<in>T}\<union>{\<langle>\<langle>1,x\<rangle>,x\<rangle>. x\<in>T})``(TT1+TT2);{AA,id(G)}]" using linComb_restrict_coord[OF AA(2) id_type, of "({\<langle>\<langle>0,x\<rangle>,x\<rangle>. x\<in>T}\<union>{\<langle>\<langle>1,x\<rangle>,x\<rangle>. x\<in>T})``(TT1+TT2)"] 
          finpow unfolding FinPow_def using assms by force
        ultimately have eq1:"\<Sum>[({\<langle>\<langle>0,x\<rangle>,x\<rangle>. x\<in>T}\<union>{\<langle>\<langle>1,x\<rangle>,x\<rangle>. x\<in>T})``(TT1+TT2);{restrict(AA,T),id(T)}]=
          \<Sum>[({\<langle>\<langle>0,x\<rangle>,x\<rangle>. x\<in>T}\<union>{\<langle>\<langle>1,x\<rangle>,x\<rangle>. x\<in>T})``(TT1+TT2);{AA,id(G)}]" by auto
        have "restrict(AA,T):T\<rightarrow>R" using restrict_fun[OF AA(2) assms]. moreover
        note finpow moreover
        {
          fix x assume x:"x\<in>T-({\<langle>\<langle>0,x\<rangle>,x\<rangle>. x\<in>T}\<union>{\<langle>\<langle>1,x\<rangle>,x\<rangle>. x\<in>T})``(TT1+TT2)"
          with assms have "x\<in>G-({\<langle>\<langle>0,x\<rangle>,x\<rangle>. x\<in>T}\<union>{\<langle>\<langle>1,x\<rangle>,x\<rangle>. x\<in>T})``(TT1+TT2)" by auto
          with AA(3) have "AA`x=\<zero>\<^sub>R" by auto
          with x have "restrict(AA,T)`x=\<zero>\<^sub>R" using restrict by auto
        }
        then have "\<forall>x\<in>T-({\<langle>\<langle>0,x\<rangle>,x\<rangle>. x\<in>T}\<union>{\<langle>\<langle>1,x\<rangle>,x\<rangle>. x\<in>T})``(TT1+TT2). restrict(AA,T)`x=\<zero>\<^sub>R" by auto ultimately
        have "\<langle>({\<langle>\<langle>0,x\<rangle>,x\<rangle>. x\<in>T}\<union>{\<langle>\<langle>1,x\<rangle>,x\<rangle>. x\<in>T})``(TT1+TT2),restrict(AA,T)\<rangle>\<in>{\<langle>F,E\<rangle>\<in>FinPow(T)\<times>(T\<rightarrow>R). \<forall>x\<in>T-F. E`x=\<zero>\<^sub>R}" by auto
        then have "\<exists>F\<in>FinPow(T). \<exists>E\<in>T\<rightarrow>R. (\<forall>x\<in>T-F. E`x=\<zero>\<^sub>R) \<and> (\<Sum>[({\<langle>\<langle>0,x\<rangle>,x\<rangle>. x\<in>T}\<union>{\<langle>\<langle>1,x\<rangle>,x\<rangle>. x\<in>T})``(TT1+TT2);{restrict(AA,T),id(T)}]=\<Sum>[F;{E,id(T)}])"
          using exI[of "\<lambda>F. F\<in>FinPow(T) \<and> (\<exists>E\<in>T\<rightarrow>R. (\<forall>x\<in>T-F. E`x=\<zero>\<^sub>R) \<and> (\<Sum>[({\<langle>\<langle>0,x\<rangle>,x\<rangle>. x\<in>T}\<union>{\<langle>\<langle>1,x\<rangle>,x\<rangle>. x\<in>T})``(TT1+TT2);{restrict(AA,T),id(T)}]=\<Sum>[F;{E,id(T)}]))" "({\<langle>\<langle>0,x\<rangle>,x\<rangle>. x\<in>T}\<union>{\<langle>\<langle>1,x\<rangle>,x\<rangle>. x\<in>T})``(TT1+TT2)"]
          exI[of "\<lambda>E. E\<in>T\<rightarrow>R \<and> ((\<forall>x\<in>T-(({\<langle>\<langle>0,x\<rangle>,x\<rangle>. x\<in>T}\<union>{\<langle>\<langle>1,x\<rangle>,x\<rangle>. x\<in>T})``(TT1+TT2)). E`x=\<zero>\<^sub>R) \<and> (\<Sum>[({\<langle>\<langle>0,x\<rangle>,x\<rangle>. x\<in>T}\<union>{\<langle>\<langle>1,x\<rangle>,x\<rangle>. x\<in>T})``(TT1+TT2);{restrict(AA,T),id(T)}]=\<Sum>[({\<langle>\<langle>0,x\<rangle>,x\<rangle>. x\<in>T}\<union>{\<langle>\<langle>1,x\<rangle>,x\<rangle>. x\<in>T})``(TT1+TT2);{E,id(T)}]))"
            "restrict(AA,T)"] by auto
        then have "\<Sum>[({\<langle>\<langle>0,x\<rangle>,x\<rangle>. x\<in>T}\<union>{\<langle>\<langle>1,x\<rangle>,x\<rangle>. x\<in>T})``(TT1+TT2);{restrict(AA,T),id(T)}]\<in>{\<Sum>[FF;{AA,id(T)}]. 
          \<langle>FF,AA\<rangle> \<in> {\<langle>F,E\<rangle>\<in>FinPow(T)\<times>(T\<rightarrow>R). \<forall>x\<in>T-F. E`x=\<zero>\<^sub>R}}" by auto
        with eq1 have "\<Sum>[({\<langle>\<langle>0,x\<rangle>,x\<rangle>. x\<in>T}\<union>{\<langle>\<langle>1,x\<rangle>,x\<rangle>. x\<in>T})``(TT1+TT2);{AA,id(G)}]\<in>{span of}T" using A unfolding Span_def[OF assms]
          by auto
        with AA(1) eq have "T1\<ra>\<^sub>GT2\<in>{span of}T" by auto
      }
      ultimately have "T1\<ra>\<^sub>GT2\<in>{span of}T" by auto
    }
    then have "\<forall>x\<in>{span of}T. \<forall>y\<in>{span of}T. x\<ra>\<^sub>Gy\<in>{span of}T" by blast
    then have "({span of}T){is closed under}f"  unfolding IsOpClosed_def by auto moreover
    {
      fix r TT assume "r\<in>R" "TT\<in>{span of}T"
      with A obtain n AA where T:"r\<in>R" "TT=\<Sum>[n;{AA,id(T)}]" "n\<in>FinPow(T)" "AA:T\<rightarrow>R" "\<forall>x\<in>T-n. AA`x=\<zero>\<^sub>R"
        unfolding Span_def[OF assms(1)] by auto
      have "r\<cdot>\<^sub>M(TT)=\<Sum>[n;{{\<langle>t,r\<cdot>\<^sub>R(AA`t)\<rangle>.t\<in>T},id(T)}]" using linComb_action(1)[OF T(4) _ T(1) T(3), of "id(T)"] T(2)
        func1_1_L1B[OF id_type assms] by auto moreover
      have fun:"{\<langle>t,r\<cdot>\<^sub>R(AA`t)\<rangle>.t\<in>T}:T\<rightarrow>R" using linComb_action(2)[OF T(4) _ T(1,3)] func1_1_L1B[OF id_type assms] by auto
        moreover
      {
        fix z assume z:"z\<in>T-n"
        then have "{\<langle>t,r\<cdot>\<^sub>R(AA`t)\<rangle>.t\<in>T}`z=r\<cdot>\<^sub>R(AA`z)" using apply_equality[of z "r\<cdot>\<^sub>R(AA`z)"
          "{\<langle>t,r\<cdot>\<^sub>R(AA`t)\<rangle>.t\<in>T}" T "\<lambda>t. R"] using fun by auto
        also have "\<dots>=r\<cdot>\<^sub>R\<zero>\<^sub>R" using T(5) z by auto
        also have "\<dots>=\<zero>\<^sub>R" using ring.Ring_ZF_1_L6(2)[OF T(1)] by auto
        ultimately have "{\<langle>t,r\<cdot>\<^sub>R(AA`t)\<rangle>.t\<in>T}`z=\<zero>\<^sub>R" by auto
      }
      then have "\<forall>z\<in>T-n. {\<langle>t,r\<cdot>\<^sub>R(AA`t)\<rangle>.t\<in>T}`z=\<zero>\<^sub>R" by auto ultimately
      have "r\<cdot>\<^sub>M(TT)\<in>{span of}T" unfolding Span_def[OF assms(1)] using A T(3) by auto
    }
    then have "\<forall>r\<in>R. \<forall>TT\<in>{span of}T. r\<cdot>\<^sub>M(TT)\<in>{span of}T" by blast
    ultimately have "IsAsubmodule({span of}T)" "T\<subseteq>({span of}T)" using submoduleI by auto
  }
  ultimately show "IsAsubmodule({span of}T)" "T\<subseteq>({span of}T)" by auto
qed

text\<open>Given a linear combination, it is in the span of the image of the second function.\<close>

lemma (in module0) linear_comb_span:
  assumes "AA:X\<rightarrow>R" "B:X\<rightarrow>G" "D\<in>FinPow(X)"
  shows "\<Sum>[D;{AA,B}]\<in>({span of}(B``D))"
proof-
  {
    assume A:"B``D=0"
    {
      assume "D\<noteq>0"
      then obtain d where "d\<in>D" by auto
      then have "B`d\<in>B``D" using image_fun[OF assms(2)] assms(3) unfolding FinPow_def by auto
      with A have "False" by auto
    }
    then have "D=0" by auto
    then have "\<Sum>[D;{AA,B}]=\<zero>\<^sub>G" using LinearComb_def[OF assms] by auto moreover
    with A have ?thesis using Span_def by auto
  }
  moreover
  {
    assume A:"B``D\<noteq>0"
    have sub:"B``D\<subseteq>G" using assms(2) func1_1_L6(2) by auto
    from assms obtain AB where AA:"\<Sum>[D;{AA,B}]=\<Sum>[B``D;{AB,id(G)}]" "AB:G\<rightarrow>R" "\<forall>x\<in>G-B``D. AB`x=\<zero>\<^sub>R"
      using index_module by blast
    have fin:"Finite(B``D)" using func_imagedef[OF assms(2)] assms(3) unfolding FinPow_def
      using Finite_RepFun[of D "\<lambda>t. B`t"] by auto
    with sub have finpow:"B``D\<in>FinPow(G)" unfolding FinPow_def by auto
    with AA(1) have "\<Sum>[D;{AA,B}]=\<Sum>[B``D;{restrict(AB,B``D),restrict(id(G),B``D)}]"
      using linComb_restrict_coord AA(2) id_type by auto
    moreover have "restrict(id(G),B``D)=id(G) O id(B``D)" using right_comp_id_any by auto
    then have "restrict(id(G),B``D)=id(B``D)" using left_comp_id[of "id(B``D)"] sub by auto
    ultimately have "\<Sum>[D;{AA,B}]=\<Sum>[B``D;{restrict(AB,B``D),id(B``D)}]" by auto moreover
    have "restrict(AB,B``D):B``D\<rightarrow>R" using AA(2) restrict_fun sub by auto moreover
    have "\<forall>x\<in>B``D-B``D. restrict(AB,B``D)`x=\<zero>\<^sub>R" by auto ultimately
    have "\<Sum>[D;{AA,B}]\<in>{span of}(B``D)" using fin A unfolding Span_def[OF sub] FinPow_def by auto
  }
  ultimately show ?thesis by blast
qed

text\<open>It turns out that the span is the smallest submodule that contains the
original set.\<close>

theorem(in module0) linear_ind_set_comb_submodule2:
  assumes "T\<subseteq>H" "IsAsubmodule(H)"
  shows "({span of}T)\<subseteq>H"
proof-
  have as:"T\<subseteq>G" using assms(1) ab_group.group0_3_L2[OF sumodule_is_subgroup[OF assms(2)]] by auto 
  {
    assume A:"T=0"
    {
      fix x assume "x\<in>{span of}T"
      with A have "x=\<zero>\<^sub>G" using Span_def[OF as] by auto
      then have "x\<in>H" using assms(2) unfolding IsAsubmodule_def
        using ab_group.group0_3_L5 by auto
    }
    then have "({span of}T)\<subseteq>H" by auto
  }
  moreover
  {
    assume A:"T\<noteq>0"
    {
      fix x assume "x\<in>{span of}T"
      with A obtain n AA where "x=\<Sum>[n;{AA,id(T)}]" "n\<in>FinPow(T)" "AA:T\<rightarrow>R"
        unfolding Span_def[OF as] by auto
      then have x:"x=\<Sum>[n;{AA,id(T)}]" "n\<in>FinPow(T)" "AA:T\<rightarrow>R" "id(T):T\<rightarrow>H"
        using assms(1) func1_1_L1B id_type[of T] by auto
      then have "x\<in>H" using linear_comb_submod assms(2) by auto
    }
    then have "({span of}T)\<subseteq>H" by auto
  }
  ultimately show "({span of}T)\<subseteq>H" by auto
qed

corollary(in module0) span_mono:
  assumes "T\<subseteq>D" "D\<subseteq>G"
  shows "({span of}T) \<subseteq> ({span of}D)"
proof-
  from assms(2) have "D\<subseteq>({span of}D)" "IsAsubmodule({span of}D)" using linear_ind_set_comb_submodule by auto
  with assms(1) have "T\<subseteq>({span of}D)" "IsAsubmodule({span of}D)" by auto
  then show ?thesis using linear_ind_set_comb_submodule2 by auto
qed

text\<open>A basis can be defined as a spanning set without
redundancies; i.e., linearly independent.\<close>

definition(in module0)
  IsBasis ("_{is a basis}" 89)
  where "T\<subseteq>G \<Longrightarrow> T{is a basis} \<equiv> T{is linearly independent} \<and> ({span of}T)=G"

text\<open>Also, the union of submodules is not a submodule,
but the span of the union is the smallest submodule that contains it.
We define this as the sum of submodules.\<close>

definition(in module0)
  SumModules ("{+\<^sub>M}_" 80)
  where "\<forall>U\<in>\<FF>. IsAsubmodule(U) \<Longrightarrow> {+\<^sub>M}\<FF> \<equiv> {span of}(\<Union>\<FF>)"

text\<open>It can happen that the action of $R$ onto the module
gives the neutral element without $r\in R$ being a zero divisor.\<close>

definition(in module0)
  TorsionEle ("_{is a torsion element}" 98)
  where "m\<in>G \<Longrightarrow> m{is a torsion element} \<equiv> (\<exists>r\<in>R. r\<cdot>\<^sub>Mm=\<zero>\<^sub>G \<and> (\<forall>rr\<in>R. r\<cdot>\<^sub>Rrr=\<zero>\<^sub>R \<longrightarrow> rr=\<zero>\<^sub>R))"

text\<open>In case the multiplication of the ring is commutative, we can assure that
this elements form a submodule.\<close>

theorem(in module0) comm_ring_torsion_subm:
  assumes "M{is commutative on}R"
  shows "IsAsubmodule({m\<in>G. m{is a torsion element}})"
proof(rule submoduleI)
  show "{m\<in>G. m{is a torsion element}}\<subseteq>G" by auto
  have "\<zero>\<^sub>G\<in>G" using ab_group.group0_2_L2 by auto moreover
  {
    fix rr assume "rr\<in>R"
    then have "\<one>\<^sub>R\<cdot>\<^sub>Rrr=rr" using ring.Ring_ZF_1_L3(6) by auto
  }
  then have "\<forall>rr\<in>R. \<one>\<^sub>R\<cdot>\<^sub>Rrr=\<zero>\<^sub>R \<longrightarrow> rr=\<zero>\<^sub>R" by auto moreover
  have "\<one>\<^sub>R\<cdot>\<^sub>M\<zero>\<^sub>G=\<zero>\<^sub>G" "\<one>\<^sub>R\<in>R" using mult_zeroG ring.Ring_ZF_1_L2(2) by auto
  ultimately have "\<zero>\<^sub>G\<in>{m\<in>G. m{is a torsion element}}" using ring.Ring_ZF_1_L2(1) TorsionEle_def by auto
  then show "{m\<in>G. m{is a torsion element}}\<noteq>0" by auto
  {
    fix m1 m2 assume "m1\<in>{m\<in>G. m{is a torsion element}}" "m2\<in>{m\<in>G. m{is a torsion element}}"
    then have m:"m1\<in>G" "m2\<in>G" "\<exists>r\<in>R. r\<cdot>\<^sub>Mm1=\<zero>\<^sub>G \<and> (\<forall>rr\<in>R. r\<cdot>\<^sub>Rrr=\<zero>\<^sub>R \<longrightarrow> rr=\<zero>\<^sub>R)" "\<exists>r\<in>R. r\<cdot>\<^sub>Mm2=\<zero>\<^sub>G \<and> (\<forall>rr\<in>R. r\<cdot>\<^sub>Rrr=\<zero>\<^sub>R \<longrightarrow> rr=\<zero>\<^sub>R)"
      using TorsionEle_def by auto
    then obtain r1 r2 where r:"r1\<in>R" "r1\<cdot>\<^sub>Mm1=\<zero>\<^sub>G" "r2\<in>R" "r2\<cdot>\<^sub>Mm2=\<zero>\<^sub>G" "\<forall>rr\<in>R. r1\<cdot>\<^sub>Rrr=\<zero>\<^sub>R \<longrightarrow> rr=\<zero>\<^sub>R"
      "\<forall>rr\<in>R. r2\<cdot>\<^sub>Rrr=\<zero>\<^sub>R \<longrightarrow> rr=\<zero>\<^sub>R" by auto
    have "r1\<cdot>\<^sub>Rr2\<in>R" using r(1,3) ring.Ring_ZF_1_L4(3) by auto
    then have "S`(r1\<cdot>\<^sub>Rr2)\<in>End(G,f)" using S_fun apply_type by auto
    then have S:"S`(r1\<cdot>\<^sub>Rr2):G\<rightarrow>G" "Homomor(S`(r1\<cdot>\<^sub>Rr2),G,f,G,f)" unfolding End_def by auto
    then have "\<forall>g1\<in>G. \<forall>g2\<in>G. (S`(r1\<cdot>\<^sub>Rr2)) ` (f ` \<langle>g1, g2\<rangle>) = f ` \<langle>(S`(r1\<cdot>\<^sub>Rr2)) ` g1, (S`(r1\<cdot>\<^sub>Rr2)) ` g2\<rangle>" using Homomor_def[OF Ggroup Ggroup]
       by auto
    with m(1,2) have "(r1\<cdot>\<^sub>Rr2)\<cdot>\<^sub>M(m1\<ra>\<^sub>Gm2)=((r1\<cdot>\<^sub>Rr2)\<cdot>\<^sub>Mm1)\<ra>\<^sub>G((r1\<cdot>\<^sub>Rr2)\<cdot>\<^sub>Mm2)" by auto
    also have "\<dots>=((r1\<cdot>\<^sub>Rr2)\<cdot>\<^sub>Mm1)\<ra>\<^sub>G(r1\<cdot>\<^sub>M(r2\<cdot>\<^sub>Mm2))" using S_dist2 m(2) r(1,3) by auto
    also have "\<dots>=((r1\<cdot>\<^sub>Rr2)\<cdot>\<^sub>Mm1)\<ra>\<^sub>G(r1\<cdot>\<^sub>M\<zero>\<^sub>G)" using r(4) by auto
    also have "\<dots>=((r1\<cdot>\<^sub>Rr2)\<cdot>\<^sub>Mm1)\<ra>\<^sub>G\<zero>\<^sub>G" using mult_zeroG r(1) by auto
    also have "\<dots>=(r1\<cdot>\<^sub>Rr2)\<cdot>\<^sub>Mm1" using ab_group.group0_2_L2 m(1)
      apply_type[OF S(1)] by auto
    also have "\<dots>=(r2\<cdot>\<^sub>Rr1)\<cdot>\<^sub>Mm1" using assms unfolding IsCommutative_def using r(1,3) by auto
    also have "\<dots>=r2\<cdot>\<^sub>M(r1\<cdot>\<^sub>Mm1)" using S_dist2 m(1) r(1,3) by auto
    also have "\<dots>=r2\<cdot>\<^sub>M\<zero>\<^sub>G" using r(2) by auto
    also have "\<dots>=\<zero>\<^sub>G" using mult_zeroG r(3) by auto
    ultimately have "(r1\<cdot>\<^sub>Rr2)\<cdot>\<^sub>M(m1\<ra>\<^sub>Gm2)=\<zero>\<^sub>G" by auto
    moreover
    {
      fix rr assume rr:"rr\<in>R" "(r1\<cdot>\<^sub>Rr2)\<cdot>\<^sub>Rrr=\<zero>\<^sub>R"
      then have "r1\<cdot>\<^sub>R(r2\<cdot>\<^sub>Rrr)=\<zero>\<^sub>R" using ring.Ring_ZF_1_L11(2)
        r(1,3) by auto
      with r(5,3) rr(1) have "(r2\<cdot>\<^sub>Rrr)=\<zero>\<^sub>R" using ring.Ring_ZF_1_L4(3) by auto
      with r(6) rr(1) have "rr=\<zero>\<^sub>R" by auto
    }
    then have "\<forall>rr\<in>R. (r1\<cdot>\<^sub>Rr2)\<cdot>\<^sub>Rrr=\<zero>\<^sub>R \<longrightarrow> rr=\<zero>\<^sub>R" by auto
    ultimately have "\<exists>r\<in>R. r\<cdot>\<^sub>M(m1\<ra>\<^sub>Gm2)=\<zero>\<^sub>G \<and>(\<forall>rr\<in>R. r\<cdot>\<^sub>Rrr=\<zero>\<^sub>R \<longrightarrow> rr=\<zero>\<^sub>R)" using ring.Ring_ZF_1_L4(3)
      r(1,3) by auto
    then have "(m1\<ra>\<^sub>Gm2){is a torsion element}" using TorsionEle_def[OF ab_group.group_op_closed]
      m(1,2) by auto
    then have "(m1\<ra>\<^sub>Gm2)\<in>{m\<in>G. m{is a torsion element}}" using m(1,2) ab_group.group_op_closed by auto
  }
  then show "{m\<in>G. m{is a torsion element}}{is closed under} f" unfolding IsOpClosed_def by auto
  {
    fix r h assume "r\<in>R" "h\<in>{m\<in>G. m{is a torsion element}}"
    then have "r\<in>R" "h\<in>G" "\<exists>r\<in>R. r\<cdot>\<^sub>Mh=\<zero>\<^sub>G \<and>(\<forall>rr\<in>R. r\<cdot>\<^sub>Rrr=\<zero>\<^sub>R \<longrightarrow> rr=\<zero>\<^sub>R)" using TorsionEle_def
      by auto
    then obtain r2 where rh:"r\<in>R" "r2\<in>R" "h\<in>G" "r2\<cdot>\<^sub>Mh=\<zero>\<^sub>G" "(\<forall>rr\<in>R. r2\<cdot>\<^sub>Rrr=\<zero>\<^sub>R \<longrightarrow> rr=\<zero>\<^sub>R)" by auto
    have "r2\<cdot>\<^sub>M(r\<cdot>\<^sub>Mh)=(r2\<cdot>\<^sub>Rr)\<cdot>\<^sub>Mh" using S_dist2 rh(1-3) by auto
    also have "\<dots>=(r\<cdot>\<^sub>Rr2)\<cdot>\<^sub>Mh" using assms rh(1,2) unfolding IsCommutative_def by auto
    also have "\<dots>=r\<cdot>\<^sub>M(r2\<cdot>\<^sub>Mh)" using S_dist2 rh(1-3) by auto
    also have "\<dots>=r\<cdot>\<^sub>M\<zero>\<^sub>G" using rh(4) by auto
    also have "\<dots>=\<zero>\<^sub>G" using mult_zeroG rh(1) by auto
    ultimately have "r2\<cdot>\<^sub>M(r\<cdot>\<^sub>Mh)=\<zero>\<^sub>G" by auto
    with rh(2,5) have "\<exists>t\<in>R. t\<cdot>\<^sub>M(r\<cdot>\<^sub>Mh)=\<zero>\<^sub>G \<and>(\<forall>rr\<in>R. t\<cdot>\<^sub>Rrr=\<zero>\<^sub>R \<longrightarrow> rr=\<zero>\<^sub>R)" by auto
    moreover have "S`r\<in>End(G,f)" using S_fun apply_type rh(1) by auto
    then have "S`r:G\<rightarrow>G" unfolding End_def by auto
    with rh(3) have "(S`r)`h\<in>G" using apply_type by auto
    ultimately have "r\<cdot>\<^sub>Mh\<in>{m\<in>G. m{is a torsion element}}" using TorsionEle_def by auto
  }
  then show "\<forall>r\<in>R. \<forall>h\<in>Collect(G, TorsionEle). r \<cdot>\<^sub>M h \<in> Collect(G, TorsionEle)" by auto
qed

text\<open>A corollary that follows then is: if $R$ is commutative, then 
every irreducible module is its own torsion module or the only torsion element is
the neutral element.\<close>

corollary(in module0) irred_module_torsion_comm_ring:
  assumes "M{is commutative on}R" "{m\<in>G. m{is a torsion element}}\<noteq>G" "[G,f]{is irreducible for}[R,A,M|S]"
  shows "{m\<in>G. m{is a torsion element}}={\<zero>\<^sub>G}"
proof-
  from assms(1) have "IsAsubmodule({m\<in>G. m{is a torsion element}})" using comm_ring_torsion_subm
    by auto moreover
  with assms(2,3) show "{m\<in>G. m{is a torsion element}}={\<zero>\<^sub>G}"
    using Irr_def[OF isAmodule] by auto
qed


end
