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
EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE. *)

section \<open>Hyper numbers\<close>

theory UltraConstruction_ZF imports Ultrafilter_ZF EquivClass1
begin

text\<open>This theory deals with hyper numbers.\<close>

locale ultra = 
  fixes \<FF> and I
  assumes ultraFilter:"\<FF>{is an ultrafilter on}I"

begin

text\<open>We define an equivalence relation\<close>

definition hyper_rel where
"hyper_rel(X) \<equiv> {\<langle>f,g\<rangle>\<in>Pi(I,X)\<times>Pi(I,X). {n\<in>I. f`n = g`n}\<in>\<FF>}"

text\<open>The relation is reflexive\<close>

lemma hyper_refl:
  shows "refl(Pi(I,X),hyper_rel(X))" unfolding refl_def
proof-
  {
    fix x assume x:"x:Pi(I,X)"
    have "{n\<in>I. x`n = x`n} = I" by auto moreover
    have "I\<in>\<FF>" using ultraFilter unfolding IsUltrafilter_def IsFilter_def by auto
    ultimately have "{n\<in>I. x`n = x`n}\<in>\<FF>" by auto
    with x have "\<langle>x,x\<rangle>\<in>hyper_rel(X)" unfolding hyper_rel_def by auto
  }
  then show "\<forall>x\<in>Pi(I, X). \<langle>x, x\<rangle> \<in> hyper_rel(X)" by auto
qed

text\<open>The relation is symmetric\<close>

lemma hyper_sym:
  shows "sym(hyper_rel(X))" unfolding sym_def
proof(safe)
  fix x y assume "\<langle>x, y\<rangle> \<in> hyper_rel(X)"
  then have as:"x:Pi(I,X)" "y:Pi(I,X)" "{n\<in>I. x`n = y`n}\<in>\<FF>" unfolding hyper_rel_def by auto
  {
    fix n assume "n\<in>{n\<in>I. x`n = y`n}"
    then have "n\<in>I" "x`n=y`n" by auto
    then have "n\<in>{n\<in>I. y`n = x`n}" by auto
  } moreover
  {
    fix n assume "n\<in>{n\<in>I. y`n = x`n}"
    then have "n\<in>I" "y`n=x`n" by auto
    then have "n\<in>{n\<in>I. x`n = y`n}" by auto
  } ultimately
  have "{n\<in>I. y`n = x`n} = {n\<in>I. x`n = y`n}" by blast
  with as(3) have "{n\<in>I. y`n = x`n} :\<FF>" by auto
  with as(1,2) show "\<langle>y,x\<rangle>\<in>hyper_rel(X)" unfolding hyper_rel_def by auto
qed

text\<open>The relation is transitive\<close>

lemma hyper_trans:
  shows "trans(hyper_rel(X))" unfolding trans_def
proof(safe)
  fix x y z assume as:"\<langle>x, y\<rangle> \<in> hyper_rel(X)" "\<langle>y, z\<rangle> \<in> hyper_rel(X)"
  then have A:"x:Pi(I,X)" "z:Pi(I,X)" unfolding hyper_rel_def by auto
  {
    fix n assume "n\<in>{n\<in>I. x`n = y`n}\<inter>{n\<in>I. y`n = z`n}"
    then have "n\<in>{n\<in>I. x`n = z`n}" by auto
  }
  then have sub:"{n\<in>I. x`n = y`n}\<inter>{n\<in>I. y`n = z`n} \<subseteq> {n\<in>I. x`n = z`n}" by auto
  from as(1,2) have "{n\<in>I. x`n = y`n}\<inter>{n\<in>I. y`n = z`n}:\<FF>" using ultraFilter
    unfolding hyper_rel_def IsUltrafilter_def IsFilter_def by auto
  then have "\<forall>A\<in>Pow(I). {n\<in>I. x`n = y`n}\<inter>{n\<in>I. y`n = z`n} \<subseteq> A \<longrightarrow> A\<in>\<FF>"
    using ultraFilter unfolding IsUltrafilter_def IsFilter_def by auto
  moreover have "{n\<in>I. x`n = z`n}\<in>Pow(I)" by auto
  ultimately have "({n\<in>I. x`n = y`n}\<inter>{n\<in>I. y`n = z`n} \<subseteq> {n\<in>I. x`n = z`n}) \<longrightarrow> {n\<in>I. x`n = z`n}\<in>\<FF>"
    by auto
  with sub have "{n\<in>I. x`n = z`n}\<in>\<FF>" by auto
  with A show "\<langle>x, z\<rangle> \<in> hyper_rel(X)" unfolding hyper_rel_def by auto
qed

text\<open>The relation is an equivalence\<close>

lemma hyper_equiv:
  shows "equiv(Pi(I,X), hyper_rel(X))" unfolding equiv_def
  using hyper_refl hyper_sym hyper_trans apply auto
  unfolding hyper_rel_def by auto

definition hyper_set where
"hyper_set(X) \<equiv> Pi(I,X)// hyper_rel(X)"

lemma incl_inj:
  fixes Y
  defines "YY \<equiv> \<lambda>_. Y"
  defines "incl \<equiv> {\<langle>x,hyper_rel(YY)``{ConstantFunction(I,x)}\<rangle>. x\<in>Y}"
  shows "incl\<in>inj(Y,hyper_set(YY))" unfolding inj_def
proof(safe)
  {
    fix x assume x:"x:Y"
    then have "ConstantFunction(I,x):I\<rightarrow>Y" using func1_3_L1 by auto
    then have "hyper_rel(YY)``{ConstantFunction(I,x)}\<in>hyper_set(YY)" unfolding hyper_set_def
      quotient_def YY_def by auto
  }
  then have "\<forall>x\<in>Y. hyper_rel(YY)``{ConstantFunction(I,x)}\<in>hyper_set(YY)" by auto
  then show f:"incl:Y\<rightarrow>hyper_set(YY)" using ZF_fun_from_total unfolding incl_def by auto
  {
    fix w x assume as:"w:Y" "x:Y" "incl ` w = incl ` x"
    then have e:"hyper_rel(YY)``{ConstantFunction(I,w)} = hyper_rel(YY)``{ConstantFunction(I,x)}"
      using apply_equality[OF _ f] unfolding incl_def by auto
    from as(1,2) have c:"ConstantFunction(I,w):I\<rightarrow>Y" "ConstantFunction(I,x):I\<rightarrow>Y"
      using func1_3_L1 by auto
    with e have "\<langle>ConstantFunction(I,w),ConstantFunction(I,x)\<rangle>\<in>hyper_rel(YY)" using same_image_equiv[of "I\<rightarrow>Y" "hyper_rel(YY)"]
      hyper_equiv YY_def by auto
    then have "{n\<in>I. ConstantFunction(I,w)`n = ConstantFunction(I,x)`n}:\<FF>"
      unfolding hyper_rel_def by auto
    then have "{n\<in>I. w = x}:\<FF>" using func1_3_L2 by auto
    then show "w=x" using ultraFilter unfolding IsUltrafilter_def IsFilter_def by auto
  }
qed


lemma hyper_set_structure:
  assumes "\<forall>i\<in>I. P(i):X(i)\<times>X(i)\<rightarrow>X(i)"
  defines "Q \<equiv> {\<langle>\<langle>q1,q2\<rangle>,{\<langle>i,P(i)`\<langle>q1`i,q2`i\<rangle>\<rangle>. i\<in>I}\<rangle>. \<langle>q1,q2\<rangle>\<in>Pi(I,X)\<times>Pi(I,X)}"
  shows "Congruent2(hyper_rel(X), Q)" "Q:Pi(I,X)\<times>Pi(I,X) \<rightarrow> Pi(I,X)"
    "\<forall>i\<in>I. \<forall>x\<in>Pi(I,X). \<forall>y\<in>Pi(I,X). Q`\<langle>x,y\<rangle>`i = P(i)`\<langle>x`i,y`i\<rangle>"
  unfolding Congruent2_def hyper_rel_def apply safe apply auto
proof-
  {
    fix x y assume xy:"x\<in>Pi(I,X)" "y\<in>Pi(I,X)"
    {
      fix i assume i:"i:I"
      with xy have "x`i:X(i)" "y`i:X(i)" using apply_type by auto
      with assms(1) have "P(i)`\<langle>x`i,y`i\<rangle>\<in>X(i)" using apply_type i by auto
    }
    then have "{\<langle>i,P(i)`\<langle>x`i,y`i\<rangle>\<rangle>. i\<in>I}:Pi(I,X)"
      unfolding Pi_def function_def by auto
  }
  then have "\<forall>x\<in>Pi(I, X) \<times> Pi(I, X).
       (\<lambda>\<langle>q1,q2\<rangle>. {\<langle>i, P(i) ` \<langle>q1 ` i, q2 ` i\<rangle>\<rangle> . i \<in> I})(x) \<in> Pi(I, X)" by auto moreover
  have "Q={\<langle>x, (\<lambda>\<langle>q1,q2\<rangle>. {\<langle>i, P(i) ` \<langle>q1 ` i, q2 ` i\<rangle>\<rangle> . i \<in> I})(x)\<rangle> . x \<in> Pi(I, X) \<times> Pi(I, X)}"
    unfolding Q_def by force
  ultimately show qF:"Q:Pi(I,X)\<times>Pi(I,X)\<rightarrow>Pi(I,X)" unfolding Q_def 
    using ZF_fun_from_total[of "Pi(I,X)\<times>Pi(I,X)" "\<lambda>\<langle>q1,q2\<rangle>. {\<langle>i,P(i)`\<langle>q1`i,q2`i\<rangle>\<rangle>. i\<in>I}" "Pi(I,X)"]
    by auto
  then have "\<forall>x\<in>Pi(I,X). \<forall>y\<in>Pi(I,X). Q`\<langle>x,y\<rangle> = {\<langle>i,P(i)`\<langle>x`i,y`i\<rangle>\<rangle>. i\<in>I}"
    using apply_equality unfolding Q_def by auto moreover
  from qF have "\<forall>x\<in>Pi(I,X). \<forall>y\<in>Pi(I,X). Q`\<langle>x,y\<rangle>\<in>Pi(I,X)"
    using apply_type by auto ultimately
  have R:"\<forall>i\<in>I. \<forall>x\<in>Pi(I,X). \<forall>y\<in>Pi(I,X). Q`\<langle>x,y\<rangle>`i = P(i)`\<langle>x`i,y`i\<rangle>"
    using apply_equality[where A=I and B=X] by auto
  then show "\<And>i x y. i \<in> I \<Longrightarrow> x \<in> Pi(I, X) \<Longrightarrow> y \<in> Pi(I, X) \<Longrightarrow> Q ` \<langle>x, y\<rangle> ` i = P(i) ` \<langle>x ` i, y ` i\<rangle>" by auto
  fix x y z t
  assume as:"{n \<in> I . x ` n = y ` n} \<in> \<FF>"
       "x \<in> Pi(I,X)" "y \<in> Pi(I,X)" "{n \<in> I . z ` n = t ` n} \<in> \<FF>"
       "z \<in> Pi(I,X)" "t \<in> Pi(I,X)"
  from qF as(2,5) show "Q`\<langle>x,z\<rangle>:Pi(I,X)" using apply_type by auto
  from qF as(3,6) show "Q`\<langle>y,t\<rangle>:Pi(I,X)" using apply_type by auto
  {
    fix n assume "n\<in>{n \<in> I . x ` n = y ` n}\<inter>{n \<in> I . z ` n = t ` n}"
    then have "n\<in>I" "x ` n = y ` n" "z ` n = t ` n" by auto
    then have "P(n)`\<langle>x`n,z`n\<rangle> = P(n)`\<langle>y`n,t`n\<rangle>" by auto
    with `n\<in>I` have "n\<in>{n \<in> I . P(n)`\<langle>x`n,z`n\<rangle> = P(n)`\<langle>y`n,t`n\<rangle>}" by auto
  }
  then have "{n \<in> I . x ` n = y ` n}\<inter>{n \<in> I . z ` n = t ` n} \<subseteq> {n \<in> I . P(n)`\<langle>x`n,z`n\<rangle> = P(n)`\<langle>y`n,t`n\<rangle>}"
    by blast
  moreover from as(1,4) have "{n \<in> I . x ` n = y ` n}\<inter>{n \<in> I . z ` n = t ` n}:\<FF>"
    using ultraFilter unfolding IsUltrafilter_def IsFilter_def by auto
  then have "\<forall>A\<in>Pow(I). {n \<in> I . x ` n = y ` n}\<inter>{n \<in> I . z ` n = t ` n} \<subseteq> A \<longrightarrow> A:\<FF>"
    using ultraFilter unfolding IsUltrafilter_def IsFilter_def by auto
  then have "{n \<in> I . P(n)`\<langle>x`n,z`n\<rangle> = P(n)`\<langle>y`n,t`n\<rangle>}\<in>Pow(I) \<longrightarrow> (({n \<in> I . x ` n = y ` n}\<inter>{n \<in> I . z ` n = t ` n} \<subseteq> {n \<in> I . P(n)`\<langle>x`n,z`n\<rangle> = P(n)`\<langle>y`n,t`n\<rangle>}) \<longrightarrow> {n \<in> I . P(n)`\<langle>x`n,z`n\<rangle> = P(n)`\<langle>y`n,t`n\<rangle>}:\<FF>)"
    by auto
  then have "({n \<in> I . x ` n = y ` n}\<inter>{n \<in> I . z ` n = t ` n} \<subseteq> {n \<in> I . P(n)`\<langle>x`n,z`n\<rangle> = P(n)`\<langle>y`n,t`n\<rangle>}) \<longrightarrow> {n \<in> I . P(n)`\<langle>x`n,z`n\<rangle> = P(n)`\<langle>y`n,t`n\<rangle>}:\<FF>" by auto
  ultimately have "{n \<in> I . P(n)`\<langle>x`n,z`n\<rangle> = P(n)`\<langle>y`n,t`n\<rangle>}:\<FF>" by auto
  then show "{n \<in> I . Q`\<langle>x,z\<rangle>`n = Q`\<langle>y,t\<rangle>`n}:\<FF>"
    using R as(2,3,5,6) by auto
qed

subsection\<open>Internal sets\<close>

definition internal_set where
"S:Pi(I,\<lambda>i. Pow(Y(i))) \<Longrightarrow> internal_set(S,Y) \<equiv> {hyper_rel(Y)``{x}. x\<in>{x\<in>Pi(I,Y). {n\<in>I. x`n\<in>S`n}\<in>\<FF>}}"

lemma internal_subset:
  assumes "S:Pi(I,\<lambda>i. Pow(Y(i)))"
  shows "internal_set(S,Y) \<subseteq> hyper_set(Y)"
proof-
  {
    fix t assume "t\<in>internal_set(S,Y)"
    then have "t\<in>{hyper_rel(Y)``{x}. x\<in>{x\<in>Pi(I,Y). {n\<in>I. x`n\<in>S`n}\<in>\<FF>}}"
      unfolding internal_set_def[OF assms].
    then obtain q where q:"t=hyper_rel(Y)``{q}" "q:Pi(I,Y)" "{n\<in>I. q`n\<in>S`n}\<in>\<FF>"
      by auto
    from q(1,2) have "t\<in>hyper_set(Y)" unfolding hyper_set_def quotient_def by auto
  }
  then show "internal_set(S,Y) \<subseteq> hyper_set(Y)" by auto
qed

lemma internal_sub:
  assumes "S1:Pi(I,\<lambda>i. Pow(Y(i)))"  "S2:Pi(I,\<lambda>i. Pow(Y(i)))" "{n\<in>I. S1`n \<subseteq> S2`n}\<in>\<FF>"
  shows "internal_set(S1,Y) \<subseteq> internal_set(S2,Y)"
proof
  fix x assume "x\<in>internal_set(S1,Y)"
  then obtain xx where x:"xx\<in>Pi(I,Y)" "x=hyper_rel(Y)``{xx}" "{n\<in>I. xx`n\<in>S1`n}\<in>\<FF>"
    unfolding internal_set_def[OF assms(1)] by auto
  from x(3) assms(3) have "{n\<in>I. S1`n \<subseteq> S2`n}\<inter>{n\<in>I. xx`n\<in>S1`n}\<in>\<FF>" using ultraFilter
    unfolding IsFilter_def IsUltrafilter_def by auto
  moreover have "{n\<in>I. xx`n\<in>S2`n}\<in>Pow(I)" by auto
  moreover have "{n\<in>I. S1`n \<subseteq> S2`n}\<inter>{n\<in>I. xx`n\<in>S1`n} \<subseteq> {n\<in>I. xx`n\<in>S2`n}" by auto
  ultimately have "{n\<in>I. xx`n\<in>S2`n}\<in>\<FF>" using ultraFilter unfolding IsFilter_def IsUltrafilter_def
    by auto
  with x(1,2) show "x\<in>internal_set(S2,Y)" unfolding internal_set_def[OF assms(2)] by auto
qed

corollary internal_eq:
  assumes "S1:Pi(I,\<lambda>i. Pow(Y(i)))"  "S2:Pi(I,\<lambda>i. Pow(Y(i)))" "{n\<in>I. S1`n = S2`n}\<in>\<FF>"
  shows "internal_set(S1,Y) = internal_set(S2,Y)"
proof
  have "{n\<in>I. S1`n = S2`n} \<subseteq> {n\<in>I. S1`n \<subseteq> S2`n}" "{n\<in>I. S1`n = S2`n} \<subseteq> {n\<in>I. S2`n \<subseteq> S1`n}" by auto
  moreover have "{n\<in>I. S1`n \<subseteq> S2`n}:Pow(I)" "{n\<in>I. S2`n \<subseteq> S1`n}:Pow(I)" by auto
  moreover note assms(3) ultimately have A:"{n\<in>I. S1`n \<subseteq> S2`n}:\<FF>" "{n\<in>I. S2`n \<subseteq> S1`n}:\<FF>"
    using ultraFilter unfolding IsFilter_def IsUltrafilter_def by auto
  from A(1) show "internal_set(S1,Y) \<subseteq> internal_set(S2,Y)" using internal_sub[OF assms(1,2)] by auto
  from A(2) show "internal_set(S2,Y) \<subseteq> internal_set(S1,Y)" using internal_sub[OF assms(2,1)] by auto
qed

lemma internal_total_set:
  shows "internal_set({\<langle>i,X(i)\<rangle>. i\<in>I},X) = hyper_set(X)"
proof
  have f:"{\<langle>i,X(i)\<rangle>. i\<in>I}:Pi(I,\<lambda>i. Pow(X(i)))" unfolding Pi_def function_def by auto
  {
    fix t assume "t\<in>internal_set({\<langle>i,X(i)\<rangle>. i\<in>I},X)"
    then have "t\<in>{hyper_rel(X)``{x}. x\<in>{x\<in>Pi(I,X). {n\<in>I. x`n\<in>{\<langle>i,X(i)\<rangle>. i\<in>I}`n}\<in>\<FF>}}"
      unfolding internal_set_def[OF f].
    then obtain q where q:"t=hyper_rel(X)``{q}" "q:Pi(I,X)" "{n\<in>I. q`n\<in>{\<langle>i,X(i)\<rangle>. i\<in>I}`n}\<in>\<FF>"
      by auto
    from q(1,2) have "t\<in>hyper_set(X)" unfolding hyper_set_def quotient_def by auto
  }
  then show "internal_set({\<langle>i,X(i)\<rangle>. i\<in>I},X) \<subseteq> hyper_set(X)" by auto
  {
    fix t assume "t\<in>hyper_set(X)"
    then obtain q where q:"t=hyper_rel(X)``{q}" "q:Pi(I,X)" unfolding hyper_set_def
        quotient_def by auto
    from f have R:"\<forall>n\<in>I. {\<langle>i,X(i)\<rangle>. i\<in>I}`n = X(n)" using apply_equality by auto
    from q(2) have "\<forall>n\<in>I. q`n\<in>X(n)" using apply_type by auto
    then have "{n\<in>I. q`n\<in>X(n)} = I" by auto
    then have "{n\<in>I. q`n\<in>X(n)}\<in>\<FF>" using ultraFilter unfolding IsUltrafilter_def IsFilter_def
      by auto
    with R have "{n\<in>I. q`n\<in>{\<langle>i,X(i)\<rangle>. i\<in>I}`n}\<in>\<FF>" by auto
    with q(2) have "q\<in>{x\<in>Pi(I,X). {n\<in>I. x`n\<in>{\<langle>i,X(i)\<rangle>. i\<in>I}`n}\<in>\<FF>}" by auto
    with q(1) have "t\<in>{hyper_rel(X)``{x}. x\<in>{x\<in>Pi(I,X). {n\<in>I. x`n\<in>{\<langle>i,X(i)\<rangle>. i\<in>I}`n}\<in>\<FF>}}" by auto
    then have "t:internal_set({\<langle>i,X(i)\<rangle>. i\<in>I},X)" unfolding internal_set_def[OF f].
  }
  then show "hyper_set(X) \<subseteq> internal_set({\<langle>i,X(i)\<rangle>. i\<in>I},X)" by auto
qed

definition isInternal where
"isInternal(Y,X) \<equiv> \<exists>S\<in>Pi(I,\<lambda>i. Pow(X(i))). Y=internal_set(S,X)" 

corollary total_inter:
  shows "isInternal(hyper_set(X),X)"
proof-
  have "{\<langle>i,X(i)\<rangle>. i\<in>I}:Pi(I,\<lambda>i. Pow(X(i)))" unfolding Pi_def function_def by auto
  then show ?thesis unfolding isInternal_def using internal_total_set[THEN sym] by auto
qed

lemma internal_inter:
  assumes "isInternal(A,X)" "isInternal(B,X)"
  shows "isInternal(A\<inter>B,X)"
proof-
  from assms obtain SA SB where s:"SA:Pi(I,\<lambda>i. Pow(X(i)))" "SB:Pi(I,\<lambda>i. Pow(X(i)))" 
    "A=internal_set(SA,X)" "B=internal_set(SB,X)"
    unfolding isInternal_def by auto
  let ?S="{\<langle>n,(SA`n)\<inter>(SB`n)\<rangle>. n\<in>I}"
  from s(1,2) have "\<forall>n\<in>I. (SA`n)\<in>Pow(X(n))" "\<forall>n\<in>I. (SB`n)\<in>Pow(X(n))" using apply_type[of _ I "\<lambda>i. Pow(X(i))"]
    by auto
  then have "\<forall>n\<in>I. (SA`n)\<inter>(SB`n)\<in>Pow(X(n))" by auto
  then have f:"?S:Pi(I,\<lambda>i. Pow(X(i)))" unfolding Pi_def function_def by auto
  {
    fix t assume t:"t\<in>internal_set(?S,X)"
    then obtain x where x:"t=hyper_rel(X)``{x}" "x\<in>Pi(I,X)" "{n\<in>I. x`n\<in>?S`n}\<in>\<FF>"
      unfolding internal_set_def[OF f] by auto
    from x(3) have "{n\<in>I. x`n\<in>(SA`n)\<inter>(SB`n)}\<in>\<FF>"
      using apply_equality[OF _ f] by auto
    then have R:"\<forall>A\<in>Pow(I). {n\<in>I. x`n\<in>(SA`n)\<inter>(SB`n)} \<subseteq> A \<longrightarrow> A\<in>\<FF>"
      using ultraFilter unfolding IsFilter_def IsUltrafilter_def by auto
    moreover have "{n\<in>I. x`n\<in>SA`n}\<in>Pow(I)" by auto
    ultimately have "{n\<in>I. x`n\<in>(SA`n)\<inter>(SB`n)} \<subseteq> {n\<in>I. x`n\<in>SA`n} \<longrightarrow> {n\<in>I. x`n\<in>SA`n}\<in>\<FF>" by auto
    moreover have "{n\<in>I. x`n\<in>(SA`n)\<inter>(SB`n)} \<subseteq> {n\<in>I. x`n\<in>SA`n}" by auto
    ultimately have "{n\<in>I. x`n\<in>SA`n}\<in>\<FF>" by auto
    with x(1,2) have A:"t\<in>internal_set(SA,X)" unfolding internal_set_def[OF s(1)] by auto
    have "{n\<in>I. x`n\<in>SB`n}\<in>Pow(I)" by auto
    with R have "{n\<in>I. x`n\<in>(SA`n)\<inter>(SB`n)} \<subseteq> {n\<in>I. x`n\<in>SB`n} \<longrightarrow> {n\<in>I. x`n\<in>SB`n}\<in>\<FF>" by auto
    moreover have "{n\<in>I. x`n\<in>(SA`n)\<inter>(SB`n)} \<subseteq> {n\<in>I. x`n\<in>SB`n}" by auto
    ultimately have "{n\<in>I. x`n\<in>SB`n}\<in>\<FF>" by auto
    with x(1,2) have "t\<in>internal_set(SB,X)" unfolding internal_set_def[OF s(2)] by auto
    with A have "t\<in>A\<inter>B" using s(3,4) by auto
  }
  then have "internal_set(?S,X) \<subseteq> A\<inter>B" by auto moreover
  {
    fix t assume t:"t\<in>A\<inter>B"
    with s(3,4) obtain ta tb where t:"t=hyper_rel(X)``{ta}" "ta\<in>Pi(I,X)" "{n\<in>I. ta`n\<in>SA`n}\<in>\<FF>"
      "t=hyper_rel(X)``{tb}" "tb\<in>Pi(I,X)" "{n\<in>I. tb`n\<in>SB`n}\<in>\<FF>" unfolding internal_set_def[OF s(1)]
      internal_set_def[OF s(2)] by blast
    from t(1,4) have "hyper_rel(X)``{ta}=hyper_rel(X)``{tb}" by auto
    then have "\<langle>ta,tb\<rangle>\<in>hyper_rel(X)" using same_image_equiv[OF hyper_equiv] t(5) by auto
    then have "{n\<in>I. ta`n=tb`n}:\<FF>" unfolding hyper_rel_def by auto
    with t(3) have "{n\<in>I. ta`n=tb`n}\<inter>{n\<in>I. ta`n\<in>SA`n}:\<FF>" using ultraFilter
      unfolding IsFilter_def IsUltrafilter_def by auto
    with t(6) have "{n\<in>I. ta`n=tb`n}\<inter>{n\<in>I. ta`n\<in>SA`n}\<inter>{n\<in>I. tb`n\<in>SB`n}:\<FF>"
      using ultraFilter unfolding IsFilter_def IsUltrafilter_def by auto
    then have "\<forall>A\<in>Pow(I). {n\<in>I. ta`n=tb`n}\<inter>{n\<in>I. ta`n\<in>SA`n}\<inter>{n\<in>I. tb`n\<in>SB`n}\<subseteq>A \<longrightarrow> A:\<FF>"
      using ultraFilter unfolding IsFilter_def IsUltrafilter_def by auto
    moreover have "{n\<in>I. ta`n\<in>(SA`n)\<inter>SB`n} :Pow(I)" by auto
    ultimately have "{n\<in>I. ta`n=tb`n}\<inter>{n\<in>I. ta`n\<in>SA`n}\<inter>{n\<in>I. tb`n\<in>SB`n}\<subseteq>{n\<in>I. ta`n\<in>(SA`n)\<inter>SB`n} \<longrightarrow> {n\<in>I. ta`n\<in>(SA`n)\<inter>SB`n}:\<FF>"
      by auto
    then have "{n\<in>I. ta`n\<in>(SA`n)\<inter>SB`n}:\<FF>" by auto
    then have "{n\<in>I. ta`n\<in>{\<langle>n, SA ` n \<inter> SB ` n\<rangle> . n \<in> I}`n}:\<FF>"
      using apply_equality[OF _ f] by auto
    with t(1,2) have "t\<in>internal_set(?S,X)" unfolding internal_set_def[OF f] by auto
  }
  then have "A\<inter>B \<subseteq> internal_set(?S,X)" by auto
  ultimately have "A\<inter>B = internal_set(?S,X)" by auto
  then show ?thesis unfolding isInternal_def using f by auto
qed

text\<open>The complement of an internal set is internal\<close>

lemma complement_internal:
  assumes "isInternal(A,X)"
  shows "isInternal(hyper_set(X)-A,X)"
proof-
  from assms obtain SA where s:"SA:Pi(I,\<lambda>i. Pow(X(i)))"
    "A=internal_set(SA,X)" unfolding isInternal_def by auto
  let ?S="{\<langle>n,X(n)-(SA`n)\<rangle>. n\<in>I}"
  have "\<forall>n\<in>I. X(n)-(SA`n)\<in>Pow(X(n))" by auto
  then have f:"?S:Pi(I,\<lambda>i. Pow(X(i)))" unfolding Pi_def function_def by auto
  {
    fix t assume t:"t\<in>internal_set(?S,X)"
    then obtain x where x:"t=hyper_rel(X)``{x}" "x\<in>Pi(I,X)" "{n\<in>I. x`n\<in>?S`n}\<in>\<FF>"
      unfolding internal_set_def[OF f] by auto
    {
      assume "t\<in>internal_set(SA,X)"
      then obtain y where y:"t=hyper_rel(X)``{y}" "y\<in>Pi(I,X)" "{n\<in>I. y`n\<in>SA`n}\<in>\<FF>"
        unfolding internal_set_def[OF s(1)] by auto
      from x(1) y(1) have "\<langle>x,y\<rangle>\<in>hyper_rel(X)" using y(2) same_image_equiv
          hyper_equiv[of X] by auto
      then have "{n\<in>I. x`n = y`n}\<in>\<FF>" unfolding hyper_rel_def by auto
      with y(3) have "{n\<in>I. y`n\<in>SA`n}\<inter>{n\<in>I. x`n = y`n}\<in>\<FF>"
        using ultraFilter unfolding IsFilter_def IsUltrafilter_def by auto
      then have "\<And>A. A\<in>Pow(I) \<Longrightarrow> {n\<in>I. y`n\<in>SA`n}\<inter>{n\<in>I. x`n = y`n} \<subseteq> A \<Longrightarrow> A:\<FF>"
        using ultraFilter unfolding IsFilter_def IsUltrafilter_def by auto
      then have "{n\<in>I. x`n\<in>SA`n}\<in>Pow(I) \<Longrightarrow> {n\<in>I. y`n\<in>SA`n}\<inter>{n\<in>I. x`n = y`n} \<subseteq> {n\<in>I. x`n\<in>SA`n} \<Longrightarrow> {n\<in>I. x`n\<in>SA`n}:\<FF>" by auto
      moreover have "{n\<in>I. y`n\<in>SA`n}\<inter>{n\<in>I. x`n = y`n} \<subseteq> {n\<in>I. x`n\<in>SA`n}" by auto
      ultimately have "{n\<in>I. x`n\<in>SA`n}: \<FF>" by auto
      with x(3) have "{n\<in>I. x`n\<in>SA`n}\<inter>{n\<in>I. x`n\<in>X(n)-(SA`n)}\<in>\<FF>" using ultraFilter
        apply_equality[OF _ f]
        unfolding IsUltrafilter_def IsFilter_def by auto moreover
      {
        fix n assume n:"n\<in>{n\<in>I. x`n\<in>SA`n}\<inter>{n\<in>I. x`n\<in>X(n)-(SA`n)}"
        then have False by auto
      }
      then have "{n\<in>I. x`n\<in>SA`n}\<inter>{n\<in>I. x`n\<in>X(n)-(SA`n)} = 0" by auto
      ultimately have "0\<in>\<FF>" by auto
      then have False using ultraFilter
        unfolding IsUltrafilter_def IsFilter_def by auto
    }
    then have "t\<notin>internal_set(SA,X)" by auto moreover
    have "t\<in>hyper_set(X)" using internal_subset[OF f] t by auto
    ultimately have "t\<in>hyper_set(X)-A" using s(2) by auto
  }
  then have "internal_set(?S,X) \<subseteq> hyper_set(X)-A" by auto moreover
  {
    fix t assume "t\<in>hyper_set(X)-A"
    then have t:"t\<in>hyper_set(X)" "t\<notin>A" by auto
    from t(1) obtain x where x:"t=hyper_rel(X)``{x}" "x:Pi(I,X)" unfolding hyper_set_def
      quotient_def by auto
    with t(2) s(2) have "{n\<in>I. x`n\<in>SA`n}\<notin>\<FF>" unfolding internal_set_def[OF s(1)] by auto
    then have "I-{n\<in>I. x`n\<in>SA`n}\<in>\<FF>" using set_ultrafilter[OF _ ultraFilter]
      by auto
    then have "{n\<in>I. x`n\<in>X(n)-SA`n}\<in>Pow(I) \<Longrightarrow> I-{n\<in>I. x`n\<in>SA`n} \<subseteq> {n\<in>I. x`n\<in>X(n)-SA`n} \<longrightarrow> {n\<in>I. x`n\<in>X(n)-SA`n}:\<FF>"
      using ultraFilter unfolding IsFilter_def IsUltrafilter_def by auto moreover
    {
      fix q assume "q\<in>I-{n\<in>I. x`n\<in>SA`n}"
      then have "q: I" "x`q\<notin>SA`q" by auto
      with x(2) have "q\<in>I" "x`q:X(q)" "x`q\<notin>SA`q" using apply_type by auto
      then have "q\<in>{n\<in>I. x`n\<in>X(n)-SA`n}" by auto
    }
    then have "I-{n\<in>I. x`n\<in>SA`n} \<subseteq> {n\<in>I. x`n\<in>X(n)-SA`n}" by auto ultimately
    have "{n\<in>I. x`n\<in>X(n)-SA`n}\<in>\<FF>" by auto
    then have "{n\<in>I. x`n\<in>?S`n}\<in>\<FF>" using apply_equality[OF _ f] by auto
    with x(1,2) have "t\<in>internal_set(?S,X)" unfolding internal_set_def[OF f] by auto
  }
  ultimately have "hyper_set(X)-A = internal_set(?S,X)" by auto
  then show ?thesis unfolding isInternal_def using f by auto
qed

lemma finite_internal:
  assumes "A\<in>FinPow(hyper_set(X))"
  shows "isInternal(A,X)" unfolding isInternal_def
proof(rule FinPow_induct[OF _ _ assms])
  let ?S0="I\<times>{0}"
  have s:"?S0:Pi(I,\<lambda>i. Pow(X(i)))" unfolding Pi_def function_def by auto
  {
    fix t assume "t\<in>internal_set(?S0,X)"
    then obtain x where x:"t=hyper_rel(X)``{x}" "x:Pi(I,X)" "{n\<in>I. x`n\<in>?S0`n}\<in>\<FF>"
      unfolding internal_set_def[OF s] by auto
    from x(3) have "{n\<in>I. x`n\<in>0}\<in>\<FF>" using apply_equality[OF _ s] by auto
    then have "0\<in>\<FF>" by auto
    then have False using ultraFilter unfolding IsFilter_def IsUltrafilter_def by auto
  }
  then have "0 = internal_set(?S0,X)" by auto
  with s show "\<exists>S\<in>\<Prod>i\<in>I. Pow(X(i)). 0 = internal_set(S,X)" by auto
  {
    fix B assume b:"B\<in>FinPow(hyper_set(X))" "\<exists>S\<in>\<Prod>i\<in>I. Pow(X(i)). B = internal_set(S,X)"
    from b(2) obtain S where S:"S:(\<Prod>i\<in>I. Pow(X(i)))" "B=internal_set(S,X)" by auto

    {
      fix t assume "t\<in>hyper_set(X)"
      then obtain x where x:"t=hyper_rel(X)``{x}" "x:Pi(I,X)" unfolding hyper_set_def
        quotient_def by auto
      let ?S="{\<langle>i,S`i\<union>{x`i}\<rangle>. i\<in>I}"
      have f:"?S:Pi(I,\<lambda>i. Pow(X(i)))" unfolding Pi_def function_def apply auto
        using apply_type[OF x(2)] apply_type[OF S(1)] by auto
      {
        fix q assume q:"q\<in>B\<union>{t}"
        {
          assume "q\<in>B"
          with S(2) obtain y where y:"q=hyper_rel(X)``{y}" "y:Pi(I,X)" "{n\<in>I. y`n\<in>S`n}:\<FF>"
            unfolding internal_set_def[OF S(1)] by auto
          have "{n\<in>I. y`n\<in>S`n} \<subseteq> {n\<in>I. y`n\<in>S`n\<union>{x`n}}" by auto
          moreover from y(3) have "\<And>Q. Q \<subseteq> I \<Longrightarrow> {n\<in>I. y`n\<in>S`n} \<subseteq> Q \<Longrightarrow> Q:\<FF>"
            using ultraFilter unfolding IsFilter_def IsUltrafilter_def by auto
          from this[of "{n\<in>I. y`n\<in>S`n\<union>{x`n}}"] 
          have "{n\<in>I. y`n\<in>S`n} \<subseteq> {n\<in>I. y`n\<in>S`n\<union>{x`n}} \<Longrightarrow> {n\<in>I. y`n\<in>S`n\<union>{x`n}}:\<FF>" by auto
          ultimately have "{n\<in>I. y`n\<in>S`n\<union>{x`n}}:\<FF>" by auto
          then have "{n\<in>I. y`n\<in>?S`n}:\<FF>" using apply_equality[OF _ f] by auto
          with y(1,2) have "q\<in>internal_set(?S,X)" unfolding internal_set_def[OF f] by auto
        } moreover
        {
          assume "q\<notin>B"
          with q have "q=t" by auto
          with x have xx:"q=hyper_rel(X)``{x}" "x:Pi(I,X)" by auto
          have "{n\<in>I. x`n\<in>{x`n}} = I" by auto
          then have "{n\<in>I. x`n\<in>{x`n}}\<in>\<FF>" using ultraFilter unfolding IsFilter_def
            IsUltrafilter_def by auto
          then have "\<And>Q. Q \<subseteq> I \<Longrightarrow> {n\<in>I. x`n\<in>{x`n}} \<subseteq> Q \<Longrightarrow> Q:\<FF>"
            using ultraFilter unfolding IsFilter_def IsUltrafilter_def by auto
          from this[of "{n:I. x`n:?S`n}"] have 
            "{n\<in>I. x`n\<in>{x`n}} \<subseteq> {n:I. x`n:?S`n} \<Longrightarrow> {n:I. x`n:?S`n}:\<FF>" by auto
          moreover
          have "{n\<in>I. x`n\<in>{x`n}} \<subseteq> {n:I. x`n:?S`n}" using apply_equality[OF _ f] by auto
          ultimately have " {n:I. x`n:?S`n}:\<FF>" by auto
          with xx have "q\<in>internal_set(?S,X)" unfolding internal_set_def[OF f] by auto
        } ultimately
        have "q:internal_set(?S,X)" by auto
      }
      then have "B\<union>{t} \<subseteq> internal_set(?S,X)" by auto moreover
      {
        fix q assume q:"q\<in>internal_set(?S,X)" "q\<noteq>t"
        then obtain y where y:"q=hyper_rel(X)``{y}" "y:Pi(I,X)" "{n:I. y`n:?S`n}:\<FF>"
          unfolding internal_set_def[OF f] by auto
        {
          assume "{n\<in>I. y`n\<in>S`n}\<notin>\<FF>"
          then have "I-{n\<in>I. y`n\<in>S`n}\<in>\<FF>" using ultraFilter
            set_ultrafilter[of _ I, OF _ ultraFilter] by auto
          with y(3) have "(I-{n\<in>I. y`n\<in>S`n})\<inter>{n:I. y`n:?S`n}:\<FF>"
            using ultraFilter unfolding IsFilter_def IsUltrafilter_def by auto
          then have "\<And>B. B:Pow(I) \<Longrightarrow> (I-{n\<in>I. y`n\<in>S`n})\<inter>{n:I. y`n:?S`n} \<subseteq> B \<Longrightarrow> B:\<FF>"
            using ultraFilter unfolding IsFilter_def IsUltrafilter_def by auto
          from this[of "{n:I. y`n=x`n}"] have "(I-{n\<in>I. y`n\<in>S`n})\<inter>{n:I. y`n:?S`n} \<subseteq> {n:I. y`n=x`n} \<Longrightarrow> {n:I. y`n=x`n}:\<FF>"
            by auto moreover
          {
            fix h assume "h:(I-{n\<in>I. y`n\<in>S`n})\<inter>{n:I. y`n:?S`n}"
            then have "h\<in>I" "y`h\<notin>S`h" "y`h\<in>?S`h" by auto
            then have "h\<in>I" "y`h = x`h" using apply_equality[OF _ f] by auto
            then have "h:{n:I. y`n=x`n}" by auto
          }
          then have "(I-{n\<in>I. y`n\<in>S`n})\<inter>{n:I. y`n:?S`n} \<subseteq> {n:I. y`n=x`n}" by auto
          ultimately have "{n:I. y`n=x`n}:\<FF>" by auto
          with x(2) y(2) have "\<langle>y,x\<rangle>:hyper_rel(X)" unfolding hyper_rel_def by auto
          then have "q=t" using x(1) y(1) equiv_class_eq[OF hyper_equiv] by auto
          with q(2) have False by auto
        }
        then have "{n\<in>I. y`n\<in>S`n}\<in>\<FF>" by auto
        with y(1,2) have "q\<in>B" using S(2) unfolding internal_set_def[OF S(1)] by auto
      }
      then have "internal_set(?S,X) \<subseteq> B\<union>{t}" by auto
      ultimately have "B\<union>{t} = internal_set(?S,X)" by auto
      with f have "\<exists>S\<in>\<Prod>i\<in>I. Pow(X(i)). B \<union> {t} = internal_set(S,X)" by auto
    }
    then have "\<forall>t\<in>hyper_set(X). \<exists>S\<in>\<Prod>i\<in>I. Pow(X(i)). B \<union> {t} = internal_set(S,X)" by auto
  }
  then show "\<forall>A\<in>FinPow(hyper_set(X)).
       (\<exists>S\<in>\<Prod>i\<in>I. Pow(X(i)). A = internal_set(S,X)) \<longrightarrow>
       (\<forall>t\<in>hyper_set(X). \<exists>S\<in>\<Prod>i\<in>I. Pow(X(i)). A \<union> {t} = internal_set(S,X))" by auto
qed

lemma internal_union:
  assumes "isInternal(A,X)" "isInternal(B,X)"
  shows "isInternal(A\<union>B,X)"
proof-
  from assms obtain SA SB where s:"SA:Pi(I,\<lambda>i. Pow(X(i)))" "SB:Pi(I,\<lambda>i. Pow(X(i)))" 
    "A=internal_set(SA,X)" "B=internal_set(SB,X)"
    unfolding isInternal_def by auto
  let ?S="{\<langle>n,(SA`n)\<union>(SB`n)\<rangle>. n\<in>I}"
  from s(1,2) have "\<forall>n\<in>I. (SA`n)\<in>Pow(X(n))" "\<forall>n\<in>I. (SB`n)\<in>Pow(X(n))" using apply_type[of _ I "\<lambda>i. Pow(X(i))"]
    by auto
  then have "\<forall>n\<in>I. (SA`n)\<union>(SB`n)\<in>Pow(X(n))" by auto
  then have f:"?S:Pi(I,\<lambda>i. Pow(X(i)))" unfolding Pi_def function_def by auto
  {
    fix t assume t:"t\<in>internal_set(?S,X)"
    then obtain x where x:"t=hyper_rel(X)``{x}" "x\<in>Pi(I,X)" "{n\<in>I. x`n\<in>?S`n}\<in>\<FF>"
      unfolding internal_set_def[OF f] by auto
    from x(3) have U:"{n\<in>I. x`n\<in>(SA`n)\<union>(SB`n)}\<in>\<FF>"
      using apply_equality[OF _ f] by auto
    {
      assume "t\<notin>A"
      with x(1,2) s(3) have "{n\<in>I. x`n\<in>(SA`n)}\<notin>\<FF>" unfolding internal_set_def[OF s(1)]
        by auto
      then have "I-{n\<in>I. x`n\<in>(SA`n)}\<in>\<FF>" using ultraFilter
        set_ultrafilter[of "{n\<in>I. x`n\<in>(SA`n)}"] by auto moreover
      have "{n\<in>I. x`n\<notin>(SA`n)}\<in>Pow(I)" by auto moreover
      {
        fix n assume "n\<in>I-{n\<in>I. x`n\<in>(SA`n)}"
        then have "n\<in>{n\<in>I. x`n\<notin>(SA`n)}" by auto
      }
      then have "I-{n\<in>I. x`n\<in>(SA`n)} \<subseteq> {n\<in>I. x`n\<notin>(SA`n)}" by auto
      ultimately have "{n\<in>I. x`n\<notin>(SA`n)}:\<FF>" using ultraFilter unfolding IsFilter_def
        IsUltrafilter_def by auto
      with U have "{n\<in>I. x`n\<in>(SA`n)\<union>(SB`n)}\<inter>{n\<in>I. x`n\<notin>(SA`n)}:\<FF>"
        using ultraFilter unfolding IsFilter_def IsUltrafilter_def by auto moreover
      have "{n:I. x`n\<in>SB`n}\<in>Pow(I)" by auto moreover
      {
        fix n assume "n\<in>{n\<in>I. x`n\<in>(SA`n)\<union>(SB`n)}\<inter>{n\<in>I. x`n\<notin>(SA`n)}"
        then have "n\<in>I" "x`n\<in>SB`n" by auto
        then have "n:{n:I. x`n\<in>SB`n}" by auto
      }
      then have "{n\<in>I. x`n\<in>(SA`n)\<union>(SB`n)}\<inter>{n\<in>I. x`n\<notin>(SA`n)} \<subseteq> {n:I. x`n\<in>SB`n}" by auto
      ultimately have "{n:I. x`n\<in>SB`n}\<in>\<FF>" using ultraFilter unfolding IsFilter_def
        IsUltrafilter_def by auto
      with x(1,2) have "t\<in>B" using s(4) unfolding internal_set_def[OF s(2)] by auto
    }
    then have "t\<in>A\<union>B" by auto
  }
  then have "internal_set(?S,X) \<subseteq> A\<union>B" by auto moreover
  {
    fix t assume "t\<in>A"
    then obtain x where x:"t=hyper_rel(X)``{x}" "x\<in>Pi(I,X)" "{n\<in>I. x`n\<in>SA`n}\<in>\<FF>"
      using s(3) unfolding internal_set_def[OF s(1)] by auto
    have "{n\<in>I. x`n\<in>SA`n} \<subseteq> {n\<in>I. x`n\<in>(SA`n)\<union>(SB`n)}" by auto moreover
    have "{n\<in>I. x`n\<in>(SA`n)\<union>(SB`n)}\<in>Pow(I)" by auto moreover note x(3)
    ultimately have "{n\<in>I. x`n\<in>(SA`n)\<union>(SB`n)}:\<FF>" using ultraFilter
      unfolding IsFilter_def IsUltrafilter_def by auto
    then have "{n\<in>I. x`n\<in>?S`n}:\<FF>" using apply_equality[OF _ f] by auto
    with x(1,2) have "t\<in>internal_set(?S,X)" unfolding internal_set_def[OF f] by auto
  }
  then have "A \<subseteq> internal_set(?S,X)" by auto moreover
  {
    fix t assume "t\<in>B"
    then obtain x where x:"t=hyper_rel(X)``{x}" "x\<in>Pi(I,X)" "{n\<in>I. x`n\<in>SB`n}\<in>\<FF>"
      using s(4) unfolding internal_set_def[OF s(2)] by auto
    have "{n\<in>I. x`n\<in>SB`n} \<subseteq> {n\<in>I. x`n\<in>(SA`n)\<union>(SB`n)}" by auto moreover
    have "{n\<in>I. x`n\<in>(SA`n)\<union>(SB`n)}\<in>Pow(I)" by auto moreover note x(3)
    ultimately have "{n\<in>I. x`n\<in>(SA`n)\<union>(SB`n)}:\<FF>" using ultraFilter
      unfolding IsFilter_def IsUltrafilter_def by auto
    then have "{n\<in>I. x`n\<in>?S`n}:\<FF>" using apply_equality[OF _ f] by auto
    with x(1,2) have "t\<in>internal_set(?S,X)" unfolding internal_set_def[OF f] by auto
  }
  then have "B \<subseteq> internal_set(?S,X)" by auto ultimately
  have "A \<union> B = internal_set(?S,X)" by auto
  then show ?thesis unfolding isInternal_def using f by auto
qed
            
definition internal_rel where
"S:Pi(I,\<lambda>i. Pow(X(i)\<times>X(i))) \<Longrightarrow> internal_rel(S,X) \<equiv> {\<langle>hyper_rel(X)``{x},hyper_rel(X)``{y}\<rangle>. \<langle>x,y\<rangle>\<in>{\<langle>p,q\<rangle>\<in>Pi(I,X)\<times>Pi(I,X). {n\<in>I. \<langle>p`n,q`n\<rangle>\<in>S`n}\<in>\<FF>}}"

lemma internal_rel_subset:
  assumes "S:Pi(I,\<lambda>i. Pow(X(i)\<times>X(i)))"
  shows "internal_rel(S,X) \<subseteq> hyper_set(X)\<times>hyper_set(X)"
proof-
  {
    fix t assume "t\<in>internal_rel(S,X)"
    then have "t\<in>{\<langle>hyper_rel(X)``{x},hyper_rel(X)``{y}\<rangle>. \<langle>x,y\<rangle>\<in>{\<langle>p,q\<rangle>\<in>Pi(I,X)\<times>Pi(I,X). {n\<in>I. \<langle>p`n,q`n\<rangle>\<in>S`n}\<in>\<FF>}}"
      unfolding internal_rel_def[OF assms].
    then obtain q p where q:"t=\<langle>hyper_rel(X)``{q},hyper_rel(X)``{p}\<rangle>" "q:Pi(I,X)" "p:Pi(I,X)" "{n\<in>I. \<langle>q`n,p`n\<rangle>\<in>S`n}\<in>\<FF>"
      by auto
    from q(1-3) have "t\<in>hyper_set(X)\<times>hyper_set(X)" unfolding hyper_set_def quotient_def by auto
  }
  then show "internal_rel(S,X) \<subseteq> hyper_set(X)\<times>hyper_set(X)" by auto
qed

lemma converse_internal:
  assumes "S:Pi(I,\<lambda>i. Pow(X(i)\<times>X(i)))"
  shows "converse(internal_rel(S,X)) = internal_rel({\<langle>i,converse(S`i)\<rangle>. i\<in>I},X)"
proof
  have "\<And>i. i\<in>I \<Longrightarrow> (S`i) \<subseteq> X(i)\<times>X(i)" using apply_type[OF assms] by auto
  then have "\<And>i. i\<in>I \<Longrightarrow> converse(S`i) \<subseteq> X(i)\<times>X(i)" unfolding converse_def by auto
  then have A:"{\<langle>i,converse(S`i)\<rangle>. i\<in>I}:Pi(I,\<lambda>i. Pow(X(i)\<times>X(i)))" unfolding Pi_def function_def by auto
  {
    fix x assume "x\<in>converse(internal_rel(S,X))"
    then obtain y z where x:"x=\<langle>y,z\<rangle>" "\<langle>z,y\<rangle>\<in>internal_rel(S,X)" using converse_iff by auto
    from x(2) obtain zz yy where q:"zz:Pi(I,X)" "yy:Pi(I,X)" "z=hyper_rel(X)``{zz}"  "y=hyper_rel(X)``{yy}" 
      "{n \<in> I . \<langle>zz ` n, yy ` n\<rangle> \<in> S ` n} \<in> \<FF>" 
      unfolding internal_rel_def[OF assms] by auto
    from q(5) have "{n \<in> I . \<langle>yy ` n, zz ` n\<rangle> \<in> converse(S ` n)}:\<FF>" using converse_iff by auto
    then have "{n \<in> I . \<langle>yy ` n, zz ` n\<rangle> \<in> {\<langle>i,converse(S`i)\<rangle>. i\<in>I}`n}:\<FF>" using apply_equality[OF _ A] by auto
    with q(1-4) x(1) have "x\<in>internal_rel({\<langle>i,converse(S`i)\<rangle>. i\<in>I},X)" unfolding internal_rel_def[OF A] by auto
  }
  then show "converse(internal_rel(S, X)) \<subseteq> internal_rel({\<langle>i, converse(S ` i)\<rangle> . i \<in> I}, X)" by auto
  {
    fix x assume "x\<in>internal_rel({\<langle>i,converse(S`i)\<rangle>. i\<in>I},X)"
    

lemma internal_rel_total:
  shows "internal_rel({\<langle>i,X(i)\<times>X(i)\<rangle>. i\<in>I},X) = hyper_set(X)\<times>hyper_set(X)"
proof
  have f:"{\<langle>i,X(i)\<times>X(i)\<rangle>. i\<in>I}:Pi(I,\<lambda>i. Pow(X(i)\<times>X(i)))" unfolding Pi_def function_def by auto
  then show "internal_rel({\<langle>i,X(i)\<times>X(i)\<rangle>. i\<in>I},X) \<subseteq> hyper_set(X)\<times>hyper_set(X)" using internal_rel_subset by auto
  {
    fix m assume "m\<in>hyper_set(X)\<times>hyper_set(X)"
    then obtain m1 m2 where p:"m1\<in>hyper_set(X)" "m2\<in>hyper_set(X)" "m=\<langle>m1,m2\<rangle>" by auto
    then obtain x1 x2 where m:"m1=hyper_rel(X)``{x1}" "m2=hyper_rel(X)``{x2}" "m=\<langle>m1,m2\<rangle>"
      "x1\<in>Pi(I,X)" "x2\<in>Pi(I,X)" unfolding hyper_set_def quotient_def by auto
    {
      fix n assume n:"n\<in>I"
      with m have "\<langle>x1`n,x2`n\<rangle>\<in>X(n)\<times>X(n)" using apply_type by auto
      then have "\<langle>x1`n,x2`n\<rangle>\<in>{\<langle>i,X(i)\<times>X(i)\<rangle>. i\<in>I}`n" using apply_equality[OF _ f] n by auto
    }
    then have "I={n\<in>I. \<langle>x1`n,x2`n\<rangle>\<in>{\<langle>i,X(i)\<times>X(i)\<rangle>. i\<in>I}`n}" by auto
    then have "{n\<in>I. \<langle>x1`n,x2`n\<rangle>\<in>{\<langle>i,X(i)\<times>X(i)\<rangle>. i\<in>I}`n}:\<FF>" using
        ultraFilter unfolding IsFilter_def IsUltrafilter_def by auto
    then have "\<langle>x1,x2\<rangle>\<in>{\<langle>p,q\<rangle>\<in>Pi(I,X)\<times>Pi(I,X). {n\<in>I. \<langle>p`n,q`n\<rangle>\<in>{\<langle>i,X(i)\<times>X(i)\<rangle>. i\<in>I}`n}\<in>\<FF>}"
      using m(4,5) by auto
    with m(1,2) have "\<langle>m1,m2\<rangle>\<in>{\<langle>hyper_rel(X)``{x1},hyper_rel(X)``{x2}\<rangle>. \<langle>x1,x2\<rangle>\<in>{\<langle>p,q\<rangle>\<in>Pi(I,X)\<times>Pi(I,X). {n\<in>I. \<langle>p`n,q`n\<rangle>\<in>{\<langle>i,X(i)\<times>X(i)\<rangle>. i\<in>I}`n}\<in>\<FF>}}"
      by auto
    with p(3) have "m\<in>internal_rel({\<langle>i,X(i)\<times>X(i)\<rangle>. i\<in>I},X)"
      unfolding internal_rel_def[OF f] by auto
  }
  then show "hyper_set(X)\<times>hyper_set(X) \<subseteq> internal_rel({\<langle>i,X(i)\<times>X(i)\<rangle>. i\<in>I},X)" by auto
qed

definition internal_fun where
"S1:Pi(I,\<lambda>i. Pow(X(i))) \<Longrightarrow> S2:Pi(I,\<lambda>i. Pow(X(i))) \<Longrightarrow> S:Pi(I, \<lambda>i. S1`i \<rightarrow> S2`i) 
  \<Longrightarrow> internal_fun(S,X) \<equiv> internal_rel(S,X)"


lemma internal_fun_is_fun:
  assumes "S1:Pi(I,\<lambda>i. Pow(X(i)))" "S2:Pi(I,\<lambda>i. Pow(X(i)))" "S:Pi(I, \<lambda>i. S1`i \<rightarrow> S2`i)"
  shows "internal_fun(S,X):internal_set(S1,X)\<rightarrow>internal_set(S2,X)" unfolding Pi_def function_def
proof(safe)
  have SS:"S:Pi(I, \<lambda>i. Pow(X(i)\<times>X(i)))"
  proof-
    {
      fix x assume "x\<in>S"
      with assms(3) have "x\<in>(\<Sum>i\<in>I. S1`i \<rightarrow> S2`i)" unfolding Pi_def by auto
      then obtain i f where f:"x=\<langle>i,f\<rangle>" "i\<in>I" "f\<in>S1`i \<rightarrow> S2`i" by auto
      from f(3) have "f \<subseteq> S1`i\<times>S2`i" unfolding Pi_def by auto
      then have "f \<subseteq> X(i)\<times>X(i)" using apply_type[OF assms(1) f(2)] apply_type[OF assms(2) f(2)] by auto
      with f(1,2) have "x\<in>(\<Sum>i\<in>I. Pow(X(i)\<times>X(i)))" by auto
    }
    then have "S \<subseteq> (\<Sum>i\<in>I. Pow(X(i)\<times>X(i)))" by auto
    then show ?thesis using assms(3) unfolding Pi_def by auto
  qed
  fix x assume x:"x\<in>internal_fun(S,X)"
  then obtain y z where f:"x= \<langle>hyper_rel(X)``{y},hyper_rel(X)``{z}\<rangle>" "y:Pi(I,X)" "z:Pi(I,X)" "{n\<in>I. \<langle>y`n, z`n\<rangle>:S`n}\<in>\<FF>"
    unfolding internal_fun_def[OF assms] internal_rel_def[OF SS] by auto
  {
    fix n assume n:"n:{n\<in>I. \<langle>y`n, z`n\<rangle>:S`n}"
    then have n:"n:I" "\<langle>y`n,z`n\<rangle>:S`n" by auto
    moreover from n(1) have "S`n\<in> S1`n \<rightarrow> S2`n" using apply_type[OF assms(3)] by auto
    with n(2) have "y`n:S1`n" "z`n:S2`n" unfolding Pi_def by auto
    with n(1) have "n\<in>{n:I. y`n:S1`n}" "n\<in>{n:I. z`n:S2`n}" by auto
  }
  then have s:"{n\<in>I. \<langle>y`n, z`n\<rangle>:S`n} \<subseteq> {n:I. y`n:S1`n}" "{n\<in>I. \<langle>y`n, z`n\<rangle>:S`n} \<subseteq> {n:I. z`n:S2`n}" by auto
  from f(4) have R:"\<And>A. A\<in>Pow(I) \<Longrightarrow> {n\<in>I. \<langle>y`n, z`n\<rangle>:S`n} \<subseteq> A \<Longrightarrow> A\<in>\<FF>" using ultraFilter unfolding IsFilter_def IsUltrafilter_def
    by auto
  from R[of "{n:I. y`n:S1`n}"] s(1) have "{n:I. y`n:S1`n}\<in>\<FF>" by auto
  then have "hyper_rel(X)``{y}:internal_set(S1,X)" unfolding internal_set_def[OF assms(1)]
    using f(2) by auto moreover
  from R[of "{n:I. z`n:S2`n}"] s(2) have "{n:I. z`n:S2`n}\<in>\<FF>" by auto
  then have "hyper_rel(X)``{z}:internal_set(S2,X)" unfolding internal_set_def[OF assms(2)]
    using f(3) by auto moreover note f(1)
  ultimately show "x\<in>internal_set(S1,X)\<times>internal_set(S2,X)" by auto
next
  have SS:"S:Pi(I, \<lambda>i. Pow(X(i)\<times>X(i)))"
  proof-
    {
      fix x assume "x\<in>S"
      with assms(3) have "x\<in>(\<Sum>i\<in>I. S1`i \<rightarrow> S2`i)" unfolding Pi_def by auto
      then obtain i f where f:"x=\<langle>i,f\<rangle>" "i\<in>I" "f\<in>S1`i \<rightarrow> S2`i" by auto
      from f(3) have "f \<subseteq> S1`i\<times>S2`i" unfolding Pi_def by auto
      then have "f \<subseteq> X(i)\<times>X(i)" using apply_type[OF assms(1) f(2)] apply_type[OF assms(2) f(2)] by auto
      with f(1,2) have "x\<in>(\<Sum>i\<in>I. Pow(X(i)\<times>X(i)))" by auto
    }
    then have "S \<subseteq> (\<Sum>i\<in>I. Pow(X(i)\<times>X(i)))" by auto
    then show ?thesis using assms(3) unfolding Pi_def by auto
  qed
  fix x assume "x\<in>internal_set(S1,X)"
  then obtain y where x:"x=hyper_rel(X)``{y}" "y:Pi(I,X)" "{n:I. y`n\<in>S1`n}:\<FF>"
    unfolding internal_set_def[OF assms(1)] by auto
  let ?z="{\<langle>i,if y`i\<in>S1`i then (S`i)`(y`i) else y`i\<rangle>. i\<in>I}"
  have z:"?z\<in>Pi(I,X)" unfolding Pi_def function_def apply auto prefer 2
    using x(2) apply_type apply simp
  proof-
    fix i assume i:"i:I" "y ` i \<in> S1 ` i"
    from i(1) assms(3) have "S`i:S1`i \<rightarrow> S2`i" using apply_type by auto
    with i(2) have "(S`i)`(y`i):S2`i" using apply_type by auto
    with i(1) show "(S`i)`(y`i):X(i)" using apply_type[OF assms(2)] by auto
  qed
  {
    fix n assume "n\<in>{n:I. y`n\<in>S1`n}"
    then have n:"n:I" "y`n:S1`n" by auto
    from assms(3) n(1) have "S`n\<in>S1`n \<rightarrow> S2`n" using apply_type by auto
    with n(2) have "\<langle>y`n,(S`n)`(y`n)\<rangle>\<in>S`n" using apply_Pair by auto
    with n(1) have "n\<in>{n:I.  \<langle>y`n, ?z`n\<rangle>:S`n}" using n(2) apply_equality[OF _ z] by auto
  }
  then have "{n:I. y`n\<in>S1`n} \<subseteq> {n:I.  \<langle>y`n, ?z`n\<rangle>:S`n}" by auto
  moreover have "\<forall>C\<in>Pow(I). {n:I. y`n\<in>S1`n} \<subseteq> C \<longrightarrow> C \<in> \<FF>"
    using ultraFilter x(3) unfolding IsFilter_def IsUltrafilter_def by auto
  then have "{n:I.  \<langle>y`n, ?z`n\<rangle>:S`n}:Pow(I) \<longrightarrow> ({n:I. y`n\<in>S1`n} \<subseteq> {n:I.  \<langle>y`n, ?z`n\<rangle>:S`n} \<longrightarrow> {n:I.  \<langle>y`n, ?z`n\<rangle>:S`n} \<in> \<FF>)"
    unfolding Ball_def by auto
  then have "{n:I. y`n\<in>S1`n} \<subseteq> {n:I.  \<langle>y`n, ?z`n\<rangle>:S`n} \<longrightarrow> {n:I.  \<langle>y`n, ?z`n\<rangle>:S`n} \<in> \<FF>" by auto
  ultimately have "{n:I.  \<langle>y`n, ?z`n\<rangle>:S`n} \<in> \<FF>" by auto
  then have "\<langle>hyper_rel(X)``{y},hyper_rel(X)``{?z}\<rangle>\<in>internal_fun(S,X)"
    using z x(2,3) unfolding internal_fun_def[OF assms] internal_rel_def[OF SS] by auto
  then show "x\<in>domain(internal_fun(S,X))" using x(1) unfolding domain_def by auto
next
  have SS:"S:Pi(I, \<lambda>i. Pow(X(i)\<times>X(i)))"
  proof-
    {
      fix x assume "x\<in>S"
      with assms(3) have "x\<in>(\<Sum>i\<in>I. S1`i \<rightarrow> S2`i)" unfolding Pi_def by auto
      then obtain i f where f:"x=\<langle>i,f\<rangle>" "i\<in>I" "f\<in>S1`i \<rightarrow> S2`i" by auto
      from f(3) have "f \<subseteq> S1`i\<times>S2`i" unfolding Pi_def by auto
      then have "f \<subseteq> X(i)\<times>X(i)" using apply_type[OF assms(1) f(2)] apply_type[OF assms(2) f(2)] by auto
      with f(1,2) have "x\<in>(\<Sum>i\<in>I. Pow(X(i)\<times>X(i)))" by auto
    }
    then have "S \<subseteq> (\<Sum>i\<in>I. Pow(X(i)\<times>X(i)))" by auto
    then show ?thesis using assms(3) unfolding Pi_def by auto
  qed
  fix x y z assume as:"\<langle>x,y\<rangle>\<in>internal_fun(S,X)" "\<langle>x,z\<rangle>\<in>internal_fun(S,X)"
  from as(1) obtain h j where f:"x= hyper_rel(X)``{h}" "y=hyper_rel(X)``{j}" "h:Pi(I,X)" "j:Pi(I,X)" "{n\<in>I. \<langle>h`n, j`n\<rangle>:S`n}\<in>\<FF>"
    unfolding internal_fun_def[OF assms] internal_rel_def[OF SS] by auto
  from as(2) obtain k m where g:"x=hyper_rel(X)``{m}" "z=hyper_rel(X)``{k}" "m:Pi(I,X)" "k:Pi(I,X)" "{n\<in>I. \<langle>m`n, k`n\<rangle>:S`n}\<in>\<FF>"
    unfolding internal_fun_def[OF assms] internal_rel_def[OF SS] using f(1) by auto
  from f(1) g(1) have "hyper_rel(X)``{h} = hyper_rel(X)``{m}" by auto
  then have "\<langle>h,m\<rangle>\<in>hyper_rel(X)" using same_image_equiv[OF hyper_equiv] g(3) by auto
  then have "{n:I. h`n = m`n}:\<FF>" unfolding hyper_rel_def by auto
  with f(5) have "{n:I. h`n = m`n}\<inter>{n\<in>I. \<langle>h`n, j`n\<rangle>:S`n}:\<FF>"
    using ultraFilter unfolding IsFilter_def IsUltrafilter_def by auto
  with g(5) have "{n:I. h`n = m`n}\<inter>{n\<in>I. \<langle>h`n, j`n\<rangle>:S`n}\<inter>{n\<in>I. \<langle>m`n, k`n\<rangle>:S`n}:\<FF>"
    using ultraFilter unfolding IsFilter_def IsUltrafilter_def by auto
  then have "\<forall>A\<in>Pow(I). {n:I. h`n = m`n}\<inter>{n\<in>I. \<langle>h`n, j`n\<rangle>:S`n}\<inter>{n\<in>I. \<langle>m`n, k`n\<rangle>:S`n} \<subseteq> A \<longrightarrow> A\<in>\<FF>" 
    using ultraFilter unfolding IsFilter_def IsUltrafilter_def by auto
  then have "{n:I. j`n=k`n}:Pow(I) \<Longrightarrow> {n:I. h`n = m`n}\<inter>{n\<in>I. \<langle>h`n, j`n\<rangle>:S`n}\<inter>{n\<in>I. \<langle>m`n, k`n\<rangle>:S`n} \<subseteq> {n:I. j`n=k`n} \<longrightarrow> {n:I. j`n=k`n}\<in>\<FF>"
    by auto
  then have "{n:I. h`n = m`n}\<inter>{n\<in>I. \<langle>h`n, j`n\<rangle>:S`n}\<inter>{n\<in>I. \<langle>m`n, k`n\<rangle>:S`n} \<subseteq> {n:I. j`n=k`n} \<longrightarrow> {n:I. j`n=k`n}\<in>\<FF>" by auto moreover
  {
    fix n assume "n:{n:I. h`n = m`n}\<inter>{n\<in>I. \<langle>h`n, j`n\<rangle>:S`n}\<inter>{n\<in>I. \<langle>m`n, k`n\<rangle>:S`n}"
    then have n:"n\<in>I" "h`n=m`n" "\<langle>h`n, j`n\<rangle>:S`n" "\<langle>m`n, k`n\<rangle>:S`n" by auto
    with apply_type[OF assms(3) n(1)] have "j`n=k`n" unfolding Pi_def function_def by force
    with n(1) have "n:{n:I. j`n=k`n}" by auto
  }
  then have "{n:I. h`n = m`n}\<inter>{n\<in>I. \<langle>h`n, j`n\<rangle>:S`n}\<inter>{n\<in>I. \<langle>m`n, k`n\<rangle>:S`n} \<subseteq> {n:I. j`n=k`n}" by auto
  ultimately have "{n:I. j`n=k`n}\<in>\<FF>" by auto
  with f(4) g(4) have "\<langle>j,k\<rangle>\<in>hyper_rel(X)" unfolding hyper_rel_def by auto
  with f(2) g(2) show "y=z" using equiv_class_eq[OF hyper_equiv] by auto
qed

lemma internal_fun_apply:
  assumes "S1 \<in> (\<Prod>i\<in>I. Pow(X(i)))" "S2 \<in> (\<Prod>i\<in>I. Pow(X(i)))" "S \<in> (\<Prod>i\<in>I. S1 ` i \<rightarrow> S2 ` i)" 
    and "x\<in>Pi(I,X)" "{i:I. x`i\<in>S1`i}\<in>\<FF>" (*[x]\<in>internal_set(S1)*)
  shows "internal_fun(S, X)`(hyper_rel(X)``{x}) = hyper_rel(X)``{{\<langle>i, if x ` i \<in> S1 ` i then S ` i ` (x ` i) else x ` i\<rangle> . i \<in> I}}"
    and "{\<langle>i, if x ` i \<in> S1 ` i then S ` i ` (x ` i) else x ` i\<rangle> . i \<in> I}:Pi(I,X)"
proof- 
  have SS:"S:Pi(I, \<lambda>i. Pow(X(i)\<times>X(i)))"
  proof-
    {
      fix x assume "x\<in>S"
      with assms(3) have "x\<in>(\<Sum>i\<in>I. S1`i \<rightarrow> S2`i)" unfolding Pi_def by auto
      then obtain i f where f:"x=\<langle>i,f\<rangle>" "i\<in>I" "f\<in>S1`i \<rightarrow> S2`i" by auto
      from f(3) have "f \<subseteq> S1`i\<times>S2`i" unfolding Pi_def by auto
      then have "f \<subseteq> X(i)\<times>X(i)" using apply_type[OF assms(1) f(2)] apply_type[OF assms(2) f(2)] by auto
      with f(1,2) have "x\<in>(\<Sum>i\<in>I. Pow(X(i)\<times>X(i)))" by auto
    }
    then have "S \<subseteq> (\<Sum>i\<in>I. Pow(X(i)\<times>X(i)))" by auto
    then show ?thesis using assms(3) unfolding Pi_def by auto
  qed
  let ?z="{\<langle>i, if x`i\<in>S1`i then (S`i)`(x`i) else x`i\<rangle>. i\<in>I}"
  show z:"?z\<in>Pi(I,X)" unfolding Pi_def function_def apply auto prefer 2
    using assms(4) apply_type apply simp
  proof-
    fix i assume i:"i:I" "x ` i \<in> S1 ` i"
    from i(1) assms(3) have "S`i:S1`i \<rightarrow> S2`i" using apply_type by auto
    with i(2) have "(S`i)`(x`i):S2`i" using apply_type by auto
    with i(1) show "(S`i)`(x`i):X(i)" using apply_type[OF assms(2)] by auto
  qed
  have "hyper_rel(X)``{x}\<in>internal_set(S1,X)" unfolding internal_set_def[OF assms(1)]
    using assms(4,5) by auto
  then have "\<langle>hyper_rel(X)``{x},internal_fun(S, X)`(hyper_rel(X)``{x})\<rangle>\<in>internal_fun(S, X)"
    using apply_Pair[OF internal_fun_is_fun[OF assms(1-3)]] by auto
  then have "\<langle>hyper_rel(X)``{x},internal_fun(S, X)`(hyper_rel(X)``{x})\<rangle>\<in>{\<langle>hyper_rel(X)``{x},hyper_rel(X)``{y}\<rangle>.
    \<langle>x,y\<rangle> \<in> {\<langle>p,q\<rangle> \<in> (\<Prod>i\<in>I. X(i)) \<times> (\<Prod>i\<in>I. X(i)) . {n \<in> I . \<langle>p ` n, q ` n\<rangle> \<in> S ` n} \<in> \<FF>}}"
    unfolding internal_fun_def[OF assms(1-3)] internal_rel_def[OF SS] by auto
  then obtain t y where A:"hyper_rel(X)``{x}=hyper_rel(X)``{t}" "internal_fun(S, X)`(hyper_rel(X)``{x}) = hyper_rel(X)``{y}"
    "t:Pi(I,X)" "y:Pi(I,X)" "{n \<in> I . \<langle>t ` n, y ` n\<rangle> \<in> S ` n} \<in> \<FF>" by auto
  from A(1,3) assms(4) have "\<langle>x,t\<rangle>\<in>hyper_rel(X)" using eq_equiv_class hyper_equiv[of X] by auto
  then have "{i:I. x`i = t`i}:\<FF>" unfolding hyper_rel_def by auto
  with A(5) have "{i:I. x`i = t`i}\<inter>{n \<in> I . \<langle>t ` n, y ` n\<rangle> \<in> S ` n}:\<FF>" using ultraFilter
    unfolding IsFilter_def IsUltrafilter_def by auto moreover
  have "{n \<in> I . \<langle>x ` n, y ` n\<rangle> \<in> S ` n}\<in>Pow(I)" by auto
  ultimately have "{i:I. x`i = t`i}\<inter>{n \<in> I . \<langle>t ` n, y ` n\<rangle> \<in> S ` n} \<subseteq> {n \<in> I . \<langle>x ` n, y ` n\<rangle> \<in> S ` n} \<longrightarrow> {n \<in> I . \<langle>x ` n, y ` n\<rangle> \<in> S ` n}:\<FF>"
    using ultraFilter unfolding IsFilter_def IsUltrafilter_def by auto moreover
  {
    fix i assume "i\<in>{i:I. x`i = t`i}\<inter>{n \<in> I . \<langle>t ` n, y ` n\<rangle> \<in> S ` n}"
    then have "i: I" "x`i=t`i" "\<langle>t ` i, y ` i\<rangle> \<in> S ` i" by auto
    then have "i:I" "\<langle>x`i,y`i\<rangle>\<in>S`i" by auto
    then have "i\<in>{n \<in> I . \<langle>x ` n, y ` n\<rangle> \<in> S ` n}" by auto
  }
  then have "{i:I. x`i = t`i}\<inter>{n \<in> I . \<langle>t ` n, y ` n\<rangle> \<in> S ` n} \<subseteq> {n \<in> I . \<langle>x ` n, y ` n\<rangle> \<in> S ` n}" by auto
  ultimately have "{n \<in> I . \<langle>x ` n, y ` n\<rangle> \<in> S ` n}:\<FF>" by auto
  moreover have "{n\<in>I. ?z`n = y`n}\<in>Pow(I)" by auto
  ultimately have "{n \<in> I . \<langle>x ` n, y ` n\<rangle> \<in> S ` n} \<subseteq> {n\<in>I. ?z`n = y`n} \<longrightarrow> {n\<in>I. ?z`n = y`n}\<in>\<FF>"
    using ultraFilter unfolding IsFilter_def IsUltrafilter_def
    by auto moreover
  {
    fix n assume "n:{n \<in> I . \<langle>x ` n, y ` n\<rangle> \<in> S ` n}"
    then have n:"n\<in>I" "\<langle>x`n,y`n\<rangle>\<in>S`n" by auto
    from n(1) have "S`n:S1`n\<rightarrow>S2`n" using apply_type[OF assms(3)] by auto
    with n(2) have "\<langle>x`n,y`n\<rangle>\<in>S`n" "x`n\<in>S1`n" "(S`n)`(x`n) = y`n"
      using apply_equality[of "x`n" "y`n" "S`n" "S1`n" "\<lambda>_. S2`n"] unfolding Pi_def by auto
    then have "(if x`n\<in>S1`n then (S`n)`(x`n) else x`n) = y`n" by auto
    with n(1) have "n\<in>{n\<in>I. ?z`n = y`n}" using apply_equality z by auto
  }
  then have "{n \<in> I . \<langle>x ` n, y ` n\<rangle> \<in> S ` n} \<subseteq> {n\<in>I. ?z`n = y`n}" by auto
  ultimately have "{n\<in>I. ?z`n = y`n}\<in>\<FF>" by auto
  then have "\<langle>?z,y\<rangle>\<in>hyper_rel(X)" unfolding hyper_rel_def using A(4) z by auto
  then have "\<langle>y,?z\<rangle>\<in>hyper_rel(X)" using hyper_sym unfolding sym_def by auto
  then have "hyper_rel(X)``{y} = hyper_rel(X)``{?z}" using equiv_class_eq[OF hyper_equiv]
    by auto
  with A(2) show "internal_fun(S, X)`(hyper_rel(X)``{x}) = hyper_rel(X)``{{\<langle>i, if x ` i \<in> S1 ` i then S ` i ` (x ` i) else x ` i\<rangle> . i \<in> I}}" by auto
qed

lemma internal_fun_apply_2:
  assumes "S1 \<in> (\<Prod>i\<in>I. Pow(X(i)))" "S2 \<in> (\<Prod>i\<in>I. Pow(X(i)))" "S \<in> (\<Prod>i\<in>I. S1 ` i \<rightarrow> S2 ` i)" 
    and "hyper_rel(X)``{x}\<in>internal_set(S1,X)"
  shows "internal_fun(S, X)`(hyper_rel(X)``{x}) = hyper_rel(X)``{{\<langle>i, if x ` i \<in> S1 ` i then S ` i ` (x ` i) else x ` i\<rangle> . i \<in> I}}"
  apply (rule internal_fun_apply) using assms(1) apply simp using assms(2) apply simp
  using assms(3) apply simp
proof-
  from assms(4) obtain y where A:"hyper_rel(X)``{x} = hyper_rel(X)``{y}" "y:Pi(I,X)" "{n\<in>I. y`n\<in>S1`n}\<in>\<FF>"
    unfolding internal_set_def[OF assms(1)] by auto
  from eq_equiv_class[OF A(1) hyper_equiv A(2)] show "x:Pi(I,X)" unfolding hyper_rel_def by auto
  from eq_equiv_class[OF A(1) hyper_equiv A(2)] have "{n\<in>I. x`n = y`n}:\<FF>" unfolding hyper_rel_def by auto
  with A(3) have "{n\<in>I. x`n = y`n} \<inter>{n\<in>I. y`n\<in>S1`n}\<in>\<FF>" using ultraFilter unfolding IsFilter_def IsUltrafilter_def by auto
  moreover have "{n\<in>I. x`n\<in>S1`n}\<in>Pow(I)" by auto
  ultimately have "{n\<in>I. x`n = y`n} \<inter>{n\<in>I. y`n\<in>S1`n} \<subseteq> {n\<in>I. x`n\<in>S1`n} \<longrightarrow> {n\<in>I. x`n\<in>S1`n}:\<FF>"
    using ultraFilter unfolding IsFilter_def IsUltrafilter_def by auto
  then show "{n\<in>I. x`n\<in>S1`n}:\<FF>" by auto
qed
  
lemma internal_fun_inj:
  assumes "S1 \<in> (\<Prod>i\<in>I. Pow(X(i)))" "S2 \<in> (\<Prod>i\<in>I. Pow(X(i)))" "S \<in> (\<Prod>i\<in>I. S1 ` i \<rightarrow> S2 ` i)" 
    and "{i:nat. S`i:inj(S1`i,S2`i)}\<in>\<FF>"
  shows "internal_fun(S, X)\<in>inj(internal_set(S1, X), internal_set(S2, X))"
  unfolding inj_def
proof(safe)
  from internal_fun_is_fun[OF assms(1-3)] show "internal_fun(S, X) \<in> internal_set(S1, X) \<rightarrow> internal_set(S2, X)" by auto
  fix w x assume as:"x\<in>internal_set(S1, X)" "w\<in>internal_set(S1, X)" "internal_fun(S,X)`w = internal_fun(S,X)`x"
  from as(1,2) obtain xx wx where p:"xx:Pi(I,X)" "wx\<in>Pi(I,X)" "{i\<in>I. xx`i \<in>S1`i}\<in>\<FF>"  "{i\<in>I. wx`i \<in>S1`i}\<in>\<FF>"
    "x=hyper_rel(X)``{xx}" "w=hyper_rel(X)``{wx}"
    unfolding internal_set_def[OF assms(1)] by auto
  from as have ap:"hyper_rel(X) ``
    {{\<langle>i, if xx ` i \<in> S1 ` i then S ` i ` (xx ` i) else xx ` i\<rangle> . i \<in> I}} =
hyper_rel(X) `` {{\<langle>i, if wx ` i \<in> S1 ` i then S ` i ` (wx ` i) else wx ` i\<rangle> . i \<in> I}}" using internal_fun_apply_2[OF assms(1-3)] p(5,6)
    by auto moreover
  have ff:"{\<langle>i, if wx ` i \<in> S1 ` i then S ` i ` (wx ` i) else wx ` i\<rangle> . i \<in> I}\<in>Pi(I,X)"
    "{\<langle>i, if xx ` i \<in> S1 ` i then S ` i ` (xx ` i) else xx ` i\<rangle> . i \<in> I}\<in>Pi(I,X)"
    using apply_type[OF assms(1)] apply_type[OF apply_type[OF assms(3)]] unfolding Pi_def function_def
    apply auto prefer 2 using apply_type[OF p(2)] apply simp
    using apply_type[OF assms(2)] apply blast
     prefer 2 using apply_type[OF p(1)] apply simp
    using apply_type[OF assms(2)] by blast
  ultimately have "\<langle>{\<langle>i, if xx ` i \<in> S1 ` i then S ` i ` (xx ` i) else xx ` i\<rangle> . i \<in> I}, {\<langle>i, if wx ` i \<in> S1 ` i then S ` i ` (wx ` i) else wx ` i\<rangle> . i \<in> I}\<rangle>\<in>hyper_rel(X)"
    using eq_equiv_class[OF _ hyper_equiv, of X "{\<langle>i, if xx ` i \<in> S1 ` i then S ` i ` (xx ` i) else xx ` i\<rangle> . i \<in> I}" "{\<langle>i, if wx ` i \<in> S1 ` i then S ` i ` (wx ` i) else wx ` i\<rangle> . i \<in> I}"]
    by auto
  then have Q:"{i\<in>I. {\<langle>i, if xx ` i \<in> S1 ` i then S ` i ` (xx ` i) else xx ` i\<rangle> . i \<in> I}`i = {\<langle>i, if wx ` i \<in> S1 ` i then S ` i ` (wx ` i) else wx ` i\<rangle> . i \<in> I}`i}\<in>\<FF>"
    unfolding hyper_rel_def by auto
  from p(3,4) have "{i\<in>I. xx`i \<in>S1`i}\<inter>{i\<in>I. wx`i \<in>S1`i}\<in>\<FF>" using ultraFilter
    unfolding IsFilter_def IsUltrafilter_def by auto
  then have "\<And>Q. Q:\<FF> \<Longrightarrow> {i\<in>I. xx`i \<in>S1`i}\<inter>{i\<in>I. wx`i \<in>S1`i}\<inter>Q\<in>\<FF>" using ultraFilter
    unfolding IsFilter_def IsUltrafilter_def by auto
  with Q have "{i\<in>I. xx`i \<in>S1`i}\<inter>{i\<in>I. wx`i \<in>S1`i}\<inter>{i\<in>I. {\<langle>i, if xx ` i \<in> S1 ` i then S ` i ` (xx ` i) else xx ` i\<rangle> . i \<in> I}`i = {\<langle>i, if wx ` i \<in> S1 ` i then S ` i ` (wx ` i) else wx ` i\<rangle> . i \<in> I}`i}\<in>\<FF>"
    by auto
  with assms(4) have "{i\<in>I. xx`i \<in>S1`i}\<inter>{i\<in>I. wx`i \<in>S1`i}\<inter>{i\<in>I. {\<langle>i, if xx ` i \<in> S1 ` i then S ` i ` (xx ` i) else xx ` i\<rangle> . i \<in> I}`i = {\<langle>i, if wx ` i \<in> S1 ` i then S ` i ` (wx ` i) else wx ` i\<rangle> . i \<in> I}`i}\<inter>{i \<in> nat . S ` i \<in> inj(S1 ` i, S2 ` i)}:\<FF>"
    using ultraFilter unfolding IsFilter_def IsUltrafilter_def by auto
  then have "\<And>Q. Q\<in>Pow(I) \<Longrightarrow> {i\<in>I. xx`i \<in>S1`i}\<inter>{i\<in>I. wx`i \<in>S1`i}\<inter>{i\<in>I. {\<langle>i, if xx ` i \<in> S1 ` i then S ` i ` (xx ` i) else xx ` i\<rangle> . i \<in> I}`i = {\<langle>i, if wx ` i \<in> S1 ` i then S ` i ` (wx ` i) else wx ` i\<rangle> . i \<in> I}`i}\<inter>{i \<in> nat . S ` i \<in> inj(S1 ` i, S2 ` i)} \<subseteq> Q \<Longrightarrow> Q:\<FF>"
    using ultraFilter unfolding IsFilter_def IsUltrafilter_def by auto moreover
  {
    fix i assume "i\<in>{i\<in>I. xx`i \<in>S1`i}\<inter>{i\<in>I. wx`i \<in>S1`i}\<inter>{i\<in>I. {\<langle>i, if xx ` i \<in> S1 ` i then S ` i ` (xx ` i) else xx ` i\<rangle> . i \<in> I}`i = {\<langle>i, if wx ` i \<in> S1 ` i then S ` i ` (wx ` i) else wx ` i\<rangle> . i \<in> I}`i}\<inter>{i \<in> nat . S ` i \<in> inj(S1 ` i, S2 ` i)}"
    then have i:"i\<in>I" "xx`i\<in>S1`i" "wx`i\<in>S1`i" "S ` i ` (xx ` i) = S ` i ` (wx ` i)" "S`i\<in>inj(S1`i,S2`i)" using apply_equality ff by auto
    from i(2-5) have "xx`i = wx`i" unfolding inj_def by auto
    with i(1) have "i\<in>{i\<in>I. xx`i = wx`i}" by auto
  }
  then have "{i\<in>I. xx`i \<in>S1`i}\<inter>{i\<in>I. wx`i \<in>S1`i}\<inter>{i\<in>I. {\<langle>i, if xx ` i \<in> S1 ` i then S ` i ` (xx ` i) else xx ` i\<rangle> . i \<in> I}`i = {\<langle>i, if wx ` i \<in> S1 ` i then S ` i ` (wx ` i) else wx ` i\<rangle> . i \<in> I}`i}\<inter>{i \<in> nat . S ` i \<in> inj(S1 ` i, S2 ` i)} \<subseteq> {i\<in>I. xx`i = wx`i}" by auto
  moreover have "{i\<in>I. xx`i = wx`i}\<in>Pow(I)" by auto
  ultimately have "{i\<in>I. xx`i = wx`i}:\<FF>" using ultraFilter unfolding IsFilter_def IsUltrafilter_def
    by auto
  then have "\<langle>xx,wx\<rangle>\<in>hyper_rel(X)" unfolding hyper_rel_def using p(1,2) by auto
  then show "w = x" using equiv_class_eq[OF hyper_equiv, THEN sym] p(5,6) by auto
qed

end
end
