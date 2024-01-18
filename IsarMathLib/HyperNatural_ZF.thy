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

section \<open>Hyper natural numbers\<close>

theory HyperNatural_ZF imports UltraConstruction_ZF FinOrd_ZF
begin

text\<open>This theory deals with hyper numbers.\<close>

locale hyperNatural = ultra _ nat +
  assumes non_pricipal_filter:"\<Inter>\<FF> = 0"

begin

abbreviation hyperNat ("*\<nat>") where
"*\<nat> \<equiv> hyper_set(\<lambda>_. nat)"

definition seq_class ("[_]") where
"x\<in>nat\<rightarrow>nat \<Longrightarrow> [x] \<equiv> hyper_rel(\<lambda>_. nat)``{x}"

definition omega ("\<omega>") where
"\<omega> = [id(nat)]"

definition incl ("*_" 70) where
"x\<in>nat \<Longrightarrow> *x \<equiv> [ConstantFunction(nat,x)]"

lemma incl_inj_nat:
  shows "{\<langle>x,*x\<rangle>. x\<in>nat} \<in> inj(nat, *\<nat>)" using incl_inj[of nat] 
    seq_class_def[OF func1_3_L1] incl_def
  unfolding incl_def by auto

lemma omega_not_nat:
  shows "x\<in>nat\<longrightarrow>(*x) \<noteq> \<omega>" and "\<omega>:*\<nat>"
proof
  have "id(nat):nat\<rightarrow>nat" using id_def by auto
  then have "[id(nat)]:*\<nat>" using seq_class_def[of "id(nat)"]
    unfolding hyper_set_def quotient_def by auto
  then show "\<omega>:*\<nat>" unfolding omega_def by auto
  {
    assume a:"x\<in>nat" "(*x) = \<omega>"
    from a(2) have "[ConstantFunction(nat,x)] = [id(nat)]"
      unfolding omega_def incl_def[OF a(1)].
    then have "\<langle>ConstantFunction(nat,x),id(nat)\<rangle>\<in>hyper_rel(\<lambda>_. nat)"
      using same_image_equiv[OF hyper_equiv, of "id(nat)"] inj_is_fun[OF id_inj]
      unfolding seq_class_def[OF inj_is_fun[OF id_inj]] seq_class_def[OF func1_3_L1[OF a(1)]] by auto
    then have "{n\<in>nat. ConstantFunction(nat,x)`n = id(nat)`n}:\<FF>" unfolding hyper_rel_def by auto
    then have "{n\<in>nat. x = n}:\<FF>" using apply_equality[of _ _ "id(nat)" nat "\<lambda>_. nat"] inj_is_fun[OF id_inj]
      func1_3_L2[of _ nat x] by auto moreover
    have "{n\<in>nat. x = n} = {x}" using a(1) by auto ultimately
    have f:"{x}:\<FF>" by auto
    {
      fix A assume x:"x\<in>A" "A\<subseteq> nat"
      then have "{x} \<subseteq> A" by auto
      then have "A:\<FF>" using f ultraFilter x(2) unfolding IsFilter_def IsUltrafilter_def by auto
    }
    then have "{A\<in>Pow(nat). x:A} \<subseteq> \<FF>" by auto moreover
    {
      fix A assume a:"A\<in>\<FF>"
      with f have y:"A\<inter>{x}:\<FF>" using ultraFilter unfolding IsFilter_def IsUltrafilter_def
          by auto
      {
        assume "x\<notin>A"
        then have "A\<inter>{x} = 0" by auto
        with y have "0:\<FF>" by auto
        then have False using ultraFilter unfolding IsFilter_def IsUltrafilter_def by auto
      }
      then have "x:A" by auto
      moreover from a have "A\<in>Pow(nat)" using ultraFilter unfolding IsFilter_def IsUltrafilter_def by auto
      ultimately have "A\<in>{A\<in>Pow(nat). x:A}" by auto
    }
    then have "\<FF> \<subseteq> {A\<in>Pow(nat). x:A}" by auto ultimately
    have "\<FF> = {A\<in>Pow(nat). x:A}" by auto
    then have "\<FF>=0 \<or> x\<in>\<Inter>\<FF>" by auto
    with non_pricipal_filter have "\<FF>=0" by auto
    then have False using ultraFilter unfolding IsFilter_def IsUltrafilter_def by auto
  }
  then show "x \<in> nat \<Longrightarrow> (*x) \<noteq> \<omega>" using ultraFilter unfolding IsFilter_def IsUltrafilter_def by auto
qed

text\<open>We define the order relation as the internal relation created
by a constant relation of order in natural numbers\<close>

definition lessEq (infix "*\<le>" 80) where
"x*\<le>y \<equiv> \<langle>x,y\<rangle>\<in>internal_rel({\<langle>n,{\<langle>x,y\<rangle>\<in>nat\<times>nat. x\<le>y}\<rangle>. n\<in>nat},\<lambda>_. nat)"

text\<open>We define the order relation as the internal relation created
by a constant relation of order in natural numbers\<close>

definition lessStrEq (infix "*<" 80) where
"x*<y \<equiv> \<langle>x,y\<rangle>\<in>internal_rel({\<langle>n,{\<langle>x,y\<rangle>\<in>nat\<times>nat. x<y}\<rangle>. n\<in>nat},\<lambda>_. nat)"

text\<open>Two hyper naturals are ordered iff where their representative sequences are ordered
is a set in the filter\<close>

lemma less_than_seq:
  assumes "x:nat\<rightarrow>nat" "y:nat\<rightarrow>nat"
  shows "[x] *\<le> [y] \<longleftrightarrow> {i\<in>nat. x`i \<le> y`i}\<in>\<FF>"
proof(safe)
  have S_fun:"{\<langle>n,{\<langle>x,y\<rangle>\<in>nat\<times>nat. x\<le>y}\<rangle>. n\<in>nat}:nat \<rightarrow> Pow(nat\<times>nat)" unfolding Pi_def
function_def by auto
  {
    assume "[x] *\<le> [y]"
    then have "\<langle>[x],[y]\<rangle>\<in>internal_rel({\<langle>n,{\<langle>x,y\<rangle>\<in>nat\<times>nat. x\<le>y}\<rangle>. n\<in>nat},\<lambda>_. nat)"
      unfolding lessEq_def.
    then obtain z t where zt:"[x] = [z]" "[y] = [t]" "z:nat\<rightarrow>nat " "t:nat\<rightarrow>nat"
"{n \<in> nat . \<langle>z ` n, t ` n\<rangle> \<in> {\<langle>n, {\<langle>x,y\<rangle> \<in> nat \<times> nat . x \<le> y}\<rangle> . n \<in> nat} ` n} \<in> \<FF>"
      unfolding internal_rel_def[OF S_fun] using seq_class_def by auto
    from zt(5) have "{n \<in> nat . \<langle>z ` n, t ` n\<rangle> \<in> {\<langle>x,y\<rangle> \<in> nat \<times> nat . x \<le> y}} \<in> \<FF>"
      using apply_equality S_fun by auto
    then have A:"{n \<in> nat . z ` n \<le> t ` n} \<in> \<FF>"
      using apply_type[OF zt(3)] apply_type[OF zt(4)] by auto
    from zt(1) have "\<langle>x,z\<rangle>\<in>hyper_rel(\<lambda>_. nat)" unfolding seq_class_def[OF zt(3)]
      seq_class_def[OF assms(1)] using eq_equiv_class[OF _ hyper_equiv zt(3)] by auto
    then have "{n:nat. x`n = z`n}\<in>\<FF>" unfolding hyper_rel_def by auto
    with A have A:"{n \<in> nat . z ` n \<le> t ` n}\<inter>{n:nat. x`n = z`n}\<in>\<FF>" using ultraFilter
      unfolding IsFilter_def IsUltrafilter_def by auto
    from zt(2) have "\<langle>y,t\<rangle>\<in>hyper_rel(\<lambda>_. nat)" unfolding seq_class_def[OF zt(4)]
      seq_class_def[OF assms(2)] using eq_equiv_class[OF _ hyper_equiv zt(4)] by auto
    then have "{n:nat. y`n = t`n}\<in>\<FF>" unfolding hyper_rel_def by auto
    with A have "{n:nat. y`n = t`n}\<inter>({n \<in> nat . z ` n \<le> t ` n}\<inter>{n:nat. x`n = z`n})\<in>\<FF>" using ultraFilter
      unfolding IsFilter_def IsUltrafilter_def by auto
    then have "\<forall>B\<in>Pow(nat). {n:nat. y`n = t`n}\<inter>({n \<in> nat . z ` n \<le> t ` n}\<inter>{n:nat. x`n = z`n}) \<subseteq> B \<longrightarrow> B\<in>\<FF>"
      using ultraFilter unfolding IsFilter_def IsUltrafilter_def by auto
    then have "{n\<in>nat. x`n \<le> y`n}\<in>Pow(nat) \<Longrightarrow> {n:nat. y`n = t`n}\<inter>({n \<in> nat . z ` n \<le> t ` n}\<inter>{n:nat. x`n = z`n}) \<subseteq> {n\<in>nat. x`n \<le> y`n} \<Longrightarrow> {n\<in>nat. x`n \<le> y`n}\<in>\<FF>"
      by auto
    then have "{n:nat. y`n = t`n}\<inter>({n \<in> nat . z ` n \<le> t ` n}\<inter>{n:nat. x`n = z`n}) \<subseteq> {n\<in>nat. x`n \<le> y`n} \<Longrightarrow> {n\<in>nat. x`n \<le> y`n}\<in>\<FF>" by auto moreover
    {
      fix n assume "n\<in>{n:nat. y`n = t`n}\<inter>({n \<in> nat . z ` n \<le> t ` n}\<inter>{n:nat. x`n = z`n})"
      then have "n\<in>nat" "y`n = t`n" "z`n \<le> t`n" "x`n = z`n" by auto
      then have "n\<in>nat" "x`n \<le> y`n" by auto
      then have "n\<in>{n\<in>nat. x`n \<le> y`n}" by auto
    }
    then have "{n:nat. y`n = t`n}\<inter>({n \<in> nat . z ` n \<le> t ` n}\<inter>{n:nat. x`n = z`n}) \<subseteq> {n\<in>nat. x`n \<le> y`n}" by auto
    ultimately show "{n\<in>nat. x`n \<le> y`n}\<in>\<FF>" by auto
  }
  {
    assume "{n\<in>nat. x`n \<le> y`n}\<in>\<FF>" 
    then have "{n \<in> nat . \<langle>x ` n, y ` n\<rangle> \<in> {\<langle>n, {\<langle>x,y\<rangle> \<in> nat \<times> nat . x \<le> y}\<rangle> . n \<in> nat} ` n} \<in> \<FF>"
      using apply_equality[OF _ S_fun] apply_type[OF assms(1)] apply_type[OF assms(2)] by auto
    with assms have "\<langle>[x],[y]\<rangle>\<in>internal_rel({\<langle>n,{\<langle>x,y\<rangle>\<in>nat\<times>nat. x\<le>y}\<rangle>. n\<in>nat},\<lambda>_. nat)"
      unfolding internal_rel_def[OF S_fun] seq_class_def[OF assms(1)] seq_class_def[OF assms(2)]
      by auto
    then show "[x] *\<le> [y]" unfolding lessEq_def.
  }
qed

lemma less_seq:
  assumes "x:nat\<rightarrow>nat" "y:nat\<rightarrow>nat"
  shows "[x] *< [y] \<longleftrightarrow> {i\<in>nat. x`i < y`i}\<in>\<FF>"
proof(safe)
  have S_fun:"{\<langle>n,{\<langle>x,y\<rangle>\<in>nat\<times>nat. x<y}\<rangle>. n\<in>nat}:nat \<rightarrow> Pow(nat\<times>nat)" unfolding Pi_def
function_def by auto
  {
    assume "[x] *< [y]"
    then have "\<langle>[x],[y]\<rangle>\<in>internal_rel({\<langle>n,{\<langle>x,y\<rangle>\<in>nat\<times>nat. x<y}\<rangle>. n\<in>nat},\<lambda>_. nat)"
      unfolding lessStrEq_def.
    then obtain z t where zt:"[x] = [z]" "[y] = [t]" "z:nat\<rightarrow>nat " "t:nat\<rightarrow>nat"
"{n \<in> nat . \<langle>z ` n, t ` n\<rangle> \<in> {\<langle>n, {\<langle>x,y\<rangle> \<in> nat \<times> nat . x < y}\<rangle> . n \<in> nat} ` n} \<in> \<FF>"
      unfolding internal_rel_def[OF S_fun] using seq_class_def by auto
    from zt(5) have "{n \<in> nat . \<langle>z ` n, t ` n\<rangle> \<in> {\<langle>x,y\<rangle> \<in> nat \<times> nat . x < y}} \<in> \<FF>"
      using apply_equality S_fun by auto
    then have A:"{n \<in> nat . z ` n < t ` n} \<in> \<FF>"
      using apply_type[OF zt(3)] apply_type[OF zt(4)] by auto
    from zt(1) have "\<langle>x,z\<rangle>\<in>hyper_rel(\<lambda>_. nat)" unfolding seq_class_def[OF zt(3)]
      seq_class_def[OF assms(1)] using eq_equiv_class[OF _ hyper_equiv zt(3)] by auto
    then have "{n:nat. x`n = z`n}\<in>\<FF>" unfolding hyper_rel_def by auto
    with A have A:"{n \<in> nat . z ` n < t ` n}\<inter>{n:nat. x`n = z`n}\<in>\<FF>" using ultraFilter
      unfolding IsFilter_def IsUltrafilter_def by auto
    from zt(2) have "\<langle>y,t\<rangle>\<in>hyper_rel(\<lambda>_. nat)" unfolding seq_class_def[OF zt(4)]
      seq_class_def[OF assms(2)] using eq_equiv_class[OF _ hyper_equiv zt(4)] by auto
    then have "{n:nat. y`n = t`n}\<in>\<FF>" unfolding hyper_rel_def by auto
    with A have "{n:nat. y`n = t`n}\<inter>({n \<in> nat . z ` n < t ` n}\<inter>{n:nat. x`n = z`n})\<in>\<FF>" using ultraFilter
      unfolding IsFilter_def IsUltrafilter_def by auto
    then have "\<forall>B\<in>Pow(nat). {n:nat. y`n = t`n}\<inter>({n \<in> nat . z ` n < t ` n}\<inter>{n:nat. x`n = z`n}) \<subseteq> B \<longrightarrow> B\<in>\<FF>"
      using ultraFilter unfolding IsFilter_def IsUltrafilter_def by auto
    then have "{n\<in>nat. x`n < y`n}\<in>Pow(nat) \<Longrightarrow> {n:nat. y`n = t`n}\<inter>({n \<in> nat . z ` n < t ` n}\<inter>{n:nat. x`n = z`n}) \<subseteq> {n\<in>nat. x`n < y`n} \<Longrightarrow> {n\<in>nat. x`n < y`n}\<in>\<FF>"
      by auto
    then have "{n:nat. y`n = t`n}\<inter>({n \<in> nat . z ` n < t ` n}\<inter>{n:nat. x`n = z`n}) \<subseteq> {n\<in>nat. x`n < y`n} \<Longrightarrow> {n\<in>nat. x`n < y`n}\<in>\<FF>" by auto moreover
    {
      fix n assume "n\<in>{n:nat. y`n = t`n}\<inter>({n \<in> nat . z ` n < t ` n}\<inter>{n:nat. x`n = z`n})"
      then have "n\<in>nat" "y`n = t`n" "z`n < t`n" "x`n = z`n" by auto
      then have "n\<in>nat" "x`n < y`n" by auto
      then have "n\<in>{n\<in>nat. x`n < y`n}" by auto
    }
    then have "{n:nat. y`n = t`n}\<inter>({n \<in> nat . z ` n < t ` n}\<inter>{n:nat. x`n = z`n}) \<subseteq> {n\<in>nat. x`n < y`n}" by auto
    ultimately show "{n\<in>nat. x`n < y`n}\<in>\<FF>" by auto
  }
  {
    assume "{n\<in>nat. x`n <y`n}\<in>\<FF>" 
    then have "{n \<in> nat . \<langle>x ` n, y ` n\<rangle> \<in> {\<langle>n, {\<langle>x,y\<rangle> \<in> nat \<times> nat . x < y}\<rangle> . n \<in> nat} ` n} \<in> \<FF>"
      using apply_equality[OF _ S_fun] apply_type[OF assms(1)] apply_type[OF assms(2)] by auto
    with assms have "\<langle>[x],[y]\<rangle>\<in>internal_rel({\<langle>n,{\<langle>x,y\<rangle>\<in>nat\<times>nat. x<y}\<rangle>. n\<in>nat},\<lambda>_. nat)"
      unfolding internal_rel_def[OF S_fun] seq_class_def[OF assms(1)] seq_class_def[OF assms(2)]
      by auto
    then show "[x] *< [y]" unfolding lessStrEq_def.
  }
qed

text\<open>It is a linear order\<close>

lemma order_linear:
  shows "IsLinOrder(*\<nat>, {\<langle>x,y\<rangle>\<in>*\<nat>\<times>*\<nat>. x *\<le> y})" unfolding IsLinOrder_def
antisym_def trans_def IsTotal_def apply auto
proof-
  fix x y assume as:" x \<in> *\<nat>" "y \<in> *\<nat>" "x *\<le> y" "y *\<le> x"
  from as(1,2) obtain xx xy where xy:"xx:nat\<rightarrow>nat" "xy:nat\<rightarrow>nat" "[xx] = x"  "[xy] = y"
    unfolding hyper_set_def quotient_def using seq_class_def by auto
  from xy as(3,4) have "{i \<in> nat . xx ` i \<le> xy ` i} \<in> \<FF>"  "{i \<in> nat . xy ` i \<le> xx ` i} \<in> \<FF>"
    using less_than_seq by auto
  then have "{i \<in> nat . xx ` i \<le> xy ` i} \<inter>{i \<in> nat . xy ` i \<le> xx ` i} \<in> \<FF>" using ultraFilter
    unfolding IsFilter_def IsUltrafilter_def by auto moreover
  have "{i \<in> nat . xx ` i \<le> xy ` i} \<inter>{i \<in> nat . xy ` i \<le> xx ` i} \<subseteq> {i \<in> nat . xx ` i = xy ` i}"
    using le_anti_sym by auto moreover
  have "{i \<in> nat . xx ` i = xy ` i}:Pow(nat)" by auto
  ultimately have "{i \<in> nat . xx ` i = xy ` i}:\<FF>" using ultraFilter unfolding IsFilter_def IsUltrafilter_def by auto
  then have "\<langle>xx,xy\<rangle>\<in>hyper_rel(\<lambda>_. nat)" unfolding hyper_rel_def using xy(1,2) by auto
  then show "x = y" using equiv_class_eq[OF hyper_equiv] seq_class_def xy by auto
next
  fix x y z assume as:"x \<in> *\<nat>" "y \<in> *\<nat>" "x *\<le> y" "z \<in> *\<nat>" "y *\<le> z"
  from as(1,2,4) obtain xx xy xz where xyz:"xx:nat\<rightarrow>nat" "xy:nat\<rightarrow>nat" "xz:nat\<rightarrow>nat" "[xx] = x"  "[xy] = y" "[xz] = z"
    unfolding hyper_set_def quotient_def using seq_class_def by auto
  from xyz as(3,5) have "{i \<in> nat . xx ` i \<le> xy ` i} \<in> \<FF>" "{i \<in> nat . xy ` i \<le> xz ` i} \<in> \<FF>" 
    using less_than_seq by auto
  then have "{i \<in> nat . xx ` i \<le> xy ` i} \<inter>{i \<in> nat . xy ` i \<le> xz ` i} \<in> \<FF>" using ultraFilter
    unfolding IsFilter_def IsUltrafilter_def by auto moreover
  have "{i \<in> nat . xx ` i \<le> xy ` i} \<inter>{i \<in> nat . xy ` i \<le> xz ` i} \<subseteq> {i \<in> nat . xx ` i \<le> xz ` i}"
    using le_trans by auto moreover
  have "{i \<in> nat . xx ` i \<le> xz ` i}:Pow(nat)" by auto
  ultimately have "{i \<in> nat . xx ` i \<le> xz ` i}:\<FF>" using ultraFilter unfolding IsFilter_def IsUltrafilter_def by auto
  then show "x *\<le> z" using less_than_seq xyz by auto
next
  fix x y assume as:"x \<in> *\<nat>" "y \<in> *\<nat>" "\<not>(x *\<le> y)"
  from as(1,2) obtain xx xy where xy:"xx:nat\<rightarrow>nat" "xy:nat\<rightarrow>nat" "[xx] = x"  "[xy] = y"
    unfolding hyper_set_def quotient_def using seq_class_def by auto
  from xy as(3) have "{i \<in> nat . xx ` i \<le> xy ` i} \<notin> \<FF>" using less_than_seq by auto
  then have "nat-{i \<in> nat . xx ` i \<le> xy ` i} \<in> \<FF>" using set_ultrafilter[OF _ ultraFilter, of "{i \<in> nat . xx ` i \<le> xy ` i}"] by auto
  then have "\<And>Q. Q\<in>Pow(nat) \<Longrightarrow> nat-{i \<in> nat . xx ` i \<le> xy ` i} \<subseteq> Q \<Longrightarrow> Q \<in> \<FF>" using ultraFilter unfolding IsFilter_def IsUltrafilter_def by auto
  moreover have "{i \<in> nat . (xy ` i \<le> xx ` i)} :Pow(nat)" by auto moreover
  {
    fix n assume "n\<in>nat-{i \<in> nat . xx ` i \<le> xy ` i}"
    then have n:"n:nat" "\<not> xx`n \<le>xy`n" by auto
    from apply_type n(1) have "xx`n:nat" "xy`n:nat" using xy(1,2) by auto
    then have "\<langle>xx`n,xy`n\<rangle>\<in>Le \<or> \<langle>xy`n,xx`n\<rangle>\<in>Le" using NatOrder_ZF_1_L2(3) unfolding IsTotal_def by auto
    with n(2) have "xy`n\<le>xx`n" unfolding Le_def by auto
    then have "n:{i \<in> nat . xy ` i \<le> xx ` i}" using n(1) by auto
  }
  then have "nat-{i \<in> nat . xx ` i \<le> xy ` i} \<subseteq> {i \<in> nat . xy ` i \<le> xx ` i}" by auto ultimately
  have "{i \<in> nat . xy ` i \<le> xx ` i}:\<FF>" by auto
  then show "y *\<le> x" using less_than_seq[OF xy(2,1)] xy(3,4) by auto
qed

text\<open>The strict version\<close>

lemma strict_order:
  assumes "x:*\<nat>" "y:*\<nat>"
  shows "(x *\<le> y \<and> x\<noteq>y) \<longleftrightarrow> x *< y"
proof(safe)
  from assms(1,2) obtain xx xy where xy:"xx:nat\<rightarrow>nat" "xy:nat\<rightarrow>nat" "[xx] = x"  "[xy] = y"
    unfolding hyper_set_def quotient_def using seq_class_def by auto
  {
    assume as:"x *\<le> y" "x\<noteq>y"
    from as(1) xy have A:"{i:nat. xx`i \<le> xy`i}:\<FF>" using less_than_seq by auto
    {
      assume "{i:nat. xx`i = xy`i}:\<FF>"
      then have "x=y" using xy(3,4) equiv_class_eq[OF hyper_equiv, of xx xy] unfolding seq_class_def[OF xy(1)]
        seq_class_def[OF xy(2)] unfolding hyper_rel_def using xy(1,2) by auto
      with as(2) have False by auto
    }
    then have "{i:nat. xx`i = xy`i}\<notin>\<FF>" by auto
    then have "nat-{i:nat. xx`i = xy`i}\<in>\<FF>" using set_ultrafilter[OF _ ultraFilter, of "{i:nat. xx`i = xy`i}"] by auto
    moreover have "nat-{i:nat. xx`i = xy`i} = {i:nat. xx`i \<noteq> xy`i}" by auto
    ultimately have "{i:nat. xx`i \<noteq> xy`i} :\<FF>" by auto
    with A have "{i:nat. xx`i \<noteq> xy`i}\<inter>{i:nat. xx`i \<le> xy`i}:\<FF>" using ultraFilter unfolding IsFilter_def IsUltrafilter_def by auto moreover
    {
      fix i assume  "i:{i:nat. xx`i \<noteq> xy`i}\<inter>{i:nat. xx`i \<le> xy`i}"
      then have "i\<in>nat" "xx`i < xy`i" using le_iff by auto
      then have "i\<in>{i:nat. xx`i < xy`i}" by auto
    }
    then have "{i:nat. xx`i \<noteq> xy`i}\<inter>{i:nat. xx`i \<le> xy`i}\<subseteq>{i:nat. xx`i < xy`i}" by auto
    moreover have "{i:nat. xx`i < xy`i}:Pow(nat)" by auto
    ultimately have "{i:nat. xx`i < xy`i}:\<FF>" using ultraFilter unfolding IsFilter_def IsUltrafilter_def by auto
    then show "x *< y" using less_seq[OF xy(1,2)] xy(3,4) by auto
  }
  {
    assume as:"x *< y"
    then have "{i\<in>nat. xx`i < xy`i}:\<FF>" using less_seq xy by auto moreover
    have "{i\<in>nat. xx`i \<le> xy`i}:Pow(nat)" by auto moreover
    have "{i\<in>nat. xx`i < xy`i} \<subseteq> {i\<in>nat. xx`i \<le> xy`i}" using leI by auto ultimately
    have "{i\<in>nat. xx`i \<le> xy`i}:\<FF>" using ultraFilter unfolding IsFilter_def IsUltrafilter_def by auto
    then show "x *\<le> y" using less_than_seq xy by auto
  }
  {
    assume "y *<y"
    then have "{i\<in>nat. xy`i < xy`i}:\<FF>" using less_seq xy(2,4) by auto
    then have "0:\<FF>" using lt_not_refl by auto
    then show False using ultraFilter unfolding IsFilter_def IsUltrafilter_def by auto
  }
qed      

text\<open>There is a hyper natural bigger than all natural numbers\<close>

lemma omega_bigger_naturals:
  assumes "x:nat"
  shows "(*x) *< \<omega>"
proof-
  from assms have "(*x) = [ConstantFunction(nat,x)]"
    using incl_def by auto
  have "{n\<in>nat. ConstantFunction(nat,x)`n < id(nat)`n} = {n\<in>nat. x < n}"
    using func1_3_L2[of _ nat x] id_iff by auto
  have "nat-{n\<in>nat. x < n}\<in>FinPow(nat)" apply (rule nat_induct[of x "\<lambda>q. nat-{n\<in>nat. q < n}\<in>FinPow(nat)"])
  proof-
    from assms show "x\<in>nat".
    have "{n \<in> nat . 0 < n} = nat-{0}" using Ord_0_lt[OF nat_into_Ord] lt_irrefl[of 0 False] by auto
    then have "nat-{n \<in> nat . 0 < n} = {0}" by auto
    then show "nat-{n \<in> nat . 0 < n}\<in>FinPow(nat)" unfolding FinPow_def by auto
    {
      fix x assume x:"x\<in>nat" "nat - {n \<in> nat . x < n} \<in> FinPow(nat)"
      {
        fix t assume t:"t\<in>(nat - {n \<in> nat . x < n})\<union>{succ(x)}"
        {
          assume e:"t=succ(x)"
          then have "t\<in>nat" using x(1) by auto moreover
          {
            assume "succ(x) < x"
            then have "x < x" using leI by auto
            then have False by auto
          } moreover note e
          ultimately have "t\<in>nat-{n \<in> nat. succ(x) < n}" by blast
        } moreover
        {
          assume e:"t\<noteq>succ(x)"
          with t have t:"t\<in>nat - {n \<in> nat . x < n}" by auto
          then have tnat:"t\<in>nat" by auto
          {
            assume "succ(x)<t"
            then have "x<t" using le_refl[OF nat_into_Ord[OF x(1)]] lt_trans[of x "succ(x)" t] by auto
            with t have False by auto
          }
          with tnat have "t\<in>nat-{n \<in> nat. succ(x) < n}" by auto
        } ultimately
        have "t\<in>nat-{n \<in> nat. succ(x) < n}" by auto
      }
      then have "(nat - {n \<in> nat . x < n}) \<union> {succ(x)} \<subseteq> nat - {n \<in> nat . succ(x) < n}" by auto moreover
      {
        fix t assume t:"t\<in>nat - {n \<in> nat . succ(x) < n}"
        {
          assume tn:"t\<noteq>succ(x)"
          {
            assume tx: "x < t"
            then have "succ(x)\<le>t" using succ_leI by auto
            with tn have "succ(x)<t" using le_iff by auto
            with t have False by auto
          }
          with t have "t\<in>nat - {n \<in> nat . x < n}" by auto
        }
        then have "t\<in>nat - {n \<in> nat . x < n} \<union> {succ(x)}" by auto
      }
      then have "nat - {n \<in> nat . succ(x) < n} \<subseteq> nat - {n \<in> nat . x < n} \<union> {succ(x)}" by auto
      ultimately have "nat - {n \<in> nat . succ(x) < n} = nat - {n \<in> nat . x < n} \<union> {succ(x)}" by auto
      then show "nat - {n \<in> nat . succ(x) < n}\<in>FinPow(nat)" 
        using union_finpow[OF x(2) singleton_in_finpow[OF nat_succI[OF x(1)]]] by auto
    }
  qed moreover
  {
    fix x assume as:"x\<in>nat" "{x}:\<FF>"
    {
      fix A assume x:"x\<in>A" "A\<subseteq> nat"
      then have "{x} \<subseteq> A" by auto
      then have "A:\<FF>" using as(2) ultraFilter x(2) unfolding IsFilter_def IsUltrafilter_def by auto
    }
    then have "{A\<in>Pow(nat). x:A} \<subseteq> \<FF>" by auto moreover
    {
      fix A assume a:"A\<in>\<FF>"
      with as(2) have y:"A\<inter>{x}:\<FF>" using ultraFilter unfolding IsFilter_def IsUltrafilter_def
          by auto
      {
        assume "x\<notin>A"
        then have "A\<inter>{x} = 0" by auto
        with y have "0:\<FF>" by auto
        then have False using ultraFilter unfolding IsFilter_def IsUltrafilter_def by auto
      }
      then have "x:A" by auto
      moreover from a have "A\<in>Pow(nat)" using ultraFilter unfolding IsFilter_def IsUltrafilter_def by auto
      ultimately have "A\<in>{A\<in>Pow(nat). x:A}" by auto
    }
    then have "\<FF> \<subseteq> {A\<in>Pow(nat). x:A}" by auto ultimately
    have "\<FF> = {A\<in>Pow(nat). x:A}" by auto
    then have "\<FF>=0 \<or> x\<in>\<Inter>\<FF>" by auto
    with non_pricipal_filter have "\<FF>=0" by auto
    then have False using ultraFilter unfolding IsFilter_def IsUltrafilter_def by auto
  }
  then have "\<forall>x\<in>nat. {x} \<notin> \<FF>" by auto
  ultimately have "nat - {n \<in> nat . x < n}\<notin>\<FF>" using ultrafilter_finite_set[OF ultraFilter]
    by auto
  then have "{n \<in> nat . x < n}:\<FF>" using ultraFilter set_ultrafilter[of "{n \<in> nat . x < n}"] by auto
  then have "{n\<in>nat. ConstantFunction(nat,x)`n < id(nat)`n}:\<FF>"
    using func1_3_L2[of _ nat x] by auto
  then have "[ConstantFunction(nat,x)]*<[id(nat)]" using less_seq[OF func1_3_L1 inj_is_fun[OF id_inj]]
    assms by auto
  then show ?thesis unfolding omega_def incl_def[OF assms] by auto
qed

text\<open>Every function on the natural numbers can be extended to a function on the hyper naturals\<close>

definition hyper_fun ("\<^sup>*_\<^sub>*") where
"f:nat\<rightarrow>nat \<Longrightarrow> \<^sup>*f\<^sub>* \<equiv> internal_fun(ConstantFunction(nat,f),\<lambda>_. nat)"

lemma hyper_fun_on_nat:
  assumes "f\<in>nat\<rightarrow>nat" "x\<in>nat"
  shows "\<^sup>*f\<^sub>*`(*x) = *(f`x)"
proof-
  have e:"\<^sup>*f\<^sub>*`(*x) = internal_fun(ConstantFunction(nat,f),\<lambda>_. nat)` (hyper_rel(\<lambda>_. nat)``{ConstantFunction(nat,x)})"
    unfolding hyper_fun_def[OF assms(1)] incl_def[OF assms(2)] seq_class_def[OF func1_3_L1[OF assms(2)]] by auto
  have A:"ConstantFunction(nat,nat):nat\<rightarrow>Pow(nat)" using func1_3_L1 by auto
  have B:"ConstantFunction(nat,f):(\<Prod>i\<in>nat. ConstantFunction(nat, nat) ` i \<rightarrow> ConstantFunction(nat, nat) ` i)"
    unfolding Pi_def function_def Sigma_def apply auto unfolding ConstantFunction_def apply auto
      prefer 2 using assms(1) func1_3_L2[of _ nat nat] unfolding Pi_def ConstantFunction_def apply auto
    unfolding function_def by blast
  have "{\<langle>i,nat\<rangle>. i\<in>nat} = ConstantFunction(nat,nat)" unfolding ConstantFunction_def by auto
  then have "internal_set(ConstantFunction(nat,nat), \<lambda>_. nat) = *\<nat>" using internal_total_set[of "\<lambda>_. nat"] by auto
  then have C:"hyper_rel(\<lambda>_. nat) `` {ConstantFunction(nat, x)} \<in>
    internal_set(ConstantFunction(nat, nat), \<lambda>_. nat)" unfolding hyper_set_def quotient_def
    using func1_3_L1[OF assms(2)] by auto
  from e have "\<^sup>*f\<^sub>*`(*x) =hyper_rel(\<lambda>_. nat) ``
    {{\<langle>i, if ConstantFunction(nat, x) ` i \<in> ConstantFunction(nat, nat) ` i
          then ConstantFunction(nat, f) ` i ` (ConstantFunction(nat, x) ` i)
          else ConstantFunction(nat, x) ` i\<rangle> .
      i \<in> nat}}"
    using internal_fun_apply_2[of "ConstantFunction(nat,nat)" "\<lambda>_. nat" "ConstantFunction(nat,nat)" "ConstantFunction(nat,f)"
        "ConstantFunction(nat,x)", OF A A B C] by auto
  then have "\<^sup>*f\<^sub>*`(*x) =hyper_rel(\<lambda>_. nat) ``
    {{\<langle>i, if x \<in> nat then f ` x else x\<rangle>. i \<in> nat}}"
    using func1_3_L2[of _ nat] by auto
  with assms(2) have "\<^sup>*f\<^sub>*`(*x) =hyper_rel(\<lambda>_. nat) ``{{\<langle>i,f`x\<rangle>. i\<in>nat}}" by auto
  then show ?thesis unfolding seq_class_def[OF func1_3_L1[OF apply_type[OF assms]]] incl_def[OF apply_type[OF assms]]
    unfolding ConstantFunction_def by auto
qed

text\<open>Applying a function extended from the natural numbers to the class
of certain sequence gives out the sequence of the composition\<close>

lemma hyper_fun_on_nat_2:
  assumes "f\<in>nat\<rightarrow>nat" "x\<in>nat\<rightarrow>nat"
  shows "\<^sup>*f\<^sub>*`([x]) = [f O x]"
proof-
  have e:"\<^sup>*f\<^sub>*`([x]) = internal_fun(ConstantFunction(nat,f),\<lambda>_. nat)` (hyper_rel(\<lambda>_. nat)``{x})"
    unfolding hyper_fun_def[OF assms(1)] seq_class_def[OF assms(2)] by auto
  have A:"ConstantFunction(nat,nat):nat\<rightarrow>Pow(nat)" using func1_3_L1 by auto
  have B:"ConstantFunction(nat,f):(\<Prod>i\<in>nat. ConstantFunction(nat, nat) ` i \<rightarrow> ConstantFunction(nat, nat) ` i)"
    unfolding Pi_def function_def Sigma_def apply auto unfolding ConstantFunction_def apply auto
      prefer 2 using assms(1) func1_3_L2[of _ nat nat] unfolding Pi_def ConstantFunction_def apply auto
    unfolding function_def by blast
  have "{\<langle>i,nat\<rangle>. i\<in>nat} = ConstantFunction(nat,nat)" unfolding ConstantFunction_def by auto
  then have "internal_set(ConstantFunction(nat,nat), \<lambda>_. nat) = *\<nat>" using internal_total_set[of "\<lambda>_. nat"] by auto
  then have C:"hyper_rel(\<lambda>_. nat) `` {x} \<in>
    internal_set(ConstantFunction(nat, nat), \<lambda>_. nat)" unfolding hyper_set_def quotient_def
    using assms(2) by auto
  from e have "\<^sup>*f\<^sub>*`([x]) =hyper_rel(\<lambda>_. nat) ``
    {{\<langle>i, if x ` i \<in> ConstantFunction(nat, nat) ` i
          then (ConstantFunction(nat, f) ` i) ` (x ` i)
          else x ` i\<rangle> .
      i \<in> nat}}"
    using internal_fun_apply_2[of "ConstantFunction(nat,nat)" "\<lambda>_. nat" "ConstantFunction(nat,nat)" "ConstantFunction(nat,f)"
        x, OF A A B C] by auto
  then have "\<^sup>*f\<^sub>*`([x]) =hyper_rel(\<lambda>_. nat) ``
    {{\<langle>i, if x ` i \<in> nat then (ConstantFunction(nat, f) ` i) ` (x ` i) else x ` i\<rangle>. i \<in> nat}}"
    using func1_3_L2[of _ nat nat] by auto
  then have "\<^sup>*f\<^sub>*`([x]) =hyper_rel(\<lambda>_. nat) ``
    {{\<langle>i, (ConstantFunction(nat, f) ` i) ` (x ` i)\<rangle>. i \<in> nat}}"
    using apply_type[OF assms(2)] by auto
  then have "\<^sup>*f\<^sub>*`([x]) =hyper_rel(\<lambda>_. nat) ``
    {{\<langle>i, f ` (x ` i)\<rangle>. i \<in> nat}}"
    using func1_3_L2[of _ nat f] by auto
  then have "\<^sup>*f\<^sub>*`([x]) =hyper_rel(\<lambda>_. nat) ``
    {{\<langle>i, (f O x) ` i\<rangle>. i \<in> nat}}" using comp_fun_apply[OF assms(2)] by auto
  then have "\<^sup>*f\<^sub>*`([x]) =hyper_rel(\<lambda>_. nat) `` {f O x}"
    using fun_is_set_of_pairs[OF comp_fun[OF assms(2,1)]] by auto
  then show ?thesis unfolding seq_class_def[OF comp_fun[OF assms(2,1)]].
qed

text\<open>Every subset of an internal set of the natural numbers is internal\<close>

lemma standard_internal_set:
  assumes "isInternal(A,\<lambda>_. nat)" "A \<subseteq> ({\<langle>x,*x\<rangle>. x\<in>nat}``nat)" "X \<subseteq> A"
  shows "isInternal(X,\<lambda>_. nat)"
proof-
  let ?X="{\<langle>x,*x\<rangle>. x\<in>nat}-``X"
  let ?SX="ConstantFunction(nat,?X)"
  have X:"?X \<in>Pow(nat)" using vimage_iff by auto
  have s:"?SX:nat\<rightarrow>Pow(nat)" using func1_3_L1[OF X] by auto
  {
    fix t assume t:"t\<in>X"
    with assms(2,3) have "t\<in>({\<langle>x,*x\<rangle>. x\<in>nat}``nat)" by auto
    then obtain q where q:"q\<in>nat" "t=*q" using image_iff by auto
    from t q have "q\<in>?X" using vimage_iff[of q "{\<langle>x,*x\<rangle>. x\<in>nat}" X] by auto
    then have "{n\<in>nat. q\<in>?X}=nat" by auto
    then have "{n\<in>nat. q\<in>?X}:\<FF>" using ultraFilter unfolding IsUltrafilter_def IsFilter_def by auto
    then have "{n\<in>nat. q\<in>?SX`n}:\<FF>" using func1_3_L2 by auto
    then have "{n\<in>nat. ConstantFunction(nat,q)`n\<in>?SX`n}:\<FF>" using func1_3_L2 by auto
    then have "hyper_rel(\<lambda>_. nat)``{ConstantFunction(nat,q)}:internal_set(?SX,\<lambda>_. nat)"
      unfolding internal_set_def[OF s] using func1_3_L1[OF q(1), of nat] by auto
    then have "(*q):internal_set(?SX,\<lambda>_. nat)" unfolding incl_def[OF q(1)]
      seq_class_def[OF func1_3_L1[OF q(1), of nat]].
    with q(2) have "t:internal_set(?SX,\<lambda>_. nat)" by auto
  }
  with assms(3) have "X\<subseteq> A \<inter>internal_set(?SX,\<lambda>_. nat)" by auto moreover
  {
    fix t assume "t\<in>A \<inter>internal_set(?SX,\<lambda>_. nat)"
    then have t:"t\<in>A" "t\<in>internal_set(?SX,\<lambda>_. nat)" by auto
    from t(2) obtain q where q:"q:nat\<rightarrow>nat" "t=hyper_rel(\<lambda>_. nat)``{q}"
      "{n\<in>nat. q`n:?SX`n}:\<FF>" unfolding internal_set_def[OF s] by auto
    from q(3) have A:"{n\<in>nat. q`n:?X}:\<FF>" using func1_3_L2[of _ nat ?X] by auto
    from t(1) assms(2) have "t \<in>{\<langle>x, *x\<rangle> . x \<in> nat} `` nat " by auto
    then obtain s where s:"s\<in>nat" "t=*s" using image_iff by auto
    from q(2) s(2) have "hyper_rel(\<lambda>_. nat)``{q} = *s" by auto
    then have "\<langle>q,ConstantFunction(nat, s)\<rangle>\<in>hyper_rel(\<lambda>_. nat)"
      unfolding incl_def[OF s(1)] seq_class_def[OF func1_3_L1[OF s(1)]]
      using eq_equiv_class[OF _ hyper_equiv func1_3_L1[OF s(1)]] by auto
    then have "{n\<in>nat. q`n = ConstantFunction(nat, s)`n}:\<FF>" unfolding hyper_rel_def by auto
    then have "{n\<in>nat. q`n = s}:\<FF>" using func1_3_L2[of _ nat s] by auto
    with A have "{n\<in>nat. q`n = s}\<inter>{n\<in>nat. q`n:?X}:\<FF>" using ultraFilter
      unfolding IsFilter_def IsUltrafilter_def by auto
    then have "{n\<in>nat. q`n = s}\<inter>{n\<in>nat. q`n:?X} \<noteq>0" using ultraFilter
      unfolding IsFilter_def IsUltrafilter_def by auto
    then obtain n where "n\<in>{n\<in>nat. q`n = s}\<inter>{n\<in>nat. q`n:?X}" by force
    then have "n\<in>nat" "q`n=s" "q`n\<in>?X" by auto
    then have l:"n\<in>nat" "s:?X" by auto
    from l(2) obtain x where "x\<in>X" "x=*s" using vimage_iff by auto
    with s(2) have "t\<in>X" by auto
  }
  then have "A\<inter>internal_set(?SX,\<lambda>_. nat) \<subseteq> X" by auto
  ultimately have "X= A\<inter>internal_set(?SX,\<lambda>_. nat)" by auto
  moreover have "isInternal(internal_set(?SX,\<lambda>_. nat),\<lambda>_. nat)"
    unfolding isInternal_def using s by auto moreover
  note assms(1) ultimately
  show ?thesis using internal_inter[of A "\<lambda>_. nat" "internal_set(?SX,\<lambda>_. nat)"] by auto
qed

text\<open>Every non empty internal set has a minimum element\<close>

theorem internal_set_has_minimum:
  assumes "isInternal(A,\<lambda>_. nat)" "A\<noteq>0"
  shows "\<exists>t\<in>A. \<forall>q\<in>A. t *\<le> q"
proof-
  from assms obtain S where s:"S:nat\<rightarrow>Pow(nat)" "A=internal_set(S,\<lambda>_. nat)"
    unfolding isInternal_def by auto
  let ?x="{\<langle>i,if S`i\<noteq>0 then \<mu> x. x\<in>S`i else 0\<rangle>. i\<in>nat}"
  have x:"?x\<in>nat\<rightarrow>nat" unfolding Pi_def function_def apply auto
  proof-
    fix i assume i:"i\<in>nat" "S`i\<noteq>0"
    then obtain y where "y\<in>S`i" by auto
    with s(1) i(1) have "y\<in>S`i" "Ord(y)"
      using apply_type[of S nat "\<lambda>_. Pow(nat)" i] nat_into_Ord[of y] by auto
    then have "(\<mu> x. x\<in>S`i)\<in>S`i" using LeastI[of "\<lambda>q. q\<in>S`i"] by auto
    then show "(\<mu> x. x\<in>S`i)\<in>nat" using apply_type[OF s(1) i(1)] by auto
  qed
  {
    assume as:"{n\<in>nat. S`n = 0}:\<FF>"
    {
      fix x assume "x\<in>A"
      with s(2) obtain q where x:"x=[q]" "q:nat\<rightarrow>nat" "{n\<in>nat. q`n\<in>S`n}:\<FF>" unfolding internal_set_def[OF s(1)]
        using seq_class_def by auto
      from as x(3) have "{n\<in>nat. S`n = 0}\<inter>{n\<in>nat. q`n\<in>S`n}:\<FF>" using ultraFilter
        unfolding IsFilter_def IsUltrafilter_def by auto moreover
      have "{n\<in>nat. S`n = 0}\<inter>{n\<in>nat. q`n\<in>S`n} = 0" by auto ultimately
      have "0:\<FF>" by auto
      then have False using ultraFilter unfolding IsFilter_def IsUltrafilter_def by auto
    }
    then have False using assms(2) by auto
  }
  then have "{n\<in>nat. S`n = 0}\<notin>\<FF>" by auto
  then have "nat-{n\<in>nat. S`n = 0}:\<FF>" using ultraFilter
    using set_ultrafilter[of "{n\<in>nat. S`n = 0}" nat \<FF>] by auto moreover
  have "nat-{n\<in>nat. S`n = 0} = {n\<in>nat. S`n \<noteq> 0}" by auto ultimately
  have "{n\<in>nat. S`n \<noteq> 0}:\<FF>" by auto moreover
  {
    fix n assume "n\<in>{n\<in>nat. S`n \<noteq> 0}"
    then have n:"n\<in>nat" "S`n\<noteq>0" by auto
    then obtain y where y:"y\<in>S`n" by auto
    then have "Ord(y)" using apply_type[OF s(1) n(1)] nat_into_Ord by auto
    with y have "(\<mu> x. x:S`n):S`n" using LeastI[of "\<lambda>q. q\<in>S`n" y] by auto
    then have "?x`n\<in>S`n" using n(2) apply_equality[OF _ x] n(1) by auto
    with n(1) have "n\<in>{n\<in>nat. ?x`n\<in>S`n}" by auto
  }
  then have "{n\<in>nat. S`n \<noteq> 0} \<subseteq> {n\<in>nat. ?x`n\<in>S`n}" by auto moreover
  have "{n\<in>nat. ?x`n\<in>S`n} \<in>Pow(nat)" by auto
  ultimately have B:"{n\<in>nat. ?x`n\<in>S`n} :\<FF>" using ultraFilter unfolding IsFilter_def
    IsUltrafilter_def by auto
  with x have Q:"[?x]\<in>internal_set(S,\<lambda>_. nat)" unfolding internal_set_def[OF s(1)]
    seq_class_def[OF x] by auto
  {
    fix m assume m:"m\<in>A"
    with s(2) obtain p where p:"p:nat\<rightarrow>nat" "m=[p]" "{n\<in>nat. p`n:S`n}:\<FF>"
      unfolding internal_set_def[OF s(1)] using seq_class_def by auto
    from p(3) B have "{n\<in>nat. ?x`n\<in>S`n}\<inter>{n\<in>nat. p`n:S`n}:\<FF>"
      using ultraFilter unfolding IsFilter_def IsUltrafilter_def by auto moreover
    {
      fix h assume h:"h\<in>{n\<in>nat. ?x`n\<in>S`n}\<inter>{n\<in>nat. p`n:S`n}"
      then have h:"h\<in>nat" "?x`h\<in>S`h" "p`h\<in>S`h" by auto
      from h(2) have "S`h\<noteq>0" by auto
      then have xx:"?x`h=(\<mu> x. x\<in>S`h)" using apply_equality[OF _ x] h(1) by auto
      from h(3) have "p`h\<in>nat" using apply_type[OF s(1)] h(1) by auto
      then have "Ord(p`h)" using nat_into_Ord by auto
      with h(3) xx have "?x`h\<le>p`h" using Least_le[of "\<lambda>q. q\<in>S`h" "p`h"] by auto
      with h(1) have "h\<in>{h\<in>nat. ?x`h\<le>p`h}" by auto
    }
    then have "{n\<in>nat. ?x`n\<in>S`n}\<inter>{n\<in>nat. p`n:S`n} \<subseteq> {h\<in>nat. ?x`h\<le>p`h}" by auto
    moreover have "{h\<in>nat. ?x`h\<le>p`h}\<in>Pow(nat)" by auto ultimately
    have "{h\<in>nat. ?x`h\<le>p`h}:\<FF>" using ultraFilter unfolding IsFilter_def IsUltrafilter_def by auto
    then have "[?x]*\<le>[p]" using less_than_seq[OF x p(1)] by auto
    with p(2) have "[?x]*\<le>m" by auto
  }
  then have "\<forall>m\<in>A. [?x]*\<le>m" by auto
  with Q s(2) show ?thesis by auto
qed

text\<open>Every hyper natural that is not zero, is a successor\<close>

theorem succ_hyper_nat:
  assumes "n\<in>*\<nat>" "n\<noteq>*0"
  shows "\<exists>t\<in>*\<nat>. \<^sup>*{\<langle>i,succ(i)\<rangle>. i\<in>nat}\<^sub>*`t=n"
proof-
  let ?S1="ConstantFunction(nat,nat)"
  let ?S2="ConstantFunction(nat,nat)"
  let ?S="ConstantFunction(nat,{\<langle>i,succ(i)\<rangle>. i\<in>nat})"
  have A:"?S1:nat\<rightarrow>Pow(nat)" using func1_3_L1 by auto
  have B:"?S2:nat\<rightarrow>Pow(nat)" using func1_3_L1 by auto
  have C:"?S:(\<Prod>i\<in>nat.?S1 ` i \<rightarrow> ?S2 ` i)"
    unfolding Pi_def function_def Sigma_def apply auto unfolding ConstantFunction_def apply auto
    using apply_equality[of _ nat "nat\<times>{nat}" nat "\<lambda>_. Pow(nat)"] A unfolding ConstantFunction_def
    apply simp using apply_equality[of _ nat "nat\<times>{nat}" nat "\<lambda>_. Pow(nat)"] A unfolding ConstantFunction_def
    apply simp using apply_equality[of _ nat "nat\<times>{nat}" nat "\<lambda>_. Pow(nat)"] A unfolding ConstantFunction_def
    by auto
  from assms(1) obtain q where q:"n=[q]" "q:nat\<rightarrow>nat" unfolding hyper_set_def quotient_def
    using seq_class_def by auto
  {
    assume "{n\<in>nat. q`n =0}\<in>\<FF>"
    then have "{n\<in>nat. q`n =ConstantFunction(nat,0)`n}\<in>\<FF>"
      using func1_3_L2 by auto
    then have "\<langle>q,ConstantFunction(nat,0)\<rangle>\<in>hyper_rel(\<lambda>_. nat)"
      unfolding hyper_rel_def using q(2) func1_3_L1[OF nat_0I] by auto
    then have "[q] = *0" using equiv_class_eq[OF hyper_equiv]
      unfolding seq_class_def[OF q(2)] incl_def[OF nat_0I]
      seq_class_def[OF func1_3_L1[OF nat_0I]] by auto
    with q(1) assms(2) have False by auto
  }
  then have "{n\<in>nat. q`n =0}\<notin>\<FF>" by auto
  then have "nat-{n\<in>nat. q`n =0}\<in>\<FF>" using set_ultrafilter[OF _  ultraFilter,
        of "{n\<in>nat. q`n =0}"] by auto
  moreover have "nat-{n\<in>nat. q`n =0} = {n\<in>nat. q`n \<noteq>0}" by auto
  ultimately have L:"{n\<in>nat. q`n \<noteq>0}\<in>\<FF>" by auto
  have suc:"{\<langle>i, succ(i)\<rangle> . i \<in> nat}:nat\<rightarrow>nat"
    unfolding Pi_def function_def by auto
  let ?x="{\<langle>i,pred(q`i)\<rangle>. i\<in>nat}"
  have x:"?x:nat\<rightarrow>nat" unfolding Pi_def function_def apply auto
    using apply_type[OF q(2)] by auto
  then have xN:"[?x]\<in>*\<nat>" unfolding hyper_set_def quotient_def
    seq_class_def[OF x] by auto
  then have "[?x]:internal_set({\<langle>i,nat\<rangle>. i\<in>nat},\<lambda>_. nat)"
    using internal_total_set[of "\<lambda>_. nat"] by auto moreover
  have "{\<langle>i,nat\<rangle>. i\<in>nat} = nat\<times>{nat}" by auto
  ultimately have "[?x]:internal_set(nat\<times>{nat},\<lambda>_. nat)" by auto
  then have "[?x]:internal_set(?S1,\<lambda>_. nat)" unfolding ConstantFunction_def.
  then have D:"hyper_rel(\<lambda>_. nat) `` {?x} \<in> internal_set(ConstantFunction(nat, nat), \<lambda>_. nat)"
    unfolding seq_class_def[OF x] by auto
  from internal_fun_apply_2[OF A B C D]
  have Q:"\<^sup>*{\<langle>i, succ(i)\<rangle> . i \<in> nat}\<^sub>* ` [?x] =
  hyper_rel(\<lambda>_. nat) `` {{\<langle>i, succ(pred(q`i))\<rangle> . i \<in> nat}}" using apply_type[OF x] func1_3_L2[of _ nat nat] 
    func1_3_L2[of _ nat "{\<langle>i, succ(i)\<rangle> . i \<in> nat}"] apply_equality[of _ _ "{\<langle>i, succ(i)\<rangle> . i \<in> nat}", OF _ suc]
    unfolding hyper_fun_def[OF suc] using apply_equality[OF _ x]
    seq_class_def[OF x]  by auto
  {
    fix i assume "i\<in>nat" "q`i=0"
    then have "pred(q`i) = 0" using pred_0 by auto
    then have "succ(pred(q`i)) = 1" by auto
  } 
  then have U:"\<forall>i\<in>nat. q`i= 0 \<longrightarrow> succ(pred(q`i)) = 1" by auto
  {
    fix i assume i:"i\<in>nat" "q`i\<noteq>0"
    then obtain k where k:"k\<in>nat" "q`i = succ(k)" using Nat_ZF_1_L3[OF apply_type[OF q(2)]] i by auto
    then have "pred(q`i) = k" using pred_succ_eq by auto
    then have "succ(pred(q`i)) = q`i" using k(2) by auto
  }
  then have V:"\<forall>i\<in>nat. q`i\<noteq> 0 \<longrightarrow> succ(pred(q`i)) = q`i" by auto
  have f:"{\<langle>i,succ(pred(q`i))\<rangle> . i \<in> nat} = {\<langle>i,1\<rangle>. i\<in>{p\<in>nat. q`p = 0}} \<union> {\<langle>i,q`i\<rangle>. i\<in>{p\<in>nat. q`p \<noteq> 0}}"
  proof
    {
      fix j assume "j\<in>{\<langle>i,succ(pred(q`i))\<rangle> . i \<in> nat}"
      then obtain i where i:"i\<in>nat" "j=\<langle>i,succ(pred(q`i))\<rangle>" by auto
      {
        assume as:"q`i =0"
        with U i have "j=\<langle>i,1\<rangle>" by auto
        then have "j\<in>{\<langle>i,1\<rangle>. i\<in>{p\<in>nat. q`p = 0}} \<union> {\<langle>i,q`i\<rangle>. i\<in>{p\<in>nat. q`p \<noteq> 0}}"
          using i as by auto
      } moreover
      {
        assume as:"q`i \<noteq>0"
        with V i have "j=\<langle>i,q`i\<rangle>" by auto
        then have "j\<in>{\<langle>i,1\<rangle>. i\<in>{p\<in>nat. q`p = 0}} \<union> {\<langle>i,q`i\<rangle>. i\<in>{p\<in>nat. q`p \<noteq> 0}}"
          using i as by auto
      } ultimately have "j\<in>{\<langle>i,1\<rangle>. i\<in>{p\<in>nat. q`p = 0}} \<union> {\<langle>i,q`i\<rangle>. i\<in>{p\<in>nat. q`p \<noteq> 0}}"
        by auto
    }
    then show "{\<langle>i,succ(pred(q`i))\<rangle> . i \<in> nat} \<subseteq> {\<langle>i,1\<rangle>. i\<in>{p\<in>nat. q`p = 0}} \<union> {\<langle>i,q`i\<rangle>. i\<in>{p\<in>nat. q`p \<noteq> 0}}"
      by blast
    {
      fix j assume j:"j\<in>{\<langle>i,1\<rangle>. i\<in>{p\<in>nat. q`p = 0}} \<union> {\<langle>i,q`i\<rangle>. i\<in>{p\<in>nat. q`p \<noteq> 0}}"
      {
        assume "j\<in>{\<langle>i,1\<rangle>. i\<in>{p\<in>nat. q`p = 0}}"
        then obtain i where "i\<in>nat" "q`i = 0" "j=\<langle>i,1\<rangle>" by auto
        with U have "i\<in>nat" "j=\<langle>i,succ(pred(q`i))\<rangle>" by auto
        then have "j\<in>{\<langle>i,succ(pred(q`i))\<rangle> . i \<in> nat}" by auto
      } moreover
      {
        assume "j\<notin>{\<langle>i,1\<rangle>. i\<in>{p\<in>nat. q`p = 0}}"
        with j have "j\<in>{\<langle>i,q`i\<rangle>. i\<in>{p\<in>nat. q`p \<noteq> 0}}" by auto
        then obtain i where "i\<in>nat" "q`i \<noteq> 0" "j=\<langle>i,q`i\<rangle>" by auto
        with V have "i\<in>nat" "j=\<langle>i,succ(pred(q`i))\<rangle>" by auto
        then have "j\<in>{\<langle>i,succ(pred(q`i))\<rangle> . i \<in> nat}" by auto
      } ultimately
      have "j\<in>{\<langle>i,succ(pred(q`i))\<rangle> . i \<in> nat}" by auto
    }
    then show "{\<langle>i,1\<rangle>. i\<in>{p\<in>nat. q`p = 0}} \<union> {\<langle>i,q`i\<rangle>. i\<in>{p\<in>nat. q`p \<noteq> 0}} \<subseteq> {\<langle>i,succ(pred(q`i))\<rangle> . i \<in> nat}"
      by blast
  qed
  have ff:"{\<langle>i,succ(pred(q`i))\<rangle> . i \<in> nat}:nat\<rightarrow>nat" unfolding Pi_def function_def
    apply auto using apply_type[OF q(2)] by auto
  {
    fix i assume "i\<in>{p\<in>nat. q`p \<noteq> 0}"
    then have i:"i\<in>nat" "q`i\<noteq>0" by auto
    with f have "{\<langle>i,succ(pred(q`i))\<rangle> . i \<in> nat}`i = q`i"
      using apply_equality[of i "q`i" _, OF _ ff] by auto
    with i(1) have "i:{p\<in>nat. {\<langle>i,succ(pred(q`i))\<rangle> . i \<in> nat}`p = q`p}" by auto
  }
  then have "{p\<in>nat. q`p \<noteq> 0} \<subseteq> {p\<in>nat. {\<langle>i,succ(pred(q`i))\<rangle> . i \<in> nat}`p = q`p}" by auto
  moreover note L moreover have "{p\<in>nat. {\<langle>i,succ(pred(q`i))\<rangle> . i \<in> nat}`p = q`p}:Pow(nat)" by auto
  ultimately have "{p\<in>nat. {\<langle>i,succ(pred(q`i))\<rangle> . i \<in> nat}`p = q`p}:\<FF>" using ultraFilter
    unfolding IsFilter_def IsUltrafilter_def by auto
  then have "\<langle>{\<langle>i,succ(pred(q`i))\<rangle> . i \<in> nat},q\<rangle>\<in>hyper_rel(\<lambda>_. nat)"
    unfolding hyper_rel_def using ff q(2) by auto
  then have "hyper_rel(\<lambda>_. nat)``{{\<langle>i,succ(pred(q`i))\<rangle> . i \<in> nat}} = hyper_rel(\<lambda>_. nat)``{q}"
    using equiv_class_eq[OF hyper_equiv] by auto
  with Q have "\<^sup>*{\<langle>i, succ(i)\<rangle> . i \<in> nat}\<^sub>* ` [{\<langle>i, Arith.pred(q ` i)\<rangle> . i \<in> nat}] = [q]"
    using seq_class_def[OF q(2)] by auto
  with q(1) have "\<^sup>*{\<langle>i, succ(i)\<rangle> . i \<in> nat}\<^sub>* ` [{\<langle>i, Arith.pred(q ` i)\<rangle> . i \<in> nat}] = n" by auto
  with xN show ?thesis by auto
qed

text\<open>The natural numbers is not an internal set\<close>

corollary nat_not_internal:
  shows "\<not>isInternal({\<langle>x,*x\<rangle>. x\<in>nat}``nat,\<lambda>_. nat)"
proof
  assume "isInternal({\<langle>x,*x\<rangle>. x\<in>nat}``nat,\<lambda>_. nat)"
  then have A:"isInternal(*\<nat>-({\<langle>x,*x\<rangle>. x\<in>nat}``nat),\<lambda>_. nat)"
    using complement_internal by auto
  {
    assume z:"*\<nat>-({\<langle>x,*x\<rangle>. x\<in>nat}``nat) = 0"
    then have "\<omega> \<in> {\<langle>x,*x\<rangle>. x\<in>nat}``nat" using omega_not_nat(2) by auto
    then obtain n where "\<omega> = *n" "n\<in>nat" using image_iff by auto
    then have False using omega_not_nat(1) by auto
  }
  then have B:"*\<nat>-({\<langle>x,*x\<rangle>. x\<in>nat}``nat) \<noteq> 0" by auto
  have C:"\<exists>t\<in>*\<nat>-({\<langle>x,*x\<rangle>. x\<in>nat}``nat). \<forall>q\<in>*\<nat>-({\<langle>x,*x\<rangle>. x\<in>nat}``nat). t *\<le> q"
    using internal_set_has_minimum[OF A B] by auto
  then obtain t where t:"t\<in>*\<nat>-({\<langle>x,*x\<rangle>. x\<in>nat}``nat)" "\<forall>q\<in>*\<nat>-({\<langle>x,*x\<rangle>. x\<in>nat}``nat). t *\<le> q"
    by auto
  from t(1) have A:"t\<in>*\<nat>" by auto
  {
    assume "t=*0"
    then have "t\<in>{\<langle>x,*x\<rangle>. x\<in>nat}``nat" using image_iff by auto
    with t(1) have False by auto
  }
  then have B:"t \<noteq> *0" by auto
  then obtain q where q:"q\<in>*\<nat>" "\<^sup>*{\<langle>i, succ(i)\<rangle> . i \<in> nat}\<^sub>* ` q = t" 
    using succ_hyper_nat[OF A B] by auto
  have suc:"{\<langle>i, succ(i)\<rangle> . i \<in> nat}:nat\<rightarrow>nat"
    unfolding Pi_def function_def by auto
  from q(1) obtain qx where qq:"q=[qx]" "qx:nat\<rightarrow>nat" unfolding hyper_set_def quotient_def
    using seq_class_def by auto
  from qq(1) have "\<^sup>*{\<langle>i, succ(i)\<rangle> . i \<in> nat}\<^sub>* ` q = [{\<langle>i, succ(i)\<rangle> . i \<in> nat} O qx]"
    using hyper_fun_on_nat_2[OF suc qq(2)] by auto
  then have "t=[{\<langle>i, succ(i)\<rangle> . i \<in> nat} O qx]" using q(2) by auto
  moreover from A obtain tx where tx:"t=[tx]" "tx:nat\<rightarrow>nat" unfolding hyper_set_def quotient_def
    using seq_class_def by auto
  note tx(1) ultimately have "\<langle>tx,{\<langle>i, succ(i)\<rangle> . i \<in> nat} O qx\<rangle>\<in>hyper_rel(\<lambda>_. nat)"
    using eq_equiv_class[OF _ hyper_equiv comp_fun[OF qq(2) suc]] 
    unfolding seq_class_def[OF tx(2)] seq_class_def[OF comp_fun[OF qq(2) suc]] by auto
  then have "{i:nat. tx`i = ({\<langle>i, succ(i)\<rangle> . i \<in> nat} O qx)`i}:\<FF>" unfolding hyper_rel_def by auto
  then have "{i:nat. tx`i = {\<langle>i, succ(i)\<rangle> . i \<in> nat}` (qx`i)}:\<FF>" using comp_fun_apply[OF qq(2)]
    by auto
  then have B:"{i:nat. tx`i = succ (qx`i)}:\<FF>" using apply_equality[OF _ suc]
    apply_type[OF qq(2)] by auto moreover
  have "{i:nat. qx`i \<le> tx`i}:Pow(nat)" by auto moreover
  {
    fix i assume "i\<in>{i:nat. tx`i = succ (qx`i)}"
    then have i:"i\<in>nat" "tx`i = succ(qx`i)" by auto
    have "qx ` i \<le> qx ` i" "Ord(qx ` i)"
      using nat_into_Ord[OF apply_type[OF qq(2) i(1)]] le_refl[OF nat_into_Ord[OF apply_type[OF qq(2) i(1)]]]
      by auto
    then have "(qx ` i \<le> qx ` i \<or> (qx ` i = succ(qx ` i))) \<and> Ord(qx ` i)" by blast
    then have "qx`i \<le> succ(qx`i)" using le_succ_iff by auto
    then have "qx`i \<le> tx`i" by (simp only: subst[OF i(2)[THEN sym], of "\<lambda>z. qx`i \<le> z"])
    with i(1) have "i\<in>{i:nat. qx`i \<le> tx`i}" by auto
  }
  then have "{i:nat. tx`i = succ (qx`i)} \<subseteq> {i:nat. qx`i \<le> tx`i}" by blast
  ultimately have A:"{i:nat. qx`i \<le> tx`i}:\<FF>" using ultraFilter
    unfolding IsFilter_def IsUltrafilter_def by auto
  then have "[qx] *\<le> [tx]" using less_than_seq[OF qq(2) tx(2)] by auto
  then have "q *\<le> t" using qq(1) tx(1) by auto
  {
    assume "q\<in>({\<langle>x,*x\<rangle>. x\<in>nat}``nat)"
    then obtain u where u:"q=*u" "u\<in>nat" using image_iff by auto
    then have "\<^sup>*{\<langle>i, succ(i)\<rangle> . i \<in> nat}\<^sub>* ` q = *({\<langle>i, succ(i)\<rangle> . i \<in> nat}`u)"
      using hyper_fun_on_nat[OF suc] by auto
    then have "\<^sup>*{\<langle>i, succ(i)\<rangle> . i \<in> nat}\<^sub>* ` q = *(succ(u))"
      using apply_equality[OF _ suc] u(2) by auto
    then have "t = *(succ(u))" using q(2) by auto
    then have "\<langle>succ(u),t\<rangle>\<in>{\<langle>x,*x\<rangle>. x\<in>nat}" using u(2) by auto
    then have "t: {\<langle>x,*x\<rangle>. x\<in>nat}``nat" using image_iff by auto
    with t(1) have False by auto
  }
  with q(1) have "q\<in>*\<nat>-({\<langle>x,*x\<rangle>. x\<in>nat}``nat)" by auto
  with t(2) have "t *\<le> q" by auto
  then have "{i:nat. tx`i \<le> qx`i}:\<FF>" using less_than_seq[OF tx(2) qq(2)]
    using tx(1) qq(1) by auto
  with B have "{i:nat. tx`i \<le> qx`i}\<inter>{i:nat.  tx ` i = succ(qx ` i)}:\<FF>"
    using ultraFilter unfolding IsFilter_def IsUltrafilter_def by auto moreover
  {
    fix i assume "i\<in>{i:nat. tx`i \<le> qx`i}\<inter>{i:nat.  tx ` i = succ(qx ` i)}"
    then have "i:nat" "tx`i \<le> qx`i" "tx ` i = succ(qx ` i)" by auto
    then have "succ(qx`i) \<le> qx`i" by auto
    then have False by auto
  }
  then have "{i:nat. tx`i \<le> qx`i}\<inter>{i:nat.  tx ` i = succ(qx ` i)} = 0" by auto
  ultimately show False using ultraFilter unfolding IsFilter_def IsUltrafilter_def by auto
qed

definition isHyperFinite where
"H\<in>Pow(*\<nat>) \<Longrightarrow> isHyperFinite(H) \<equiv> \<exists>S\<in>nat\<rightarrow>FinPow(nat). H = internal_set(S,\<lambda>_. nat)"

lemma hyperfinite_internal:
  assumes "H\<in>Pow(*\<nat>)" "isHyperFinite(H)"
  shows "isInternal(H,\<lambda>_. nat)"
proof-
  from assms(2) obtain S where S:"S:nat\<rightarrow>FinPow(nat)" "H=internal_set(S,\<lambda>_. nat)"
    unfolding isHyperFinite_def[OF assms(1)] isInternal_def by auto
  from S(1) have "S:nat\<rightarrow>Pow(nat)" unfolding Pi_def FinPow_def by auto
  with S(2) show ?thesis unfolding isInternal_def by auto
qed

text\<open>The family defining an internal set only need to be finite for a
set of indices in the ultrafilter for it to be hyperfinite.\<close>

lemma internal_finite_ultrafilter_imp_hyperfinite:
  assumes "S\<in>nat \<rightarrow> Pow(nat)" "{i\<in>nat. Finite(S`i)}:\<FF>"
  shows "isHyperFinite(internal_set(S,\<lambda>_. nat))"
proof-
  have A:"internal_set(S,%_. nat) \<in>Pow(*\<nat>)" using internal_subset[OF assms(1)] by auto
  let ?S ="{\<langle>i,if Finite(S`i) then S`i else 0\<rangle>. i\<in>nat}"
  have S:"?S\<in>nat \<rightarrow> Pow(nat)" "?S\<in>nat \<rightarrow> FinPow(nat)" using apply_type[OF assms(1)] unfolding Pi_def function_def FinPow_def
    apply auto
  proof-
    fix i xa assume as:"i\<in>nat"  "xa \<in> (if Finite(S ` i) then S ` i else 0)"
    then have "S`i\<in>Pow(nat)" using apply_type[OF assms(1)] by auto
    then have "(if Finite(S`i) then S`i else 0)\<in>Pow(nat)" using if_type by auto
    with as(2) show "xa\<in>nat" by auto
    then show "xa\<in>nat".
  qed
  {
    fix i assume "i\<in>{i\<in>nat. Finite(S`i)}"
    then have i:"i:nat" "Finite(S`i)" by auto
    then have "?S`i = S`i" using apply_equality[OF _ S(1)] by auto
    with i(1) have "i\<in>{i\<in>nat. ?S`i = S`i}" by auto
  }
  then have "{i\<in>nat. Finite(S`i)} \<subseteq> {i\<in>nat. S`i = ?S`i}" by auto
  moreover note assms(2) moreover have "{i\<in>nat. S`i = ?S`i}:Pow(nat)" by auto
  ultimately have " {i\<in>nat. S`i = ?S`i}:\<FF>" using ultraFilter unfolding IsFilter_def IsUltrafilter_def
    by auto
  then have "internal_set(S,\<lambda>_. nat) = internal_set(?S,%_. nat)" using internal_eq[OF assms(1) S(1)] by auto moreover
  note S(2)
  ultimately show ?thesis unfolding isHyperFinite_def[OF A] by auto
qed


text\<open>For every hyper finite set there is an internal bijection of it
with the hyper naturals up to a number. We make a note that the choice
is valid since there is an identifiable bijection that is the only
order isomorphism between any two bijective linearly ordered finite sets.

This is possible because the order is out of the choice function since
both are subsets of the natural numbers.\<close>
    
lemma hyperfinite_internally_bijective:
  assumes "H\<in>Pow(*\<nat>)" "isHyperFinite(H)"
  shows "\<exists>N\<in>*\<nat>. \<exists>S1\<in>nat\<rightarrow>Pow(nat). \<exists>S2\<in>nat\<rightarrow>Pow(nat). \<exists>S\<in>Pi(nat, \<lambda>i. S1`i \<rightarrow> S2`i). internal_fun(S,\<lambda>_.nat):bij(H,{i\<in>*\<nat>. i *< N})"
proof-
  from assms(2) obtain S where S:"S:nat\<rightarrow>FinPow(nat)" "H=internal_set(S,\<lambda>_. nat)"
    unfolding isHyperFinite_def[OF assms(1)] by auto
  let ?N="{\<langle>i,|S`i|\<rangle>. i\<in>nat}"
  have n_fun:"?N:nat\<rightarrow>nat" unfolding Pi_def function_def using apply_type[OF S(1)] unfolding FinPow_def
    using Finite_cardinal_in_nat by auto
  then have N:"[?N]:*\<nat>" unfolding hyper_set_def quotient_def using seq_class_def by auto
  {
    fix g assume g:"g\<in>Pi(nat,\<lambda>i. bij(S`i,|S`i|))"
    let ?f="internal_fun(g,\<lambda>_. nat)"
    have const:"{\<langle>i, nat\<rangle> . i \<in> nat} = ConstantFunction(nat,nat)" 
      unfolding ConstantFunction_def by auto
    have S2:"S:nat \<rightarrow> Pow(nat)" using S(1) unfolding FinPow_def Pi_def by auto moreover
    have "g\<in>Pi(nat,\<lambda>i. S`i \<rightarrow> nat)"
      unfolding Pi_def function_def apply auto
        prefer 3 using g unfolding Pi_def function_def apply blast
       prefer 2 using g unfolding Pi_def apply blast
    proof-
      fix x assume "x\<in>g"
      with g have "x\<in>(\<Sum>i\<in>nat. bij(S ` i, |S ` i|))" unfolding Pi_def by auto
      then obtain i f where x:"x=\<langle>i,f\<rangle>" "i\<in>nat" "f\<in>bij(S ` i, |S ` i|)" by auto
      have f:"f\<in>{f \<in> Pow(S ` i \<times> |S`i|) .
              S ` i \<subseteq> domain(f) \<and> (\<forall>x y. \<langle>x, y\<rangle> \<in> f \<longrightarrow> (\<forall>y'. \<langle>x, y'\<rangle> \<in> f \<longrightarrow> y = y'))}"
        using bij_is_fun[OF x(3)] unfolding Pi_def function_def .
      have "|S`i|\<in>nat" using apply_type[OF S(1) x(2)] unfolding FinPow_def
        using Finite_cardinal_in_nat by auto
      then have "|S`i| \<subseteq> nat" using OrdmemD[OF _ Ord_nat] by auto moreover
      from f have "f\<in> Pow(S ` i \<times> |S`i|)"  by auto
      ultimately have "f:  Pow(S ` i \<times> nat)" by auto
      with f have "f\<in>{f \<in> Pow(S ` i \<times> nat) .
              S ` i \<subseteq> domain(f) \<and> (\<forall>x y. \<langle>x, y\<rangle> \<in> f \<longrightarrow> (\<forall>y'. \<langle>x, y'\<rangle> \<in> f \<longrightarrow> y = y'))}" by blast
      with x(1,2) show "x \<in>
         (\<Sum>i\<in>nat.
             {f \<in> Pow(S ` i \<times> nat) .
              S ` i \<subseteq> domain(f) \<and> (\<forall>x y. \<langle>x, y\<rangle> \<in> f \<longrightarrow> (\<forall>y'. \<langle>x, y'\<rangle> \<in> f \<longrightarrow> y = y'))})" by blast
    qed
    then have g2:"g \<in> (\<Prod>i\<in>nat. S ` i \<rightarrow> ConstantFunction(nat,nat)`i)" using
      func1_3_L2[of _ nat nat] unfolding Pi_def by force
    have fun:"?f:H\<rightarrow>*\<nat>" using internal_fun_is_fun[OF S2 func1_3_L1 g2]
      internal_total_set[of "\<lambda>_. nat"] const S(2) by auto
    {
      fix t assume t:"t\<in>range(?f)"
      then obtain q where "\<langle>q,t\<rangle>\<in>?f" using rangeE by auto
      with fun have f:"q\<in>H" "t\<in>*\<nat>" "\<langle>q,t\<rangle>\<in>?f" unfolding Pi_def by auto
      from f(1,3) have fqt:"?f`q=t" using apply_equality[OF _ fun] by auto
      from f(1) S(2) obtain qx where qx:"qx:nat\<rightarrow>nat" "{i\<in>nat. qx`i\<in>S`i}\<in>\<FF>" "q=[qx]"
        unfolding internal_set_def[OF S2] using seq_class_def by auto
      from f(2) obtain tx where tx:"tx:nat\<rightarrow>nat" "t=[tx]" using seq_class_def
        unfolding hyper_set_def quotient_def by auto
      from fqt qx(3) have "t = hyper_rel(\<lambda>_. nat) `` {{\<langle>i, if qx ` i \<in> S ` i then g ` i ` (qx ` i) else qx ` i\<rangle> . i \<in> nat}}" using internal_fun_apply_2[OF S2 func1_3_L1 g2, of qx]
        f(1) S(2) unfolding seq_class_def[OF qx(1)] by auto
      with tx(2) have "[tx] = hyper_rel(\<lambda>_. nat) `` {{\<langle>i, if qx ` i \<in> S ` i then g ` i ` (qx ` i) else qx ` i\<rangle> . i \<in> nat}}" by auto
      then have "hyper_rel(\<lambda>_. nat) `` {{\<langle>i, if qx ` i \<in> S ` i then g ` i ` (qx ` i) else qx ` i\<rangle> . i \<in> nat}} = [tx]" by auto
      then have "\<langle>{\<langle>i, if qx ` i \<in> S ` i then g ` i ` (qx ` i) else qx ` i\<rangle> . i \<in> nat},tx\<rangle>\<in>hyper_rel(\<lambda>_. nat)"
        using eq_equiv_class[OF _ hyper_equiv, of "\<lambda>_. nat" _ tx] unfolding seq_class_def[OF tx(1)] using tx(1) by auto
      then have "{i\<in>nat. {\<langle>i, if qx ` i \<in> S ` i then g ` i ` (qx ` i) else qx ` i\<rangle> . i \<in> nat}`i = tx`i}:\<FF>"
  and ff:"{\<langle>i, if qx ` i \<in> S ` i then g ` i ` (qx ` i) else qx ` i\<rangle> . i \<in> nat}:nat\<rightarrow>nat"
        unfolding hyper_rel_def by auto
      then have "{i\<in>nat. {\<langle>i, if qx ` i \<in> S ` i then g ` i ` (qx ` i) else qx ` i\<rangle> . i \<in> nat}`i = tx`i}\<inter>{i\<in>nat. qx`i\<in>S`i}\<in>\<FF>"
        using ultraFilter qx(2) unfolding IsFilter_def IsUltrafilter_def by auto moreover
      {
        fix i assume "i\<in>{i\<in>nat. {\<langle>i, if qx ` i \<in> S ` i then g ` i ` (qx ` i) else qx ` i\<rangle> . i \<in> nat}`i = tx`i}\<inter>{i\<in>nat. qx`i\<in>S`i}"
        then have "i\<in>nat" "{\<langle>i, if qx ` i \<in> S ` i then g ` i ` (qx ` i) else qx ` i\<rangle> . i \<in> nat}`i = tx`i" "qx`i\<in>S`i" by auto
        then have i:"i\<in>nat" "(g ` i)  ` (qx ` i)  = tx`i" "qx`i\<in>S`i" using apply_equality[OF _ ff] by auto
        from i(1) have "g`i\<in>bij(S`i,|S`i|)" using g apply_type by auto
        with i(3) have "(g`i)`(qx`i)\<in>|S`i|" using apply_type[OF bij_is_fun] by auto
        with i(2) have "tx`i\<in>|S`i|" by auto
        then have "tx`i < |S`i|" unfolding lt_def by auto
        then have "tx`i < ?N`i" using apply_equality[of i "|S`i|" ?N] n_fun i(1) by auto
        then have "i\<in>{i\<in>nat. tx`i < ?N`i }" using i(1) by auto
      }
      then have "{i\<in>nat. {\<langle>i, if qx ` i \<in> S ` i then g ` i ` (qx ` i) else qx ` i\<rangle> . i \<in> nat}`i = tx`i}\<inter>{i\<in>nat. qx`i\<in>S`i} \<subseteq> {i\<in>nat. tx`i < ?N`i }" by auto moreover
      have "{i\<in>nat. tx`i < ?N`i }:Pow(nat)" by auto ultimately
      have "{i\<in>nat. tx`i < ?N`i }:\<FF>" using ultraFilter unfolding IsFilter_def IsUltrafilter_def by auto
      then have "[tx] *< [?N]" using less_seq[OF tx(1) n_fun] by auto
      then have "t *<[?N]" using tx(2) by auto
      with f(2) have "t:{p:*\<nat>. p *<[?N]}" by auto
    }
    then have "range(?f) \<subseteq> {p:*\<nat>. p *<[?N]}" by auto
    then have fun:"?f:H\<rightarrow>{p:*\<nat>. p *<[?N]}" using range_of_fun[OF fun] func1_1_L1B by auto
    {
      fix i assume i:"i\<in>nat"
      then have "g`i \<in>S ` i \<rightarrow> ConstantFunction(nat,nat)`i" using g2 apply_type by auto moreover
      from i have "g`i\<in>bij(S`i,|S`i| )" using g apply_type by auto ultimately
      have "g`i\<in>inj(S ` i, ConstantFunction(nat,nat)`i)" unfolding bij_def inj_def by auto
      with i have "i\<in>{i\<in>nat. g`i\<in>inj(S ` i, ConstantFunction(nat,nat)`i)}" by auto
    }
    then have "{i\<in>nat. g`i\<in>inj(S ` i, ConstantFunction(nat,nat)`i)} =nat" by auto
    then have "{i\<in>nat. g`i\<in>inj(S ` i, ConstantFunction(nat,nat)`i)}\<in>\<FF>" using ultraFilter unfolding IsFilter_def
IsUltrafilter_def by auto
    then have "?f\<in>inj(H,*\<nat>)" using internal_fun_inj[OF S2 func1_3_L1 g2] internal_total_set[of "\<lambda>_. nat"] const S(2) by auto
    with fun have "?f:inj(H,{p:*\<nat>. p *<[?N]})" unfolding inj_def by auto
    moreover
    {
      fix p assume "p\<in> {p:*\<nat>. p *<[?N]}"
      then have p:"p:*\<nat>" "p *<[?N]" by auto
      from p(1) obtain px where px:"px:nat\<rightarrow>nat" "[px] =p" unfolding hyper_set_def quotient_def using seq_class_def by auto
      from px(2) p(2) have "{i\<in>nat. px`i < ?N`i}\<in>\<FF>" using less_seq px(1) n_fun by auto
      then have A:"{i\<in>nat. px`i < |S`i|}\<in>\<FF>" using apply_equality n_fun by auto
      let ?m="{\<langle>i,if px`i < |S`i| then converse(g`i)`(px`i) else 0\<rangle>. i\<in>nat}"
      have m:"?m:nat\<rightarrow>nat" unfolding Pi_def function_def apply auto
      proof-
        fix i assume i:"i\<in>nat" "px`i < |S`i|"
        from i(1) have  "g`i\<in>bij(S`i,|S`i| )" using g apply_type by auto
        then have "converse(g`i):|S`i| \<rightarrow> S`i" using bij_converse_bij bij_is_fun by auto
        with i(2) have "converse(g`i)`(px`i)\<in>S`i" using apply_type unfolding lt_def by auto
        then show "converse(g`i)`(px`i)\<in>nat" using apply_type[OF S2] i(1) by auto
      qed
      {
        fix i assume "i\<in>{i\<in>nat. px`i < |S`i|}"
        then have i:"i\<in>nat" "px`i < |S`i|" by auto
        from i(1) have  "g`i\<in>bij(S`i,|S`i| )" using g apply_type by auto
        then have "converse(g`i):|S`i| \<rightarrow> S`i" using bij_converse_bij bij_is_fun by auto
        with i(2) have "converse(g`i)`(px`i)\<in>S`i" using apply_type unfolding lt_def by auto
        with i(2) have "?m`i\<in>S`i" using apply_equality[OF _ m] i(1) by auto
        then have "i\<in>{i\<in>nat. ?m`i\<in>S`i}" using i(1) by auto
      }
      then have B:"{i\<in>nat. px`i < |S`i|} \<subseteq> {i\<in>nat. ?m`i\<in>S`i}" by auto moreover
      from A have "\<And>Q. Q\<in>Pow(nat) \<Longrightarrow> {i\<in>nat. px`i < |S`i|} \<subseteq> Q \<Longrightarrow> Q\<in>\<FF> " using 
ultraFilter unfolding IsFilter_def IsUltrafilter_def by auto moreover
      have "{i\<in>nat. ?m`i\<in>S`i} :Pow(nat)" by auto ultimately
      have C:"{i\<in>nat. ?m`i\<in>S`i}:\<FF>" by auto
      then have fm:"?f`[?m] = hyper_rel(\<lambda>_. nat) ``{{\<langle>i, if {\<langle>i, if px ` i < |S ` i| then converse(g ` i) ` (px ` i) else 0\<rangle> . i \<in> nat} ` i \<in> S ` i
          then g ` i ` ({\<langle>i, if px ` i < |S ` i| then converse(g ` i) ` (px ` i) else 0\<rangle> . i \<in> nat} ` i)
          else {\<langle>i, if px ` i < |S ` i| then converse(g ` i) ` (px ` i) else 0\<rangle> . i \<in> nat} ` i\<rangle> .
      i \<in> nat}}" using internal_fun_apply(1)[OF S2 func1_3_L1 g2 m] seq_class_def[OF m] by auto
      {
        fix i assume "i\<in>{i\<in>nat. px`i < |S`i|}"
        then have i:"i:nat" "px`i < |S`i|" by auto
        from i(1) have bij:"g`i\<in>bij(S`i,|S`i| )" using g apply_type by auto
        then have "converse(g`i):|S`i| \<rightarrow> S`i" using bij_converse_bij bij_is_fun by auto
        with i(2) have "converse(g`i)`(px`i)\<in>S`i" using apply_type unfolding lt_def by auto
        then have "{\<langle>i, if {\<langle>i, if px ` i < |S ` i| then converse(g ` i) ` (px ` i) else 0\<rangle> . i \<in> nat} ` i \<in> S ` i
          then g ` i ` ({\<langle>i, if px ` i < |S ` i| then converse(g ` i) ` (px ` i) else 0\<rangle> . i \<in> nat} ` i)
          else {\<langle>i, if px ` i < |S ` i| then converse(g ` i) ` (px ` i) else 0\<rangle> . i \<in> nat} ` i\<rangle> .
      i \<in> nat}`i = (if (?m ` i \<in> S ` i) then (g ` i) ` (?m ` i) else (?m ` i))" 
          using apply_equality[OF _ internal_fun_apply(2)[OF S2 func1_3_L1 g2 m C]] i(1) by auto
        then have "{\<langle>i, if {\<langle>i, if px ` i < |S ` i| then converse(g ` i) ` (px ` i) else 0\<rangle> . i \<in> nat} ` i \<in> S ` i
          then g ` i ` ({\<langle>i, if px ` i < |S ` i| then converse(g ` i) ` (px ` i) else 0\<rangle> . i \<in> nat} ` i)
          else {\<langle>i, if px ` i < |S ` i| then converse(g ` i) ` (px ` i) else 0\<rangle> . i \<in> nat} ` i\<rangle> .
      i \<in> nat}`i = (g ` i) ` (?m ` i)"  using i B by auto
        then have "{\<langle>i, if {\<langle>i, if px ` i < |S ` i| then converse(g ` i) ` (px ` i) else 0\<rangle> . i \<in> nat} ` i \<in> S ` i
          then g ` i ` ({\<langle>i, if px ` i < |S ` i| then converse(g ` i) ` (px ` i) else 0\<rangle> . i \<in> nat} ` i)
          else {\<langle>i, if px ` i < |S ` i| then converse(g ` i) ` (px ` i) else 0\<rangle> . i \<in> nat} ` i\<rangle> .
      i \<in> nat}`i = (g ` i) ` (converse(g ` i) ` (px ` i))" using i apply_equality[OF _ m] by auto
        then have "{\<langle>i, if {\<langle>i, if px ` i < |S ` i| then converse(g ` i) ` (px ` i) else 0\<rangle> . i \<in> nat} ` i \<in> S ` i
          then g ` i ` ({\<langle>i, if px ` i < |S ` i| then converse(g ` i) ` (px ` i) else 0\<rangle> . i \<in> nat} ` i)
          else {\<langle>i, if px ` i < |S ` i| then converse(g ` i) ` (px ` i) else 0\<rangle> . i \<in> nat} ` i\<rangle> .
      i \<in> nat}`i =px ` i" using right_inverse_bij[OF bij] using i(2) unfolding lt_def by auto
        with i(1) have "i\<in>{i\<in>nat. {\<langle>i, if {\<langle>i, if px ` i < |S ` i| then converse(g ` i) ` (px ` i) else 0\<rangle> . i \<in> nat} ` i \<in> S ` i
          then g ` i ` ({\<langle>i, if px ` i < |S ` i| then converse(g ` i) ` (px ` i) else 0\<rangle> . i \<in> nat} ` i)
          else {\<langle>i, if px ` i < |S ` i| then converse(g ` i) ` (px ` i) else 0\<rangle> . i \<in> nat} ` i\<rangle> .
      i \<in> nat}`i =px ` i}" by auto
      }
      then have "{i\<in>nat. px`i < |S`i| } \<subseteq> {i\<in>nat. {\<langle>i, if {\<langle>i, if px ` i < |S ` i| then converse(g ` i) ` (px ` i) else 0\<rangle> . i \<in> nat} ` i \<in> S ` i
          then g ` i ` ({\<langle>i, if px ` i < |S ` i| then converse(g ` i) ` (px ` i) else 0\<rangle> . i \<in> nat} ` i)
          else {\<langle>i, if px ` i < |S ` i| then converse(g ` i) ` (px ` i) else 0\<rangle> . i \<in> nat} ` i\<rangle> .
      i \<in> nat}`i =px ` i}" by auto
      moreover have "{i\<in>nat. {\<langle>i, if {\<langle>i, if px ` i < |S ` i| then converse(g ` i) ` (px ` i) else 0\<rangle> . i \<in> nat} ` i \<in> S ` i
          then g ` i ` ({\<langle>i, if px ` i < |S ` i| then converse(g ` i) ` (px ` i) else 0\<rangle> . i \<in> nat} ` i)
          else {\<langle>i, if px ` i < |S ` i| then converse(g ` i) ` (px ` i) else 0\<rangle> . i \<in> nat} ` i\<rangle> .
      i \<in> nat}`i =px ` i}\<in>Pow(nat)" by auto moreover note A
      ultimately have "{i\<in>nat. {\<langle>i, if {\<langle>i, if px ` i < |S ` i| then converse(g ` i) ` (px ` i) else 0\<rangle> . i \<in> nat} ` i \<in> S ` i
          then g ` i ` ({\<langle>i, if px ` i < |S ` i| then converse(g ` i) ` (px ` i) else 0\<rangle> . i \<in> nat} ` i)
          else {\<langle>i, if px ` i < |S ` i| then converse(g ` i) ` (px ` i) else 0\<rangle> . i \<in> nat} ` i\<rangle> .
      i \<in> nat}`i =px ` i}\<in>\<FF>" using ultraFilter unfolding IsFilter_def IsUltrafilter_def by auto
      with px(1) have "\<langle>{\<langle>i, if {\<langle>i, if px ` i < |S ` i| then converse(g ` i) ` (px ` i) else 0\<rangle> . i \<in> nat} ` i \<in> S ` i
          then g ` i ` ({\<langle>i, if px ` i < |S ` i| then converse(g ` i) ` (px ` i) else 0\<rangle> . i \<in> nat} ` i)
          else {\<langle>i, if px ` i < |S ` i| then converse(g ` i) ` (px ` i) else 0\<rangle> . i \<in> nat} ` i\<rangle> .
      i \<in> nat},px\<rangle>\<in>hyper_rel(\<lambda>_. nat)" using internal_fun_apply(2)[OF S2 func1_3_L1 g2 m C] unfolding hyper_rel_def by auto
      then have "hyper_rel(\<lambda>_. nat)``{{\<langle>i, if {\<langle>i, if px ` i < |S ` i| then converse(g ` i) ` (px ` i) else 0\<rangle> . i \<in> nat} ` i \<in> S ` i
          then g ` i ` ({\<langle>i, if px ` i < |S ` i| then converse(g ` i) ` (px ` i) else 0\<rangle> . i \<in> nat} ` i)
          else {\<langle>i, if px ` i < |S ` i| then converse(g ` i) ` (px ` i) else 0\<rangle> . i \<in> nat} ` i\<rangle> .
      i \<in> nat}} = p" using equiv_class_eq[OF hyper_equiv] using px(2) seq_class_def[OF px(1)] by auto
      with fm have "?f`[?m] = p" by auto moreover
      from C m have "?m\<in>{f:nat\<rightarrow>nat. {i\<in>nat. f`i:S`i}:\<FF>}" by auto
      then have "[?m]\<in>internal_set(S,\<lambda>_. nat)" unfolding internal_set_def[OF S2] seq_class_def[OF m] by auto
      ultimately have "\<exists>m\<in>H. ?f`m = p" using S(2) by auto
    }
    then have "\<forall>p\<in>{q\<in>*\<nat>. q *< [?N]}. \<exists>m\<in>H. ?f`m = p" by auto
    then have "?f:surj(H,{p\<in>*\<nat>. p *< [?N]})" unfolding surj_def using fun by blast
    ultimately have "?f:bij(H,{p\<in>*\<nat>. p *< [?N]})" unfolding bij_def by auto
    then have "\<exists>N\<in>*\<nat>. \<exists>S1\<in>nat\<rightarrow>Pow(nat). \<exists>S2\<in>nat\<rightarrow>Pow(nat). \<exists>S\<in>Pi(nat, \<lambda>i. S1`i \<rightarrow> S2`i). internal_fun(S, \<lambda>_. nat) \<in> bij(H, {i \<in> *\<nat> . i *< N})" using N S2 g2
      func1_3_L1[of nat "Pow(nat)"] by auto
  }
  then have R:"(\<Prod>i\<in>nat. bij(S ` i, |S ` i|))\<noteq>0 \<Longrightarrow> \<exists>N\<in>*\<nat>. \<exists>S1\<in>nat\<rightarrow>Pow(nat). \<exists>S2\<in>nat\<rightarrow>Pow(nat). \<exists>S\<in>Pi(nat, \<lambda>i. S1`i \<rightarrow> S2`i). internal_fun(S, \<lambda>_. nat) \<in> bij(H, {i \<in> *\<nat> . i *< N})" by blast
  let ?g="{\<langle>i,THE f. f \<in> ord_iso(S`i,Le,|S`i|,Le)\<rangle>. i\<in>nat}"
  {
    fix i assume i:"i:nat"
    have f:"Finite(S`i)" using apply_type[OF S(1)] i unfolding FinPow_def by auto
    then have "|S`i| :nat" using Finite_cardinal_in_nat by auto
    then have "|S`i| \<subseteq> nat" "Finite( |S`i|)" using Ord_nat nat_into_Finite unfolding Ord_def Transset_def by auto 
    then have A:"|S`i| :FinPow(nat)" unfolding FinPow_def by auto
    from f have B:"|S`i| \<approx> S`i" using well_ord_cardinal_eqpoll Finite_imp_well_ord[OF f] by auto
    from fin_ord_iso_ex_uniq[OF NatOrder_ZF_1_L2(4) NatOrder_ZF_1_L2(4) apply_type[OF S(1) i] A B] have "\<exists>!f. f\<in>ord_iso(S`i,Le,|S`i|,Le)" by auto
    then have "(THE f. f \<in> ord_iso(S`i,Le,|S`i|,Le)) \<in> ord_iso(S`i,Le,|S`i|,Le)" using theI[of "\<lambda>f. f\<in> ord_iso(S`i,Le,|S`i|,Le)"] by auto
    then have "(THE f. f \<in> ord_iso(S`i,Le,|S`i|,Le)) \<in> bij(S`i,| S`i| )" unfolding ord_iso_def by blast
  }
  then have "?g\<in>Pi(nat, \<lambda>i. bij(S ` i, |S ` i|))" unfolding Pi_def function_def by auto
  with R show ?thesis by auto
qed

lemma hyperfinite_internally_bijective:
  assumes "H\<in>Pow(*\<nat>)"  "N\<in>*\<nat>" "S1\<in>nat \<rightarrow> Pow(nat)" "S2\<in>nat \<rightarrow> Pow(nat)" "S\<in>(\<Prod>i\<in>nat. S1 ` i \<rightarrow> S2 ` i)" "internal_fun(S,\<lambda>_.nat):bij(H,{i\<in>*\<nat>. i *< N})"
  shows "isHyperFinite(H)"
proof-
  from assms(6) have "converse(internal_fun(S,\<lambda>_. nat)):bij({i\<in>*\<nat>. i *< N},H)" using bij_converse_bij by auto
  
  from internal_fun_is_fun[OF assms(3-5)] have "internal_fun(S,\<lambda>_.nat):internal_set(S1,\<lambda>_. nat) \<rightarrow> internal_set(S2,\<lambda>_. nat)".
  then have "H = internal_set(S1,%_. nat)" using domain_of_fun domain_of_bij[OF assms(6)] by auto
  have "internal_fun(S,\<lambda>_. nat) =  {\<langle>hyper_rel(%_. nat)``{x},hyper_rel(X)``{y}\<rangle>. \<langle>x,y\<rangle>\<in>{\<langle>p,q\<rangle>\<in>(nat\<rightarrow>nat)\<times>(nat\<rightarrow>nat). {n:nat. \<langle>p`n,q`n\<rangle>\<in>S`n}\<in>\<FF>}}"
        

end
end