(*  Title:      HOL/Nunchaku_Examples/Typedef_Nuns.thy
    Author:     Jasmin Blanchette, Inria Nancy, LORIA, MPII
    Copyright   2009-2015

Examples featuring Nunchaku applied to typedefs.
*)

section {* Examples Featuring Nunchaku Applied to Typedefs *}

theory Typedef_Nuns
imports Complex_Main "../Nunchaku"
begin

nunchaku_params [verbose, timeout = 240]

definition "three = {0::nat, 1, 2}"
typedef three = three
unfolding three_def by blast

definition A :: three where "A \<equiv> Abs_three 0"
definition B :: three where "B \<equiv> Abs_three 1"
definition C :: three where "C \<equiv> Abs_three 2"

lemma "x = (y::three)"
nunchaku [expect = genuine]
oops

definition "one_or_two = {undefined False::'a, undefined True}"

typedef 'a one_or_two = "one_or_two :: 'a set"
unfolding one_or_two_def by auto

lemma "x = (y::unit one_or_two)"
nunchaku [expect = none]
sorry

lemma "x = (y::bool one_or_two)"
nunchaku [expect = genuine]
oops

lemma "undefined False \<longleftrightarrow> undefined True \<Longrightarrow> x = (y::bool one_or_two)"
nunchaku [expect = none]
sorry

lemma "undefined False \<longleftrightarrow> undefined True \<Longrightarrow> \<exists>x (y::bool one_or_two). x \<noteq> y"
nunchaku [expect = potential] (* unfortunate *)
oops

lemma "\<exists>x (y::bool one_or_two). x \<noteq> y"
nunchaku [expect = none]
oops

definition "bounded = {n::nat. finite (UNIV :: 'a set) \<longrightarrow> n < card (UNIV :: 'a set)}"

typedef 'a bounded = "bounded(TYPE('a))"
unfolding bounded_def
apply (rule_tac x = 0 in exI)
apply (case_tac "card UNIV = 0")
by auto

lemma "x = (y::unit bounded)"
nunchaku [expect = none]
sorry

lemma "x = (y::bool bounded)"
nunchaku [expect = genuine]
oops

lemma "x \<noteq> (y::bool bounded) \<Longrightarrow> z = x \<or> z = y"
nunchaku [expect = potential] (* unfortunate *)
sorry

lemma "x \<noteq> (y::(bool \<times> bool) bounded) \<Longrightarrow> z = x \<or> z = y"
nunchaku [expect = genuine]
oops

lemma "True \<equiv> ((\<lambda>x::bool. x) = (\<lambda>x. x))"
nunchaku [expect = none]
by (rule True_def)

lemma "False \<equiv> \<forall>P. P"
nunchaku [expect = none]
by (rule False_def)

lemma "() = Abs_unit True"
nunchaku [expect = none]
by (rule Unity_def)

lemma "() = Abs_unit False"
nunchaku [expect = none]
by simp

lemma "Rep_unit () = True"
nunchaku [expect = none]
by (insert Rep_unit) simp

lemma "Rep_unit () = False"
nunchaku [expect = genuine]
oops

lemma "Pair a b = Abs_prod (Pair_Rep a b)"
nunchaku [expect = none]
by (rule Pair_def)

lemma "Pair a b = Abs_prod (Pair_Rep b a)"
nunchaku [expect = none]
nunchaku [dont_box, expect = genuine]
oops

lemma "fst (Abs_prod (Pair_Rep a b)) = a"
nunchaku [expect = none]
by (simp add: Pair_def [THEN sym])

lemma "fst (Abs_prod (Pair_Rep a b)) = b"
nunchaku [expect = none]
nunchaku [dont_box, expect = genuine]
oops

lemma "a \<noteq> a' \<Longrightarrow> Pair_Rep a b \<noteq> Pair_Rep a' b"
nunchaku [expect = none]
apply (rule ccontr)
apply simp
apply (drule subst [where P = "\<lambda>r. Abs_prod r = Abs_prod (Pair_Rep a b)"])
 apply (rule refl)
by (simp add: Pair_def [THEN sym])

lemma "Abs_prod (Rep_prod a) = a"
nunchaku [expect = none]
by (rule Rep_prod_inverse)

lemma "Inl \<equiv> \<lambda>a. Abs_sum (Inl_Rep a)"
nunchaku [expect = none]
by (simp add: Inl_def o_def)

lemma "Inl \<equiv> \<lambda>a. Abs_sum (Inr_Rep a)"
nunchaku [card "'a + 'a" = 2, expect = genuine]
oops

lemma "Inl_Rep a \<noteq> Inr_Rep a"
nunchaku [expect = none]
by (rule Inl_Rep_not_Inr_Rep)

lemma "Abs_sum (Rep_sum a) = a"
nunchaku [expect = none]
nunchaku [expect = none]
by (rule Rep_sum_inverse)

lemma "0::nat \<equiv> Abs_Nat Zero_Rep"
nunchaku [expect = none]
by (rule Zero_nat_def [abs_def])

lemma "Suc n = Abs_Nat (Suc_Rep (Rep_Nat n))"
nunchaku [expect = none]
by (rule Nat.Suc_def)

lemma "Suc n = Abs_Nat (Suc_Rep (Suc_Rep (Rep_Nat n)))"
nunchaku [expect = genuine]
oops

lemma "Abs_Nat (Rep_Nat a) = a"
nunchaku [expect = none]
by (rule Rep_Nat_inverse)

lemma "Abs_list (Rep_list a) = a"
(* nunchaku [expect = none] FIXME *)
by (rule Rep_list_inverse)

record point =
  Xcoord :: int
  Ycoord :: int

lemma "Abs_point_ext (Rep_point_ext a) = a"
nunchaku [expect = none]
by (fact Rep_point_ext_inverse)

lemma "Fract a b = of_int a / of_int b"
nunchaku [expect = none]
by (rule Fract_of_int_quotient)

lemma "Abs_rat (Rep_rat a) = a"
nunchaku [expect = none]
by (rule Rep_rat_inverse)

typedef check = "{x::nat. x < 2}" by (rule exI[of _ 0], auto)

lemma "Rep_check (Abs_check n) = n \<Longrightarrow> n < 2"
nunchaku [expect = none]
using Rep_check[of "Abs_check n"] by auto

lemma "Rep_check (Abs_check n) = n \<Longrightarrow> n < 1"
nunchaku [expect = genuine]
oops

end
