(*  Title:      HOL/Nunchaku_Examples/Core_Nuns.thy
    Author:     Jasmin Blanchette, Inria Nancy, LORIA, MPII
    Copyright   2009-2015

Examples featuring Nunchaku's functional core.
*)

section {* Examples Featuring Nunchaku's Functional Core *}

theory Core_Nuns
imports "../Nunchaku"
begin

nunchaku_params [verbose, max_potential = 0, timeout = 240]


subsection {* Curry in a Hurry *}

lemma "(\<lambda>f x y. (curry o case_prod) f x y) = (\<lambda>f x y. (\<lambda>x. x) f x y)"
nunchaku [expect = none]
by auto

lemma "(\<lambda>f p. (case_prod o curry) f p) = (\<lambda>f p. (\<lambda>x. x) f p)"
nunchaku [expect = none]
by auto

lemma "case_prod (curry f) = f"
nunchaku [expect = none]
by auto

lemma "curry (case_prod f) = f"
nunchaku [expect = none]
by auto

lemma "case_prod (\<lambda>x y. f (x, y)) = f"
nunchaku [expect = none]
by auto


subsection {* Representations *}

lemma "\<exists>f. f = (\<lambda>x. x) \<and> f y = y"
nunchaku [expect = none]
by auto

lemma "(\<exists>g. \<forall>x. g (f x) = x) \<longrightarrow> (\<forall>y. \<exists>x. y = f x)"
nunchaku [card 'a = 25, card 'b = 24, expect = genuine]
nunchaku [mono, expect = none]
oops

lemma "\<exists>f. f = (\<lambda>x. x) \<and> f y \<noteq> y"
nunchaku [expect = genuine]
oops

lemma "P (\<lambda>x. x)"
nunchaku [expect = genuine]
oops

lemma "{(a :: 'a \<times> 'a, b :: 'b)}^-1 = {(b, a)}"
nunchaku [expect = none]
by auto

lemma "fst (a, b) = a"
nunchaku [expect = none]
by auto

lemma "\<exists>P. P = Id"
nunchaku [expect = none]
by auto

lemma "(a :: 'a \<Rightarrow> 'b, a) \<in> Id\<^sup>*"
nunchaku [expect = none]
by auto

lemma "(a :: 'a \<times> 'a, a) \<in> Id\<^sup>* \<union> {(a, b)}\<^sup>*"
nunchaku [expect = none]
by auto

lemma "(a, a) \<in> Id"
nunchaku [expect = none]
by (auto simp: Id_def)

lemma "((a :: 'a, b :: 'a), (a, b)) \<in> Id"
nunchaku [expect = none]
by (auto simp: Id_def)

lemma "(x :: 'a \<times> 'a) \<in> UNIV"
nunchaku [expect = none]
sorry

lemma "{} = A - A"
nunchaku [expect = none]
by auto

lemma "g = Let (A \<or> B)"
nunchaku [expect = none]
nunchaku [expect = genuine]
oops

lemma "(let a_or_b = A \<or> B in a_or_b \<or> \<not> a_or_b)"
nunchaku [expect = none]
by auto

lemma "A \<subseteq> B"
nunchaku [expect = genuine]
oops

lemma "A = {b}"
nunchaku [expect = genuine]
oops

lemma "{a, b} = {b}"
nunchaku [expect = genuine]
oops

lemma "(a :: 'a \<times> 'a, a :: 'a \<times> 'a) \<in> R"
nunchaku [expect = genuine]
oops

lemma "f (g :: 'a \<Rightarrow> 'a) = x"
nunchaku [expect = genuine]
oops

lemma "f (a, b) = x"
nunchaku [expect = genuine]
oops

lemma "f (a, a) = f (c, d)"
nunchaku [expect = genuine]
oops

lemma "(x :: 'a) = (\<lambda>a. \<lambda>b. \<lambda>c. if c then a else b) x x True"
nunchaku [expect = none]
by auto

lemma "\<exists>F. F a b = G a b"
nunchaku [expect = none]
by auto

lemma "f = case_prod"
nunchaku [expect = genuine]
oops

lemma "(A :: 'a \<times> 'a, B :: 'a \<times> 'a) \<in> R \<Longrightarrow> (A, B) \<in> R"
nunchaku [expect = none]
by auto

lemma "(A, B) \<in> R \<or> (\<exists>C. (A, C) \<in> R \<and> (C, B) \<in> R) \<Longrightarrow>
       A = B \<or> (A, B) \<in> R \<or> (\<exists>C. (A, C) \<in> R \<and> (C, B) \<in> R)"
nunchaku [expect = none]
by auto

lemma "f = (\<lambda>x :: 'a \<times> 'b. x)"
nunchaku [expect = genuine]
oops


subsection {* Quantifiers *}

lemma "x = y"
nunchaku [expect = genuine]
oops

lemma "\<forall>x. x = y"
nunchaku [expect = genuine]
oops

lemma "\<forall>x :: 'a \<Rightarrow> bool. x = y"
nunchaku [expect = genuine]
oops

lemma "\<exists>x :: 'a \<Rightarrow> bool. x = y"
nunchaku [expect = unknown]
by auto

lemma "\<exists>x y :: 'a \<Rightarrow> bool. x = y"
nunchaku [expect = unknown]
by auto

lemma "\<forall>x. \<exists>y. f x y = f x (g x)"
nunchaku [expect = none]
by auto

lemma "\<forall>u. \<exists>v. \<forall>w. \<exists>x. f u v w x = f u (g u) w (h u w)"
nunchaku [expect = none]
by auto

lemma "\<forall>u. \<exists>v. \<forall>w. \<exists>x. f u v w x = f u (g u w) w (h u)"
nunchaku [expect = genuine]
oops

lemma "\<forall>u. \<exists>v. \<forall>w. \<exists>x. \<forall>y. \<exists>z. f u v w x y z = f u (g u) w (h u w) y (k u w y)"
nunchaku [expect = none]
by auto

lemma "\<forall>u. \<exists>v. \<forall>w. \<exists>x. \<forall>y. \<exists>z. f u v w x y z = f u (g u) w (h u w y) y (k u w y)"
nunchaku [expect = genuine]
oops

lemma "\<forall>u. \<exists>v. \<forall>w. \<exists>x. \<forall>y. \<exists>z. f u v w x y z = f u (g u w) w (h u w) y (k u w y)"
nunchaku [expect = genuine]
oops

lemma "\<forall>u :: 'a \<times> 'b. \<exists>v :: 'c. \<forall>w :: 'd. \<exists>x :: 'e \<times> 'f. f u v w x = f u (g u) w (h u w)"
nunchaku [expect = none]
by blast

lemma "\<forall>u :: 'a \<times> 'b. \<exists>v :: 'c. \<forall>w :: 'd. \<exists>x :: 'e \<times> 'f. f u v w x = f u (g u w) w (h u)"
nunchaku [expect = genuine]
oops

lemma "\<forall>u :: 'a \<Rightarrow> 'b. \<exists>v :: 'c. \<forall>w :: 'd. \<exists>x :: 'e \<Rightarrow> 'f. f u v w x = f u (g u) w (h u w)"
nunchaku [expect = none]
by blast

lemma "\<forall>u :: 'a \<Rightarrow> 'b. \<exists>v :: 'c. \<forall>w :: 'd. \<exists>x :: 'e \<Rightarrow> 'f. f u v w x = f u (g u w) w (h u)"
nunchaku [expect = genuine]
oops

lemma "\<forall>x. if \<forall>y. x = y then False else True"
nunchaku [expect = genuine]
oops

lemma "\<forall>x :: 'a \<times> 'b. if \<forall>y. x = y then False else True"
nunchaku [expect = genuine]
oops

lemma "\<forall>x. if \<exists>y. x = y then True else False"
nunchaku [expect = none]
by simp

lemma "(\<exists>x :: 'a. \<forall>y. P x y) \<or> (\<exists>x :: 'a \<times> 'a. \<forall>y. P y x)"
nunchaku [expect = genuine]
oops

lemma "\<exists>x. if x = y then \<forall>y. y = x \<or> y \<noteq> x else \<forall>y. y = (x, x) \<or> y \<noteq> (x, x)"
nunchaku [expect = none]
by auto

lemma "\<exists>x. if x = y then \<exists>y. y = x \<or> y \<noteq> x else \<exists>y. y = (x, x) \<or> y \<noteq> (x, x)"
nunchaku [expect = none]
by auto

lemma "let x = (\<forall>x. P x) in if x then x else \<not> x"
nunchaku [expect = none]
by auto

lemma "let x = (\<forall>x :: 'a \<times> 'b. P x) in if x then x else \<not> x"
nunchaku [expect = none]
by auto


subsection {* Schematic Variables *}

schematic_goal "x = ?x"
nunchaku [expect = none]
by auto

schematic_goal "\<forall>x. x = ?x"
nunchaku [expect = genuine]
oops

schematic_goal "\<exists>x. x = ?x"
nunchaku [expect = none]
by auto

schematic_goal "\<exists>x :: 'a \<Rightarrow> 'b. x = ?x"
nunchaku [expect = none]
by auto

schematic_goal "\<forall>x. ?x = ?y"
nunchaku [expect = none]
by auto

schematic_goal "\<exists>x. ?x = ?y"
nunchaku [expect = none]
by auto


subsection {* Known Constants *}

lemma "\<And>x. f x y = f x y"
nunchaku [expect = none]
oops

lemma "\<And>x. f x y = f y x"
nunchaku [expect = genuine]
oops

lemma "P x \<equiv> P x"
nunchaku [expect = none]
by auto

lemma "P x \<equiv> Q x \<Longrightarrow> P x = Q x"
nunchaku [expect = none]
by auto

lemma "P x = Q x \<Longrightarrow> P x \<equiv> Q x"
nunchaku [expect = none]
by auto

lemma "P x \<Longrightarrow> P x"
nunchaku [expect = none]
by auto

lemma "True \<Longrightarrow> True" "False \<Longrightarrow> True" "False \<Longrightarrow> False"
nunchaku [expect = none]
by auto

lemma "True \<Longrightarrow> False"
nunchaku [expect = genuine]
oops

lemma "x = Not"
nunchaku [expect = genuine]
oops

lemma "I = (\<lambda>x. x) \<Longrightarrow> Not = (\<lambda>x. Not (I x))"
nunchaku [expect = none]
by auto

lemma "x = True"
nunchaku [expect = genuine]
oops

lemma "x = False"
nunchaku [expect = genuine]
oops

lemma "x = undefined"
nunchaku [expect = genuine]
oops

lemma "(False, ()) = undefined \<Longrightarrow> ((), False) = undefined"
nunchaku [expect = genuine]
oops

lemma "undefined = undefined"
nunchaku [expect = none]
by auto

lemma "f undefined = f undefined"
nunchaku [expect = none]
by auto

lemma "f undefined = g undefined"
nunchaku [expect = genuine]
oops

lemma "\<exists>!x. x = undefined"
nunchaku [expect = none]
by auto

lemma "\<forall>x. f x y = f x y"
nunchaku [expect = none]
oops

lemma "\<forall>x. f x y = f y x"
nunchaku [expect = genuine]
oops

lemma "All (\<lambda>x. f x y = f x y) = True"
nunchaku [expect = none]
by auto

lemma "All (\<lambda>x. f x y = f x y) = False"
nunchaku [expect = genuine]
oops

lemma "x = Ex \<Longrightarrow> False"
nunchaku [expect = genuine]
oops

lemma "\<exists>x. f x y = f x y"
nunchaku [expect = none]
oops

lemma "\<exists>x. f x y = f y x"
nunchaku [expect = none]
oops

lemma "Ex (\<lambda>x. f x y = f x y) = True"
nunchaku [expect = none]
by auto

lemma "Ex (\<lambda>x. f x y = f y x) = True"
nunchaku [expect = none]
by auto

lemma "Ex (\<lambda>x. f x y = f x y) = False"
nunchaku [expect = genuine]
oops

lemma "Ex (\<lambda>x. f x y \<noteq> f x y) = False"
nunchaku [expect = none]
by auto

lemma "I = (\<lambda>x. x) \<Longrightarrow> Ex P = Ex (\<lambda>x. P (I x))"
nunchaku [expect = none]
by auto

lemma "x = y \<Longrightarrow> y = x"
nunchaku [expect = none]
by auto

lemma "x = y \<Longrightarrow> f x = f y"
nunchaku [expect = none]
by auto

lemma "x = y \<and> y = z \<Longrightarrow> x = z"
nunchaku [expect = none]
by auto

lemma "I = (\<lambda>x. x) \<Longrightarrow> (op \<and>) = (\<lambda>x. op \<and> (I x))"
      "I = (\<lambda>x. x) \<Longrightarrow> (op \<and>) = (\<lambda>x y. x \<and> (I y))"
nunchaku [expect = none]
by auto

lemma "(a \<and> b) = (\<not> (\<not> a \<or> \<not> b))"
nunchaku [expect = none]
by auto

lemma "a \<and> b \<Longrightarrow> a" "a \<and> b \<Longrightarrow> b"
nunchaku [expect = none]
by auto

lemma "(op \<longrightarrow>) = (\<lambda>x. op\<longrightarrow> x)" "(op\<longrightarrow> ) = (\<lambda>x y. x \<longrightarrow> y)"
nunchaku [expect = none]
by auto

lemma "((if a then b else c) = d) = ((a \<longrightarrow> (b = d)) \<and> (\<not> a \<longrightarrow> (c = d)))"
nunchaku [expect = none]
by auto

lemma "(if a then b else c) = (THE d. (a \<longrightarrow> (d = b)) \<and> (\<not> a \<longrightarrow> (d = c)))"
nunchaku [expect = none]
by auto

lemma "fst (x, y) = x"
nunchaku [expect = none]
by (simp add: fst_def)

lemma "snd (x, y) = y"
nunchaku [expect = none]
by (simp add: snd_def)

lemma "fst (x :: 'a \<Rightarrow> 'b, y) = x"
nunchaku [expect = none]
by (simp add: fst_def)

lemma "snd (x :: 'a \<Rightarrow> 'b, y) = y"
nunchaku [expect = none]
by (simp add: snd_def)

lemma "fst (x, y :: 'a \<Rightarrow> 'b) = x"
nunchaku [expect = none]
by (simp add: fst_def)

lemma "snd (x, y :: 'a \<Rightarrow> 'b) = y"
nunchaku [expect = none]
by (simp add: snd_def)

lemma "fst (x :: 'a \<times> 'b, y) = x"
nunchaku [expect = none]
by (simp add: fst_def)

lemma "snd (x :: 'a \<times> 'b, y) = y"
nunchaku [expect = none]
by (simp add: snd_def)

lemma "fst (x, y :: 'a \<times> 'b) = x"
nunchaku [expect = none]
by (simp add: fst_def)

lemma "snd (x, y :: 'a \<times> 'b) = y"
nunchaku [expect = none]
by (simp add: snd_def)

lemma "I = (\<lambda>x. x) \<Longrightarrow> fst = (\<lambda>x. fst (I x))"
nunchaku [expect = none]
by auto

lemma "fst (x, y) = snd (y, x)"
nunchaku [expect = none]
by auto

lemma "(x, x) \<in> Id"
nunchaku [expect = none]
by auto

lemma "(x, y) \<in> Id \<Longrightarrow> x = y"
nunchaku [expect = none]
by auto

lemma "I = (\<lambda>x. x) \<Longrightarrow> Id = {x. I x \<in> Id}"
nunchaku [expect = none]
by auto

lemma "{} = {x. False}"
nunchaku [expect = none]
by (metis empty_def)

lemma "x \<in> {}"
nunchaku [expect = genuine]
oops

lemma "{a, b} = {b}"
nunchaku [expect = genuine]
oops

lemma "{a, b} \<noteq> {b}"
nunchaku [expect = genuine]
oops

lemma "{a} = {b}"
nunchaku [expect = genuine]
oops

lemma "{a} \<noteq> {b}"
nunchaku [expect = genuine]
oops

lemma "{a, b, c} = {c, b, a}"
nunchaku [expect = none]
by auto

lemma "UNIV = {x. True}"
nunchaku [expect = none]
by (simp only: UNIV_def)

lemma "x \<in> UNIV \<longleftrightarrow> True"
nunchaku [expect = none]
by (simp only: UNIV_def mem_Collect_eq)

lemma "x \<notin> UNIV"
nunchaku [expect = genuine]
oops

lemma "I = (\<lambda>x. x) \<Longrightarrow> op \<in> = (\<lambda>x. (op \<in> (I x)))"
nunchaku [expect = none]
apply (rule ext)
apply (rule ext)
by simp

lemma "insert = (\<lambda>x y. insert x (y \<union> y))"
nunchaku [expect = none]
by simp

lemma "I = (\<lambda>x. x) \<Longrightarrow> trancl = (\<lambda>x. trancl (I x))"
nunchaku [expect = none]
by auto

lemma "rtrancl = (\<lambda>x. rtrancl x \<union> {(y, y)})"
nunchaku [expect = none]
apply (rule ext)
by auto

lemma "(x, x) \<in> rtrancl {(y, y)}"
nunchaku [expect = none]
by auto

lemma "((x, x), (x, x)) \<in> rtrancl {}"
nunchaku [expect = none]
by auto

lemma "I = (\<lambda>x. x) \<Longrightarrow> op \<union> = (\<lambda>x. op \<union> (I x))"
nunchaku [expect = none]
by auto

lemma "a \<in> A \<Longrightarrow> a \<in> (A \<union> B)" "b \<in> B \<Longrightarrow> b \<in> (A \<union> B)"
nunchaku [expect = none]
by auto

lemma "I = (\<lambda>x. x) \<Longrightarrow> op \<inter> = (\<lambda>x. op \<inter> (I x))"
nunchaku [expect = none]
by auto

lemma "a \<notin> A \<Longrightarrow> a \<notin> (A \<inter> B)" "b \<notin> B \<Longrightarrow> b \<notin> (A \<inter> B)"
nunchaku [expect = none]
by auto

lemma "x \<in> ((A :: 'a set) - B) \<longleftrightarrow> x \<in> A \<and> x \<notin> B"
nunchaku [expect = none]
by auto

lemma "I = (\<lambda>x. x) \<Longrightarrow> op \<subset> = (\<lambda>x. op \<subset> (I x))"
nunchaku [expect = none]
by auto

lemma "A \<subset> B \<Longrightarrow> (\<forall>a \<in> A. a \<in> B) \<and> (\<exists>b \<in> B. b \<notin> A)"
nunchaku [expect = none]
by auto

lemma "A \<subseteq> B \<Longrightarrow> \<forall>a \<in> A. a \<in> B"
nunchaku [expect = none]
by auto

lemma "A \<subseteq> B \<Longrightarrow> A \<subset> B"
nunchaku [expect = genuine]
oops

lemma "A \<subset> B \<Longrightarrow> A \<subseteq> B"
nunchaku [expect = none]
by auto

lemma "I = (\<lambda>x :: 'a set. x) \<Longrightarrow> uminus = (\<lambda>x. uminus (I x))"
nunchaku [expect = none]
by auto

lemma "A \<union> - A = UNIV"
nunchaku [expect = none]
by auto

lemma "A \<inter> - A = {}"
nunchaku [expect = none]
by auto

lemma "A = -(A :: 'a set)"
nunchaku [card 'a = 10, expect = genuine]
oops

lemma "finite A"
nunchaku [expect = none]
oops

lemma "finite A \<Longrightarrow> finite B"
nunchaku [expect = none]
oops

lemma "All finite"
nunchaku [expect = none]
oops

subsection {* The and Eps *}

lemma "x = The"
nunchaku [expect = genuine]
oops

lemma "\<exists>x. x = The"
nunchaku [expect = none]
nunchaku [expect = genuine]
oops

lemma "P x \<Longrightarrow> P (The P)"
nunchaku [expect = none]
nunchaku [expect = genuine]
oops

lemma "(\<forall>x. \<not> P x) \<longrightarrow> The P = y"
nunchaku [expect = genuine]
oops

lemma "I = (\<lambda>x. x) \<Longrightarrow> The = (\<lambda>x. The (I x))"
nunchaku [expect = none]
by auto

lemma "x = Eps"
nunchaku [expect = genuine]
oops

lemma "\<exists>x. x = Eps"
nunchaku [expect = none]
by auto

lemma "P x \<and> (\<forall>y. P y \<longrightarrow> y = x) \<longrightarrow> Eps P = x"
nunchaku [expect = none]
by auto

lemma "P x \<and> P y \<and> x \<noteq> y \<longrightarrow> Eps P = z"
nunchaku [expect = genuine]
apply auto
oops

lemma "P x \<Longrightarrow> P (Eps P)"
nunchaku [expect = none]
by (metis exE_some)

lemma "\<forall>x. \<not> P x \<longrightarrow> Eps P = y"
nunchaku [expect = genuine]
oops

lemma "P (Eps P)"
nunchaku [expect = genuine]
oops

lemma "Eps (\<lambda>x. x \<in> P) \<in> (P :: nat set)"
nunchaku [expect = genuine]
oops

lemma "\<not> P (Eps P)"
nunchaku [expect = genuine]
oops

lemma "\<not> (P  ::  nat \<Rightarrow> bool) (Eps P)"
nunchaku [expect = genuine]
oops

lemma "P \<noteq> bot \<Longrightarrow> P (Eps P)"
nunchaku [expect = none]
sorry

lemma "(P  ::  nat \<Rightarrow> bool) \<noteq> bot \<Longrightarrow> P (Eps P)"
nunchaku [expect = none]
sorry

lemma "P (The P)"
nunchaku [expect = genuine]
oops

lemma "(P  ::  nat \<Rightarrow> bool) (The P)"
nunchaku [expect = genuine]
oops

lemma "\<not> P (The P)"
nunchaku [expect = genuine]
oops

lemma "\<not> (P  ::  nat \<Rightarrow> bool) (The P)"
nunchaku [expect = genuine]
oops

lemma "The P \<noteq> x"
nunchaku [expect = genuine]
oops

lemma "The P \<noteq> (x :: nat)"
nunchaku [expect = genuine]
oops

lemma "P x \<Longrightarrow> P (The P)"
nunchaku [expect = genuine]
oops

lemma "P (x :: nat) \<Longrightarrow> P (The P)"
nunchaku [expect = genuine]
oops

lemma "P = {x} \<Longrightarrow> (THE x. x \<in> P) \<in> P"
nunchaku [expect = none]
oops

lemma "P = {x :: nat} \<Longrightarrow> (THE x. x \<in> P) \<in> P"
nunchaku [expect = none]
oops

consts Q  ::  'a

lemma "Q (Eps Q)"
nunchaku [expect = genuine]
oops

lemma "(Q  ::  nat \<Rightarrow> bool) (Eps Q)"
nunchaku [expect = none] (* unfortunate *)
oops

lemma "\<not> (Q  ::  nat \<Rightarrow> bool) (Eps Q)"
nunchaku [expect = genuine]
oops

lemma "\<not> (Q  ::  nat \<Rightarrow> bool) (Eps Q)"
nunchaku [expect = genuine]
oops

lemma "(Q :: 'a \<Rightarrow> bool) \<noteq> bot \<Longrightarrow> (Q :: 'a \<Rightarrow> bool) (Eps Q)"
nunchaku [expect = none]
sorry

lemma "(Q :: nat \<Rightarrow> bool) \<noteq> bot \<Longrightarrow> (Q :: nat \<Rightarrow> bool) (Eps Q)"
nunchaku [expect = none]
sorry

lemma "Q (The Q)"
nunchaku [expect = genuine]
oops

lemma "(Q :: nat \<Rightarrow> bool) (The Q)"
nunchaku [expect = genuine]
oops

lemma "\<not> Q (The Q)"
nunchaku [expect = genuine]
oops

lemma "\<not> (Q :: nat \<Rightarrow> bool) (The Q)"
nunchaku [expect = genuine]
oops

lemma "The Q \<noteq> x"
nunchaku [expect = genuine]
oops

lemma "The Q \<noteq> (x :: nat)"
nunchaku [expect = genuine]
oops

lemma "Q x \<Longrightarrow> Q (The Q)"
nunchaku [expect = genuine]
oops

lemma "Q (x :: nat) \<Longrightarrow> Q (The Q)"
nunchaku [expect = genuine]
oops

lemma "Q = (\<lambda>x :: 'a. x = a) \<Longrightarrow> (Q :: 'a \<Rightarrow> bool) (The Q)"
nunchaku [expect = none]
sorry

lemma "Q = (\<lambda>x :: nat. x = a) \<Longrightarrow> (Q :: nat \<Rightarrow> bool) (The Q)"
nunchaku [expect = none]
sorry

nunchaku_params [max_potential = 1]

lemma "(THE j. j > Suc 2 \<and> j \<le> 3) \<noteq> 0"
nunchaku [card nat = 2, expect = potential]
nunchaku [card nat = 6, expect = potential] (* unfortunate *)
oops

lemma "(THE j. j > Suc 2 \<and> j \<le> 4) = x \<Longrightarrow> x \<noteq> 0"
nunchaku [card nat = 2, expect = potential]
nunchaku [card nat = 6, expect = none]
sorry

lemma "(THE j. j > Suc 2 \<and> j \<le> 4) = x \<Longrightarrow> x = 4"
nunchaku [card nat = 2, expect = potential]
nunchaku [card nat = 6, expect = none]
sorry

lemma "(THE j. j > Suc 2 \<and> j \<le> 5) = x \<Longrightarrow> x = 4"
nunchaku [card nat = 6, expect = genuine]
oops

lemma "(THE j. j > Suc 2 \<and> j \<le> 5) = x \<Longrightarrow> x = 4 \<or> x = 5"
nunchaku [card nat = 6, expect = genuine]
oops

lemma "(SOME j. j > Suc 2 \<and> j \<le> 3) \<noteq> 0"
nunchaku [card nat = 2, expect = potential]
nunchaku [card nat = 6, expect = genuine]
oops

lemma "(SOME j. j > Suc 2 \<and> j \<le> 4) = x \<Longrightarrow> x \<noteq> 0"
nunchaku [card nat = 2, expect = potential]
nunchaku [card nat = 6, expect = none]
oops

lemma "(SOME j. j > Suc 2 \<and> j \<le> 4) = x \<Longrightarrow> x = 4"
nunchaku [card nat = 2, expect = potential]
nunchaku [card nat = 6, expect = none]
sorry

lemma "(SOME j. j > Suc 2 \<and> j \<le> 5) = x \<Longrightarrow> x = 4"
nunchaku [card nat = 6, expect = genuine]
oops

lemma "(SOME j. j > Suc 2 \<and> j \<le> 5) = x \<Longrightarrow> x = 4 \<or> x = 5"
nunchaku [card nat = 6, expect = none]
sorry

nunchaku_params [max_potential = 0]

subsection {* Destructors and Recursors *}

lemma "(x :: 'a) = (case True of True \<Rightarrow> x | False \<Rightarrow> x)"
nunchaku [expect = none]
by auto

lemma "x = (case (x, y) of (x', y') \<Rightarrow> x')"
nunchaku [expect = none]
sorry

end
