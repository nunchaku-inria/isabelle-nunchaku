theory Nunchaku
imports Main
keywords
  "nunchaku" :: diag and
  "nunchaku_params" :: thy_decl
begin

definition The_unsafe :: "('a \<Rightarrow> bool) \<Rightarrow> 'a" where
  "The_unsafe = The"

definition rmember :: "'a set \<Rightarrow> 'a \<Rightarrow> bool" where
  "rmember A x \<longleftrightarrow> x \<in> A"

ML_file "Tools/nunchaku_util.ML"
ML_file "Tools/nunchaku_collect.ML"
ML_file "Tools/nunchaku_problem.ML"
ML_file "Tools/nunchaku_translate.ML"
ML_file "Tools/nunchaku_model.ML"
ML_file "Tools/nunchaku_reconstruct.ML"
ML_file "Tools/nunchaku_display.ML"
ML_file "Tools/nunchaku_tool.ML"
ML_file "Tools/nunchaku.ML"
ML_file "Tools/nunchaku_commands.ML"

hide_const (open) The_unsafe rmember

codatatype 'a t = T 'a "'a t list"

lemma "(\<forall>x. \<not> P x) \<longrightarrow> The P = y"
nunchaku [card 'x = 2-, expect = genuine, overlord]
oops

lemma "I = (\<lambda>x. x) \<Longrightarrow> The = (\<lambda>x. The (I x))"
nunchaku [expect = none, debug]
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
nunchaku [expect = genuine, show_consts]
oops

lemma "P (Eps P)"
nunchaku [expect = genuine]
oops

lemma "Eps (\<lambda>x. x \<in> P) \<in> (P :: nat set)"
nunchaku [expect = genuine, debug]
oops

lemma "\<not> P (Eps P)"
nunchaku [expect = genuine]
oops

lemma "\<not> (P :: nat \<Rightarrow> bool) (Eps P)"
nunchaku [expect = genuine]
oops

lemma "P \<noteq> bot \<Longrightarrow> P (Eps P)"
nunchaku [expect = none]
sorry

lemma "(P :: nat \<Rightarrow> bool) \<noteq> bot \<Longrightarrow> P (Eps P)"
nunchaku [expect = none]
sorry

lemma "P (The P)"
nunchaku [expect = genuine]
oops

lemma "(P :: nat \<Rightarrow> bool) (The P)"
nunchaku [expect = genuine]
oops

lemma "\<not> P (The P)"
nunchaku [expect = genuine]
oops

lemma "\<not> (P :: nat \<Rightarrow> bool) (The P)"
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

consts Q :: 'a

lemma "Q (Eps Q)"
nunchaku [expect = genuine]
oops

lemma "(Q :: nat \<Rightarrow> bool) (Eps Q)"
nunchaku [expect = genuine]
oops

lemma "\<not> (Q :: nat \<Rightarrow> bool) (Eps Q)"
nunchaku [expect = genuine]
oops

lemma "\<not> (Q :: nat \<Rightarrow> bool) (Eps Q)"
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


lemma "(THE j. j > Suc 2 \<and> j \<le> 5) = x \<Longrightarrow> x = 4"
nunchaku [expect = genuine]
oops

lemma "(THE j. j > Suc 2 \<and> j \<le> 5) = x \<Longrightarrow> x = 4 \<or> x = 5"
nunchaku [expect = genuine]
oops

lemma "(SOME j. j > Suc 2 \<and> j \<le> 3) \<noteq> 0"
nunchaku [expect = genuine]
oops

lemma "(SOME j. j > Suc 2 \<and> j \<le> 4) = x \<Longrightarrow> x \<noteq> 0"
nunchaku [expect = none]
sorry

lemma "(SOME j. j > Suc 2 \<and> j \<le> 4) = x \<Longrightarrow> x = 4"
nunchaku [expect = none]
sorry

lemma "(SOME j. j > Suc 2 \<and> j \<le> 5) = x \<Longrightarrow> x = 4"
nunchaku [expect = genuine]
oops

lemma "(SOME j. j > Suc 2 \<and> j \<le> 5) = x \<Longrightarrow> x = 4 \<or> x = 5"
nunchaku [expect = none]
sorry


end
