theory Nunchaku
imports Main
keywords
  "nunchaku" :: diag and
  "nunchaku_params" :: thy_decl
begin

definition rmember :: "'a set \<Rightarrow> 'a \<Rightarrow> bool" where
  "rmember A x \<longleftrightarrow> x \<in> A"

ML_file "Tools/nunchaku_util.ML"
ML_file "Tools/nunchaku_collect.ML"
ML_file "Tools/nunchaku_problem.ML"
ML_file "Tools/nunchaku_tool.ML"
ML_file "Tools/nunchaku_translate.ML"
ML_file "Tools/nunchaku_model.ML"
ML_file "Tools/nunchaku.ML"
ML_file "Tools/nunchaku_commands.ML"

axiomatization nonzero where
  nz: "nonzero \<noteq> (0 :: nat)"

axiomatization where
  foo: "(undefined :: nat \<Rightarrow> nat) undefined = undefined"

lemma "x \<noteq> y"
nunchaku[card = 6]


(*
schematic_goal "rev (xs :: ?'a list) = xs \<and> rev ys = ys"
nunchaku[card = 6]

lemma "x \<in> {y. y = x}"
nunchaku
oops

schematic_goal "x = ?y"
nunchaku [expect = none]

declare [[ML_exception_trace]]
declare [[ML_print_depth = 100]]

lemma "P a \<Longrightarrow> P b \<Longrightarrow> P (case xs of [] \<Rightarrow> a | y # ys \<Rightarrow> b)"
nunchaku

lemma "P (op \<and>)"
nunchaku
oops

lemma "P (Ex)"
nunchaku
oops

lemma "{a, b} \<noteq> {}"
nunchaku[debug]

lemma "Abs_Integ i \<noteq> j"
oops

lemma "Abs_int i \<noteq> j"
oops


typedef 'a bit = "{undefined :: 'a}"
  by auto

lemma
  fixes b1 b2 b3 :: "int"
  shows "b1 \<noteq> b2 \<and> b2 \<noteq> b3 \<and> b1 \<noteq> b3 \<and> b1 \<noteq> Abs_Integ d"
  nunchaku

lemma "r a b \<Longrightarrow> rtranclp r a b"
nunchaku

inductive even and odd where
  "even 0"
| "even m \<Longrightarrow> odd (Suc m)"
| "even n \<Longrightarrow> even (Suc (Suc n))"

lemma "even n"
nunchaku
oops

lemma "rev xs = ys \<and> rev ys = xs"
nunchaku[debug,overlord,satisfy]
oops
*)

(*
declare [[ML_exception_trace]]

oops

lemma "rev xs = xs"
nunchaku[overlord]
oops

lemma "[x] @ ys = x # ys"
nunchaku[overlord]
oops
*)

hide_const (open) rmember

end
