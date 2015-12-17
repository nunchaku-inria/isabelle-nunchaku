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

text {* An axiom with a type variable (denoting types which have at least two elements): *}

class classC =
  assumes classC_ax: "\<exists>x y. x \<noteq> y"

lemma "P (%x. f x x) (x :: 'a :: classC)"
nunchaku [expect = genuine]
oops

lemma "\<exists>x y. (x :: 'a :: classC) \<noteq> y"
nunchaku [expect = none]
sorry

text {* A type class for which a constant is defined: *}

class classD =
  fixes classD_const :: "'a \<Rightarrow> 'a"
  assumes classD_ax: "classD_const (classD_const x) = classD_const x"

lemma "P (x :: 'a :: classD)"
nunchaku [expect = genuine]
oops

text {* A type class with multiple superclasses: *}

class classE = classC + classD

lemma "P (x :: 'a :: classE)"
nunchaku [expect = genuine]
oops

text {* OFCLASS: *}

lemma "OFCLASS('a :: type, type_class)"
nunchaku [expect = none]
apply intro_classes
done

lemma "OFCLASS('a :: classC, type_class)"
nunchaku [expect = none]
apply intro_classes
done

lemma "OFCLASS('a :: type, classC_class)"
nunchaku [expect = genuine]
oops

text {* Overloading: *}

consts inverse :: "'a \<Rightarrow> 'a"

defs (overloaded)
inverse_bool: "inverse (b :: bool) \<equiv> \<not> b"
inverse_set: "inverse (S :: 'a set) \<equiv> -S"
inverse_pair: "inverse p \<equiv> (inverse (fst p), inverse (snd p))"

lemma "inverse b"
nunchaku [expect = genuine]
oops

lemma "P (inverse (S :: 'a set))"
nunchaku [expect = genuine]
oops

lemma "P (inverse (p :: 'a \<times> 'b))"
nunchaku [expect = genuine]
oops


(*
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
