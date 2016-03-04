theory Datatype
imports Main
begin

section {* Inductive Datatypes as in Nunchaku or Isabelle/HOL *}

subsection {* Basic Setup *}

hide_type (open) list
hide_const (open) Nil Cons hd tl

text \<open>
This will be called @{text "iota!"} in Nunchaku:
\<close>

definition The_bang :: "('a \<Rightarrow> bool) \<Rightarrow> 'a" where
  "The_bang P = (if \<exists>x. P x then The P else Nitpick.unknown)"

definition pred_of_fun :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> bool" where
  "pred_of_fun p f x y \<longleftrightarrow> p x \<and> f x = y"

typedecl elem
typedecl list

nitpick_params [user_axioms, dont_box, show_all, atoms elem = a b c d e f g h i j k l,
  atoms list = as bs cs ds es fs gs hs "is" js ks ls]


subsection {* Destructors *}

axiomatization
  null :: "list \<Rightarrow> bool" and
  hd :: "list \<Rightarrow> elem" and
  tl :: "list \<Rightarrow> list"
where
  unique_nil: "\<And>xs ys. null xs \<Longrightarrow> null ys \<Longrightarrow> xs = ys" and
  unique_cons: "\<And>xs ys. \<not> null xs \<Longrightarrow> \<not> null ys \<Longrightarrow> hd xs = hd ys \<Longrightarrow> tl xs = tl ys \<Longrightarrow> xs = ys" and
  acyclic: "\<And>xs. \<not> tranclp (pred_of_fun (Not \<circ> null) tl) xs xs"

nitpick_params [card = 1-8]


subsection {* Constructors *}

definition
  Nil :: list
where
  "Nil = The_bang (\<lambda>ys. null ys)"

definition
  Cons :: "elem \<Rightarrow> list \<Rightarrow> list"
where
  "Cons x xs = The_bang (\<lambda>ys. \<not> null ys \<and> hd ys = x \<and> tl ys = xs)"

lemma "Nil \<noteq> Cons x xs"
  nitpick[satisfy, expect = genuine]
  nitpick[expect = none]
  sorry

lemma "xs = Nil \<or> xs = Cons (hd xs) (tl xs)"
  nitpick[satisfy, expect = genuine]
  nitpick [expect = none]
  sorry

lemma "xs \<noteq> Cons x xs"
  nitpick [expect = none]
  sorry

lemma "xs \<noteq> Cons x (Cons y xs)"
  nitpick [expect = none]
  sorry

lemma "xs = ys \<longleftrightarrow> (null xs \<and> null ys) \<or> (\<not> null xs \<and> \<not> null ys \<and> hd xs = hd ys \<and> tl xs = tl ys)"
  nitpick [expect = none]
  sorry

end
