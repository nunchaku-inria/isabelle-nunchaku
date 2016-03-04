theory Codatatypes
imports Main
begin

section {* Coinductive Datatypes as in Nunchaku or Isabelle/HOL *}

subsection {* Basic Setup *}

hide_type (open) list
hide_const (open) Nil Cons hd tl

text \<open>
This will be called @{text "iota!"} in Nunchaku:
\<close>

definition The_bang :: "('a \<Rightarrow> bool) \<Rightarrow> 'a" where
  "The_bang P = (if \<exists>x. P x then The P else Nitpick.unknown)"

typedecl elem
typedecl list

nitpick_params [user_axioms, dont_box, show_all, atoms elem = a b c d e f g h i j k l,
  atoms list = as bs cs ds es fs gs hs "is" js ks ls]


subsection {* Selectors *}

axiomatization
  null :: "list \<Rightarrow> bool" and
  hd :: "list \<Rightarrow> elem" and
  tl :: "list \<Rightarrow> list"

coinductive bisim :: "list \<Rightarrow> list \<Rightarrow> bool" where
  "null xs \<Longrightarrow> bisim xs xs"
| "\<not> null xs \<Longrightarrow> \<not> null ys \<Longrightarrow> hd xs = hd ys \<Longrightarrow> bisim (tl xs) (tl ys) \<Longrightarrow> bisim xs ys"

axiomatization where
  unique_nil: "\<And>xs ys. null xs \<Longrightarrow> null ys \<Longrightarrow> xs = ys" and
  unique_cons: "\<And>xs ys. \<not> null xs \<Longrightarrow> \<not> null ys \<Longrightarrow> hd xs = hd ys \<Longrightarrow> tl xs = tl ys \<Longrightarrow> xs = ys" and
  unique: "\<And>xs ys. bisim xs ys \<Longrightarrow> xs = ys"

nitpick_params [card elem = 3, card list = 1-5]


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
  nitpick [expect = genuine]
  oops

lemma "xs \<noteq> Cons x (Cons y xs)"
  nitpick [expect = genuine]
  oops

lemma "x \<noteq> y \<Longrightarrow> xs \<noteq> Cons x (Cons y xs)"
  nitpick [expect = genuine]
  oops

lemma "xs = ys \<longleftrightarrow> (null xs \<and> null ys) \<or> (\<not> null xs \<and> \<not> null ys \<and> hd xs = hd ys \<and> tl xs = tl ys)"
  nitpick [expect = none]
  sorry

lemma "xs = Cons x ys \<Longrightarrow> ys = Cons x xs \<Longrightarrow> xs = ys"
  nitpick [expect = none]
  nitpick [satisfy, expect = genuine]
  sorry

end
