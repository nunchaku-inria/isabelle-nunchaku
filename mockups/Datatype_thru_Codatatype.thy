theory Datatype_thru_Codatatype
imports Main
begin

section {* Inductive Datatypes with Nesting through Codatatypes as in Isabelle/HOL *}

text {*
The abstract interface between a datatype and a codatatype through which it is
nested is a set function that returns the elements. This is modeled below by a
@{text subtrees} predicate.
*}


subsection {* Basic Setup *}

hide_const (open) Nil Cons hd tl

text \<open>
This will be called @{text "iota!"} in Nunchaku:
\<close>

definition The_bang :: "('a \<Rightarrow> bool) \<Rightarrow> 'a" where
  "The_bang P = (if \<exists>x. P x then The P else Nitpick.unknown)"

definition pred_of_fun :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> bool" where
  "pred_of_fun p f x y \<longleftrightarrow> p x \<and> f x = y"

typedecl elem
typedecl tree
typedecl forest

nitpick_params [user_axioms, dont_box, show_all, atoms elem = a b c d e f g h i j k l,
  atoms forest = as bs cs ds es fs gs hs "is" js ks ls,
  atoms tree = aa bb cc dd ee ff gg hh ii jj kk ll]


subsection {* Codatatype Destructors *}

axiomatization
  null :: "forest \<Rightarrow> bool" and
  hd :: "forest \<Rightarrow> tree" and
  tl :: "forest \<Rightarrow> forest"

coinductive bisim :: "forest \<Rightarrow> forest \<Rightarrow> bool" where
  "null xs \<Longrightarrow> null ys \<Longrightarrow> bisim xs ys"
| "\<not> null xs \<Longrightarrow> \<not> null ys \<Longrightarrow> hd xs = hd ys \<Longrightarrow> bisim (tl xs) (tl ys) \<Longrightarrow> bisim xs ys"

text \<open>
@{prop "hd xs = hd ys"} is appropriate, as opposed to lifting @{const bisim}
with the tree relator.
\<close>

axiomatization where
  bisim: "\<And>xs ys. bisim xs ys \<Longrightarrow> xs = ys"

definition
  subtrees :: "forest \<Rightarrow> tree \<Rightarrow> bool"
where
  "subtrees = rtranclp (pred_of_fun (Not \<circ> null) tl) OO pred_of_fun (Not \<circ> null) hd"


subsection {* Datatype Destructors *}

axiomatization
  lab :: "tree \<Rightarrow> elem" and
  sub :: "tree \<Rightarrow> forest"
where
  unique: "\<And>xs ys. lab xs = lab ys \<Longrightarrow> sub xs = sub ys \<Longrightarrow> xs = ys" and
  acyclic: "\<And>xs. \<not> tranclp (pred_of_fun (\<lambda>_. True) sub OO subtrees) xs xs"

nitpick_params [card elem = 3, card forest = 1-5, card tree = 1-5, iter = 1-5, mono]


subsection {* Codatatype Constructors *}

definition
  Nil :: forest
where
  "Nil = The_bang (\<lambda>ys. null ys)"

definition
  Cons :: "tree \<Rightarrow> forest \<Rightarrow> forest"
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

lemma "xs \<noteq> Nil \<Longrightarrow> xs \<noteq> sub (hd xs)"
  nitpick [expect = none]
  sorry


subsection {* Datatype Constructors *}

definition
  Node :: "elem \<Rightarrow> forest \<Rightarrow> tree"
where
  "Node x xs = The_bang (\<lambda>yy. lab yy = x \<and> sub yy = xs)"

lemma "xx \<noteq> Node x (Cons xx xs)"
  nitpick [expect = none]
  sorry

lemma "xx \<noteq> Node x (Cons (Node y (Cons xx Nil)) Nil)"
  nitpick [expect = none]
  nitpick [satisfy, expect = genuine]
  sorry

lemma "xx = yy \<longleftrightarrow> lab xx = lab yy \<and> sub xx = sub yy"
  nitpick [expect = none]
  sorry

lemma "sub xx \<noteq> Nil \<Longrightarrow> tl (sub xx) \<noteq> sub xx"
  nitpick [expect = genuine]
  oops

lemma "xs = Cons (Node x xs) Nil"
  nitpick [satisfy, expect = none]
  oops

end
