theory Codatatype_thru_Datatype
imports Main
begin

section {* Inductive Datatypes with Nesting through Codatatypes as in Isabelle/HOL *}

text {*
The abstract interface between a codatatype and a datatype through which it is
nested is a relator. This is modeled below by an @{text all2} predicate.
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


subsection {* Datatype Destructors *}

axiomatization
  null :: "forest \<Rightarrow> bool" and
  hd :: "forest \<Rightarrow> tree" and
  tl :: "forest \<Rightarrow> forest"

axiomatization where
  unique_nil: "\<And>xs ys. null xs \<Longrightarrow> null ys \<Longrightarrow> xs = ys" and
  unique_cons: "\<And>xs ys. \<not> null xs \<Longrightarrow> \<not> null ys \<Longrightarrow> hd xs = hd ys \<Longrightarrow> tl xs = tl ys \<Longrightarrow> xs = ys" and
  acyclic: "\<And>xs. \<not> tranclp (pred_of_fun (Not \<circ> null) tl) xs xs"

text \<open>
It is important to ignore the lists hiding under the trees for acyclicity.
\<close>

inductive
  all2 :: "(tree \<Rightarrow> tree \<Rightarrow> bool) \<Rightarrow> forest \<Rightarrow> forest \<Rightarrow> bool"
where
  "null xs \<Longrightarrow> null ys \<Longrightarrow> all2 p xs ys"
|  "\<not> null xs \<Longrightarrow> \<not> null ys \<Longrightarrow> p (hd xs) (hd ys) \<Longrightarrow> all2 p (tl xs) (tl ys) \<Longrightarrow> all2 p xs ys"

lemma all2_mono[mono]: "(\<And>xx yy. p xx yy \<longrightarrow> q xx yy) \<Longrightarrow> all2 p xs ys \<longrightarrow> all2 q xs ys"
  sorry


subsection {* Codatatype Destructors *}

axiomatization
  lab :: "tree \<Rightarrow> elem" and
  sub :: "tree \<Rightarrow> forest"
thm rel_fun_mono'

coinductive bisim :: "tree \<Rightarrow> tree \<Rightarrow> bool" where
  "lab xx = lab yy \<Longrightarrow> all2 bisim (sub xx) (sub yy) \<Longrightarrow> bisim xx yy"

axiomatization where
  unique: "\<And>xs ys. bisim xs ys \<Longrightarrow> xs = ys"

nitpick_params [card elem = 3, card forest = 1-5, card tree = 1-5, iter = 1-5, mono]


subsection {* Datatype Constructors *}

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
  nitpick [expect = none]
  sorry

lemma "xs \<noteq> Cons x (Cons y xs)"
  nitpick [expect = none]
  sorry

lemma "xs = ys \<longleftrightarrow> (null xs \<and> null ys) \<or> (\<not> null xs \<and> \<not> null ys \<and> hd xs = hd ys \<and> tl xs = tl ys)"
  nitpick [expect = none]
  sorry

lemma "xs \<noteq> Nil \<Longrightarrow> xs \<noteq> sub (hd xs)"
  nitpick [expect = genuine]
  oops


subsection {* Codatatype Constructors *}

definition
  Node :: "elem \<Rightarrow> forest \<Rightarrow> tree"
where
  "Node x xs = The_bang (\<lambda>yy. lab yy = x \<and> sub yy = xs)"

lemma "xx \<noteq> Node x (Cons xx xs)"
  nitpick [expect = genuine]
  sorry

lemma "xx \<noteq> Node x (Cons (Node y (Cons xx Nil)) Nil)"
  nitpick [expect = genuine]
  nitpick [satisfy, expect = genuine]
  sorry

lemma "xx = yy \<longleftrightarrow> lab xx = lab yy \<and> sub xx = sub yy"
  nitpick [expect = none]
  sorry

lemma "sub xx \<noteq> Nil \<Longrightarrow> tl (sub xx) \<noteq> sub xx"
  nitpick [expect = none]
  oops

end
