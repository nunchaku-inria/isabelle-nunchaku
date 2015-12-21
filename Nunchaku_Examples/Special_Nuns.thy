(*  Title:      HOL/Nunchaku_Examples/Special_Nuns.thy
    Author:     Jasmin Blanchette, Inria Nancy, LORIA, MPII
    Copyright   2009-2015

Examples featuring Nunchaku's specialization optimization.
*)

section {* Examples Featuring Nunchaku's Specialization Optimization *}

theory Special_Nuns
imports "../Nunchaku"
begin

nunchaku_params [verbose, timeout = 240]

fun f1 :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "f1 a b c d e = a + b + c + d + e"

lemma "f1 0 0 0 0 0 = f1 0 0 0 0 (1 - 1)"
nunchaku [expect = none]
nunchaku [dont_specialize, expect = none]
sorry

lemma "f1 u v w x y = f1 y x w v u"
nunchaku [timeout = 5, expect = unknown]
nunchaku [dont_specialize, timeout = 5, expect = unknown]
sorry

fun f2 :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "f2 a b c d (Suc e) = a + b + c + d + e"

lemma "f2 0 0 0 0 0 = f2 (1 - 1) 0 0 0 0"
nunchaku [expect = none]
nunchaku [dont_specialize, expect = none]
sorry

lemma "f2 0 (v - v) 0 (x - x) 0 = f2 (u - u) 0 (w - w) 0 (y - y)"
nunchaku [timeout = 5, expect = unknown]
nunchaku [dont_specialize, timeout = 5, expect = unknown]
sorry

lemma "f2 1 0 0 0 0 = f2 0 1 0 0 0"
nunchaku [expect = genuine]
nunchaku [dont_specialize, expect = genuine]
oops

lemma "f2 0 0 0 0 0 = f2 0 0 0 0 0"
nunchaku [expect = none]
nunchaku [dont_specialize, expect = none]
sorry

fun f3 :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "f3 (Suc a) b 0 d (Suc e) = a + b + d + e"
| "f3 0 b 0 d 0 = b + d"

lemma "f3 a b c d e = f3 e d c b a"
nunchaku [expect = genuine]
nunchaku [dont_specialize, expect = genuine]
oops

lemma "f3 a b c d a = f3 a d c d a"
nunchaku [expect = genuine]
nunchaku [dont_specialize, expect = genuine]
oops

lemma "\<lbrakk>c < 1; a \<ge> e; e \<ge> a\<rbrakk> \<Longrightarrow> f3 a b c d a = f3 e d c b e"
nunchaku [timeout = 5, expect = unknown]
nunchaku [dont_specialize, timeout = 5, expect = unknown]
sorry

lemma "(\<forall>u. a = u \<longrightarrow> f3 a a a a a = f3 u u u u u) \<and> (\<forall>u. b = u \<longrightarrow> f3 b b u b b = f3 u u b u u)"
nunchaku [expect = none]
nunchaku [dont_specialize, expect = none]
sorry

function f4 :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "f4 x x = 1"
| "f4 y z = (if y = z then 1 else 0)"
by auto
termination by lexicographic_order

lemma "f4 a b = f4 b a"
nunchaku [timeout = 5, expect = unknown]
nunchaku [dont_specialize, timeout = 5, expect = unknown]
sorry

lemma "f4 a (Suc a) = f4 a a"
nunchaku [expect = genuine]
nunchaku [dont_specialize, expect = genuine]
oops

fun f5 :: "(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat" where
  "f5 f (Suc a) = f a"

lemma "\<exists>one \<in> {1}. \<exists>two \<in> {2}. f5 (\<lambda>a. if a = one then 1 else if a = two then 2 else a) (Suc x) = x"
nunchaku [expect = none]
nunchaku [dont_specialize, expect = none]
sorry

lemma "\<exists>two \<in> {2}. \<exists>one \<in> {1}. f5 (\<lambda>a. if a = one then 1 else if a = two then 2 else a) (Suc x) = x"
nunchaku [expect = none]
nunchaku [dont_specialize, expect = none]
sorry

lemma "\<exists>one \<in> {1}. \<exists>two \<in> {2}. f5 (\<lambda>a. if a = one then 2 else if a = two then 1 else a) (Suc x) = x"
nunchaku [expect = genuine]
oops

lemma "\<exists>two \<in> {2}. \<exists>one \<in> {1}. f5 (\<lambda>a. if a = one then 2 else if a = two then 1 else a) (Suc x) = x"
nunchaku [expect = genuine]
oops

lemma
  "\<forall>a. g a = a \<Longrightarrow>
   \<exists>one \<in> {1}. \<exists>two \<in> {2}. f5 g x = f5 (\<lambda>a. if a = one then 1 else if a = two then 2 else a) x"
nunchaku [expect = none]
nunchaku [dont_specialize, expect = none]
sorry

lemma
  "\<forall>a. g a = a \<Longrightarrow>
   \<exists>one \<in> {2}. \<exists>two \<in> {1}. f5 g x = f5 (\<lambda>a. if a = one then 1 else if a = two then 2 else a) x"
nunchaku [expect = potential]
nunchaku [dont_specialize, expect = potential]
sorry

lemma
  "\<forall>a. g a = a \<Longrightarrow>
   \<exists>b\<^sub>1 b\<^sub>2 b\<^sub>3 b\<^sub>4 b\<^sub>5 b\<^sub>6 b\<^sub>7 b\<^sub>8 b\<^sub>9 b\<^sub>10 (b\<^sub>11::nat).
   b\<^sub>1 < b\<^sub>11 \<and> f5 g x = f5 (\<lambda>a. if b\<^sub>1 < b\<^sub>11 then a else h b\<^sub>2) x"
nunchaku [expect = potential]
nunchaku [dont_specialize, expect = none]
sorry

lemma
  "\<forall>a. g a = a \<Longrightarrow>
   \<exists>b\<^sub>1 b\<^sub>2 b\<^sub>3 b\<^sub>4 b\<^sub>5 b\<^sub>6 b\<^sub>7 b\<^sub>8 b\<^sub>9 b\<^sub>10 (b\<^sub>11::nat).
   b\<^sub>1 < b\<^sub>11 \<and> f5 g x =
   f5 (\<lambda>a. if b\<^sub>1 < b\<^sub>11 then a else h b\<^sub>2 + h b\<^sub>3 + h b\<^sub>4 + h b\<^sub>5 + h b\<^sub>6 + h b\<^sub>7 + h b\<^sub>8 + h b\<^sub>9 + h b\<^sub>10) x"
nunchaku [timeout = 5, expect = unknown]
sorry

lemma
  "\<forall>a. g a = a \<Longrightarrow>
   \<exists>b\<^sub>1 b\<^sub>2 b\<^sub>3 b\<^sub>4 b\<^sub>5 b\<^sub>6 b\<^sub>7 b\<^sub>8 b\<^sub>9 b\<^sub>10 (b\<^sub>11::nat).
   b\<^sub>1 < b\<^sub>11 \<and> f5 g x =
   f5 (\<lambda>a. if b\<^sub>1 \<ge> b\<^sub>11 then a else h b\<^sub>2 + h b\<^sub>3 + h b\<^sub>4 + h b\<^sub>5 + h b\<^sub>6 + h b\<^sub>7 + h b\<^sub>8 + h b\<^sub>9 + h b\<^sub>10) x"
nunchaku [timeout = 5, expect = potential]
oops

end
