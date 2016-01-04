(*  Title:      HOL/Nunchaku_Examples/Manual_Nuns.thy
    Author:     Jasmin Blanchette, Inria Nancy, LORIA, MPII
    Copyright   2009-2014

Examples from the Nunchaku manual.
*)

section {* Examples from the Nunchaku Manual *}

(* The "expect" arguments to Nunchaku in this and other theory files are there because the files
   also serve as a regression test suite. *)

theory Manual_Nuns
imports Real "~~/src/HOL/Library/Quotient_Product" "../Nunchaku"
begin

subsection {* 2. First Steps *}

nunchaku_params [timeout = 240]


subsubsection {* 2.1. Propositional Logic *}

lemma "P \<longleftrightarrow> Q"
nunchaku [expect = genuine]
apply auto
nunchaku [expect = genuine] 1
nunchaku [expect = genuine] 2
oops


subsubsection {* 2.2. Type Variables *}

lemma "x \<in> A \<Longrightarrow> (THE y. y \<in> A) \<in> A"
nunchaku [verbose, expect = genuine]
oops


subsubsection {* 2.3. Constants *}

lemma "x \<in> A \<Longrightarrow> (THE y. y \<in> A) \<in> A"
nunchaku [show_consts, expect = genuine]
nunchaku [dont_specialize, show_consts, expect = genuine]
oops

lemma "\<exists>!x. x \<in> A \<Longrightarrow> (THE y. y \<in> A) \<in> A"
nunchaku [expect = none]
(* sledgehammer *)
by (metis the_equality)


subsubsection {* 2.4. Skolemization *}

lemma "\<exists>g. \<forall>x. g (f x) = x \<Longrightarrow> \<forall>y. \<exists>x. y = f x"
nunchaku [expect = genuine]
oops

lemma "\<exists>x. \<forall>f. f x = x"
nunchaku [expect = genuine]
oops

lemma "refl r \<Longrightarrow> sym r"
nunchaku [expect = genuine]
oops


subsubsection {* 2.5. Natural Numbers and Integers *}

lemma "\<lbrakk>i \<le> j; n \<le> (m :: int)\<rbrakk> \<Longrightarrow> i * n + j * m \<le> i * m + j * n"
nunchaku [expect = genuine]
oops

lemma "(\<forall>n. Suc n \<noteq> n) \<Longrightarrow> P"
nunchaku [timeout = 5, expect = potential]
oops

lemma "P Suc"
nunchaku [expect = genuine]
oops

lemma "P (op + :: nat \<Rightarrow> nat \<Rightarrow> nat)"
nunchaku [expect = genuine]
oops


subsubsection {* 2.6. Inductive Datatypes *}

lemma "hd (xs @ [y, y]) = hd xs"
nunchaku [expect = genuine]
nunchaku [show_consts, expect = genuine]
oops

lemma "\<lbrakk>length xs = 1; length ys = 1\<rbrakk> \<Longrightarrow> xs = ys"
nunchaku [expect = genuine]
oops


subsubsection {* 2.7. Typedefs, Records, Rationals, and Reals *}

definition "three = {0 :: nat, 1, 2}"
typedef three = three
  unfolding three_def by blast

definition A :: three where "A \<equiv> Abs_three 0"
definition B :: three where "B \<equiv> Abs_three 1"
definition C :: three where "C \<equiv> Abs_three 2"

lemma "\<lbrakk>A \<in> X; B \<in> X\<rbrakk> \<Longrightarrow> c \<in> X"
nunchaku [expect = genuine]
oops

fun my_int_rel where
  "my_int_rel (x, y) (u, v) = (x + v = u + y)"

quotient_type my_int = "nat \<times> nat" / my_int_rel
by (auto simp add: equivp_def fun_eq_iff)

definition add_raw where
  "add_raw \<equiv> \<lambda>(x, y) (u, v). (x + (u :: nat), y + (v :: nat))"

quotient_definition "add :: my_int \<Rightarrow> my_int \<Rightarrow> my_int" is add_raw
unfolding add_raw_def by auto

lemma "add x y = add x x"
nunchaku [expect = genuine]
oops

record point =
  Xcoord :: int
  Ycoord :: int

lemma "Xcoord (p :: point) = Xcoord (q :: point)"
nunchaku [expect = genuine]
oops

lemma "4 * x + 3 * (y :: real) \<noteq> 1 / 2"
nunchaku [expect = genuine]
oops


subsubsection {* 2.8. Inductive and Coinductive Predicates *}

inductive even where
  "even 0"
| "even n \<Longrightarrow> even (Suc (Suc n))"

lemma "\<exists>n. even n \<and> even (Suc n)"
nunchaku [timeout = 5, expect = potential]
oops

lemma "\<exists>n \<le> 49. even n \<and> even (Suc n)"
nunchaku [expect = genuine]
oops

inductive even' where
  "even' (0 :: nat)"
| "even' 2"
| "\<lbrakk>even' m; even' n\<rbrakk> \<Longrightarrow> even' (m + n)"

lemma "\<exists>n \<in> {0, 2, 4, 6, 8}. \<not> even' n"
nunchaku [verbose, show_consts, expect = genuine]
oops

lemma "even' (n - 2) \<Longrightarrow> even' n"
nunchaku [show_consts, expect = genuine]
oops

coinductive nats where
  "nats (x :: nat) \<Longrightarrow> nats x"

lemma "nats = (\<lambda>n. n \<in> {0, 1, 2, 3, 4})"
nunchaku [show_consts, expect = genuine]
oops

inductive odd where
  "odd 1"
| "\<lbrakk>odd m; even n\<rbrakk> \<Longrightarrow> odd (m + n)"

lemma "odd n \<Longrightarrow> odd (n - 2)"
nunchaku [show_consts, expect = genuine]
oops


subsubsection {* 2.9. Coinductive Datatypes *}

codatatype 'a llist = LNil | LCons 'a "'a llist"

primcorec iterates where
  "iterates f a = LCons a (iterates f (f a))"

lemma "xs \<noteq> LCons a xs"
nunchaku [expect = genuine]
oops

lemma "\<lbrakk>xs = LCons a xs; ys = iterates (\<lambda>b. a) b\<rbrakk> \<Longrightarrow> xs = ys"
nunchaku [verbose, expect = genuine]
oops

lemma "\<lbrakk>xs = LCons a xs; ys = LCons a ys\<rbrakk> \<Longrightarrow> xs = ys"
nunchaku [expect = none]
sorry


subsubsection {* 2.10. Boxing *}

datatype tm =
  Var nat
| Lam tm
| App tm tm

primrec lift where
  "lift (Var j) k = Var (if j < k then j else j + 1)"
| "lift (Lam t) k = Lam (lift t (k + 1))"
| "lift (App t u) k = App (lift t k) (lift u k)"

primrec loose where
  "loose (Var j) k = (j \<ge> k)"
| "loose (Lam t) k = loose t (Suc k)"
| "loose (App t u) k = (loose t k \<or> loose u k)"

primrec subst\<^sub>1 where
  "subst\<^sub>1 \<sigma> (Var j) = \<sigma> j"
| "subst\<^sub>1 \<sigma> (Lam t) = Lam (subst\<^sub>1 (\<lambda>n. case n of 0 \<Rightarrow> Var 0 | Suc m \<Rightarrow> lift (\<sigma> m) 1) t)"
| "subst\<^sub>1 \<sigma> (App t u) = App (subst\<^sub>1 \<sigma> t) (subst\<^sub>1 \<sigma> u)"

lemma "\<not> loose t 0 \<Longrightarrow> subst\<^sub>1 \<sigma> t = t"
nunchaku [verbose, expect = genuine]
nunchaku [eval = "subst\<^sub>1 \<sigma> t", expect = genuine]
oops

primrec subst\<^sub>2 where
  "subst\<^sub>2 \<sigma> (Var j) = \<sigma> j"
| "subst\<^sub>2 \<sigma> (Lam t) = Lam (subst\<^sub>2 (\<lambda>n. case n of 0 \<Rightarrow> Var 0 | Suc m \<Rightarrow> lift (\<sigma> m) 0) t)"
| "subst\<^sub>2 \<sigma> (App t u) = App (subst\<^sub>2 \<sigma> t) (subst\<^sub>2 \<sigma> u)"

lemma "\<not> loose t 0 \<Longrightarrow> subst\<^sub>2 \<sigma> t = t"
nunchaku [expect = none]
sorry


subsubsection {* 2.11. Scope Monotonicity *}

lemma "length xs = length ys \<Longrightarrow> rev (zip xs ys) = zip xs (rev ys)"
nunchaku [verbose, expect = genuine]
oops

lemma "\<exists>g. \<forall>x :: 'b. g (f x) = x \<Longrightarrow> \<forall>y :: 'a. \<exists>x. y = f x"
nunchaku [expect = genuine]
oops


subsubsection {* 2.12. Inductive Properties *}

inductive_set reach where
"(4 :: nat) \<in> reach" |
"n \<in> reach \<Longrightarrow> n < 4 \<Longrightarrow> 3 * n + 1 \<in> reach" |
"n \<in> reach \<Longrightarrow> n + 2 \<in> reach"

lemma "n \<in> reach \<Longrightarrow> 2 dvd n"
(* nunchaku *)
apply (induct set: reach)
  apply auto
 nunchaku [timeout = 5, expect = unknown]
 apply (thin_tac "n \<in> reach")
 nunchaku [expect = genuine]
oops

lemma "n \<in> reach \<Longrightarrow> 2 dvd n \<and> n \<noteq> 0"
(* nunchaku *)
apply (induct set: reach)
  apply auto
 nunchaku [timeout = 5, expect = unknown]
 apply (thin_tac "n \<in> reach")
 nunchaku [expect = genuine]
oops

lemma "n \<in> reach \<Longrightarrow> 2 dvd n \<and> n \<ge> 4"
by (induct set: reach) arith+


subsection {* 3. Case Studies *}

nunchaku_params [max_potential = 0]


subsubsection {* 3.1. A Context-Free Grammar *}

datatype alphabet = a | b

inductive_set S\<^sub>1 and A\<^sub>1 and B\<^sub>1 where
  "[] \<in> S\<^sub>1"
| "w \<in> A\<^sub>1 \<Longrightarrow> b # w \<in> S\<^sub>1"
| "w \<in> B\<^sub>1 \<Longrightarrow> a # w \<in> S\<^sub>1"
| "w \<in> S\<^sub>1 \<Longrightarrow> a # w \<in> A\<^sub>1"
| "w \<in> S\<^sub>1 \<Longrightarrow> b # w \<in> S\<^sub>1"
| "\<lbrakk>v \<in> B\<^sub>1; v \<in> B\<^sub>1\<rbrakk> \<Longrightarrow> a # v @ w \<in> B\<^sub>1"

theorem S\<^sub>1_sound:
"w \<in> S\<^sub>1 \<longrightarrow> length [x \<leftarrow> w. x = a] = length [x \<leftarrow> w. x = b]"
nunchaku [expect = genuine]
oops

inductive_set S\<^sub>2 and A\<^sub>2 and B\<^sub>2 where
  "[] \<in> S\<^sub>2"
| "w \<in> A\<^sub>2 \<Longrightarrow> b # w \<in> S\<^sub>2"
| "w \<in> B\<^sub>2 \<Longrightarrow> a # w \<in> S\<^sub>2"
| "w \<in> S\<^sub>2 \<Longrightarrow> a # w \<in> A\<^sub>2"
| "w \<in> S\<^sub>2 \<Longrightarrow> b # w \<in> B\<^sub>2"
| "\<lbrakk>v \<in> B\<^sub>2; v \<in> B\<^sub>2\<rbrakk> \<Longrightarrow> a # v @ w \<in> B\<^sub>2"

theorem S\<^sub>2_sound:
"w \<in> S\<^sub>2 \<longrightarrow> length [x \<leftarrow> w. x = a] = length [x \<leftarrow> w. x = b]"
nunchaku [expect = genuine]
oops

inductive_set S\<^sub>3 and A\<^sub>3 and B\<^sub>3 where
  "[] \<in> S\<^sub>3"
| "w \<in> A\<^sub>3 \<Longrightarrow> b # w \<in> S\<^sub>3"
| "w \<in> B\<^sub>3 \<Longrightarrow> a # w \<in> S\<^sub>3"
| "w \<in> S\<^sub>3 \<Longrightarrow> a # w \<in> A\<^sub>3"
| "w \<in> S\<^sub>3 \<Longrightarrow> b # w \<in> B\<^sub>3"
| "\<lbrakk>v \<in> B\<^sub>3; w \<in> B\<^sub>3\<rbrakk> \<Longrightarrow> a # v @ w \<in> B\<^sub>3"

theorem S\<^sub>3_sound:
"w \<in> S\<^sub>3 \<longrightarrow> length [x \<leftarrow> w. x = a] = length [x \<leftarrow> w. x = b]"
nunchaku [expect = none]
sorry

theorem S\<^sub>3_complete:
"length [x \<leftarrow> w. x = a] = length [x \<leftarrow> w. x = b] \<longrightarrow> w \<in> S\<^sub>3"
nunchaku [expect = genuine]
oops

inductive_set S\<^sub>4 and A\<^sub>4 and B\<^sub>4 where
  "[] \<in> S\<^sub>4"
| "w \<in> A\<^sub>4 \<Longrightarrow> b # w \<in> S\<^sub>4"
| "w \<in> B\<^sub>4 \<Longrightarrow> a # w \<in> S\<^sub>4"
| "w \<in> S\<^sub>4 \<Longrightarrow> a # w \<in> A\<^sub>4"
| "\<lbrakk>v \<in> A\<^sub>4; w \<in> A\<^sub>4\<rbrakk> \<Longrightarrow> b # v @ w \<in> A\<^sub>4"
| "w \<in> S\<^sub>4 \<Longrightarrow> b # w \<in> B\<^sub>4"
| "\<lbrakk>v \<in> B\<^sub>4; w \<in> B\<^sub>4\<rbrakk> \<Longrightarrow> a # v @ w \<in> B\<^sub>4"

theorem S\<^sub>4_sound:
"w \<in> S\<^sub>4 \<longrightarrow> length [x \<leftarrow> w. x = a] = length [x \<leftarrow> w. x = b]"
nunchaku [expect = none]
sorry

theorem S\<^sub>4_complete:
"length [x \<leftarrow> w. x = a] = length [x \<leftarrow> w. x = b] \<longrightarrow> w \<in> S\<^sub>4"
nunchaku [expect = none]
sorry

theorem S\<^sub>4_A\<^sub>4_B\<^sub>4_sound_and_complete:
"w \<in> S\<^sub>4 \<longleftrightarrow> length [x \<leftarrow> w. x = a] = length [x \<leftarrow> w. x = b]"
"w \<in> A\<^sub>4 \<longleftrightarrow> length [x \<leftarrow> w. x = a] = length [x \<leftarrow> w. x = b] + 1"
"w \<in> B\<^sub>4 \<longleftrightarrow> length [x \<leftarrow> w. x = b] = length [x \<leftarrow> w. x = a] + 1"
nunchaku [expect = none]
sorry


subsubsection {* 3.2. AA Trees *}

datatype 'a aa_tree = \<Lambda> | N "'a :: linorder" nat "'a aa_tree" "'a aa_tree"

primrec data where
  "data \<Lambda> = undefined"
| "data (N x _ _ _) = x"

primrec dataset where
  "dataset \<Lambda> = {}"
| "dataset (N x _ t u) = {x} \<union> dataset t \<union> dataset u"

primrec level where
  "level \<Lambda> = 0"
| "level (N _ k _ _) = k"

primrec left where
  "left \<Lambda> = \<Lambda>"
| "left (N _ _ t\<^sub>1 _) = t\<^sub>1"

primrec right where
  "right \<Lambda> = \<Lambda>"
| "right (N _ _ _ t\<^sub>2) = t\<^sub>2"

fun wf where
  "wf \<Lambda> = True"
| "wf (N _ k t u) =
   (if t = \<Lambda> then k = 1 \<and> (u = \<Lambda> \<or> (level u = 1 \<and> left u = \<Lambda> \<and> right u = \<Lambda>))
    else wf t \<and> wf u \<and> u \<noteq> \<Lambda> \<and> level t < k \<and> level u \<le> k \<and> level (right u) < k)"

fun skew where
  "skew \<Lambda> = \<Lambda>"
| "skew (N x k t u) =
   (if t \<noteq> \<Lambda> \<and> k = level t then N (data t) k (left t) (N x k (right t) u)
    else N x k t u)"

fun split where
  "split \<Lambda> = \<Lambda>"
| "split (N x k t u) =
   (if u \<noteq> \<Lambda> \<and> k = level (right u) then N (data u) (Suc k) (N x k t (left u)) (right u)
    else N x k t u)"

theorem dataset_skew_split:
  "dataset (skew t) = dataset t"
  "dataset (split t) = dataset t"
nunchaku [expect = none]
sorry

theorem wf_skew_split:
  "wf t \<Longrightarrow> skew t = t"
  "wf t \<Longrightarrow> split t = t"
nunchaku [expect = none]
sorry

primrec insort\<^sub>1 where
  "insort\<^sub>1 \<Lambda> x = N x 1 \<Lambda> \<Lambda>"
| "insort\<^sub>1 (N y k t u) x =
   (* (split \<circ> skew) *)
   (N y k (if x < y then insort\<^sub>1 t x else t) (if x > y then insort\<^sub>1 u x else u))"

theorem wf_insort\<^sub>1: "wf t \<Longrightarrow> wf (insort\<^sub>1 t x)"
nunchaku [expect = genuine]
oops

theorem wf_insort\<^sub>1_nat:
"wf t \<Longrightarrow>
t = N 1 1 \<Lambda> \<Lambda> \<Longrightarrow>
x = 0 \<Longrightarrow>
wf (insort\<^sub>1 t (x :: nat))"
nunchaku [eval = "insort\<^sub>1 t x", expect = genuine]
oops

primrec insort\<^sub>2 where
"insort\<^sub>2 \<Lambda> x = N x 1 \<Lambda> \<Lambda>" |
"insort\<^sub>2 (N y k t u) x =
 (split \<circ> skew) (N y k (if x < y then insort\<^sub>2 t x else t)
                       (if x > y then insort\<^sub>2 u x else u))"

theorem wf_insort\<^sub>2: "wf t \<Longrightarrow> wf (insort\<^sub>2 t x)"
nunchaku [expect = none]
sorry

theorem dataset_insort\<^sub>2: "dataset (insort\<^sub>2 t x) = {x} \<union> dataset t"
nunchaku [expect = none]
sorry

end
