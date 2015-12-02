(*  Title:      HOL/Nunchaku_Examples/Refute_Nuns.thy
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2015

Refute examples adapted to Nunchaku.
*)

section {* Refute Examples Adapted to Nunchaku *}

theory Refute_Nuns
imports "../Nunchaku"
begin

nunchaku_params [verbose, card = 1-6, max_potential = 0, timeout = 240]

lemma "P \<and> Q"
apply (rule conjI)
nunchaku [expect = genuine] 1
nunchaku [expect = genuine] 2
nunchaku [expect = genuine]
nunchaku [card = 5, expect = genuine]
oops

subsection {* Examples and Test Cases *}

subsubsection {* Propositional logic *}

lemma "True"
nunchaku [expect = none]
apply auto
done

lemma "False"
nunchaku[overlord]
nunchaku [expect = genuine]
oops

lemma "P"
nunchaku [expect = genuine]
oops

lemma "\<not> P"
nunchaku [expect = genuine]
oops

lemma "P \<and> Q"
nunchaku [expect = genuine]
oops

lemma "P \<or> Q"
nunchaku [expect = genuine]
oops

lemma "P \<longrightarrow> Q"
nunchaku[overlord]
nunchaku [expect = genuine]
oops

lemma "(P::bool) = Q"
nunchaku [expect = genuine]
oops

lemma "(P \<or> Q) \<longrightarrow> (P \<and> Q)"
nunchaku [expect = genuine]
oops

subsubsection {* Predicate logic *}

lemma "P x y z"
nunchaku [expect = genuine]
oops

lemma "P x y \<longrightarrow> P y x"
nunchaku [expect = genuine]
oops

lemma "P (f (f x)) \<longrightarrow> P x \<longrightarrow> P (f x)"
nunchaku [expect = genuine]
oops

subsubsection {* Equality *}

lemma "P = True"
nunchaku [expect = genuine]
oops

lemma "P = False"
nunchaku [expect = genuine]
oops

lemma "x = y"
nunchaku [expect = genuine]
oops

lemma "f x = g x"
nunchaku [expect = genuine]
oops

lemma "(f::'a\<Rightarrow>'b) = g"
nunchaku [expect = genuine]
oops

lemma "(f::('d\<Rightarrow>'d)\<Rightarrow>('c\<Rightarrow>'d)) = g"
nunchaku [expect = genuine]
oops

lemma "distinct [a, b]"
nunchaku [expect = genuine]
apply simp
nunchaku [expect = genuine]
oops

subsubsection {* First-Order Logic *}

lemma "\<exists>x. P x"
nunchaku [expect = genuine]
oops

lemma "\<forall>x. P x"
nunchaku [expect = genuine]
oops

lemma "\<exists>!x. P x"
nunchaku [expect = genuine]
oops

lemma "Ex P"
nunchaku [expect = genuine]
oops

lemma "All P"
nunchaku [expect = genuine]
oops

lemma "Ex1 P"
nunchaku [expect = genuine]
oops

lemma "(\<exists>x. P x) \<longrightarrow> (\<forall>x. P x)"
nunchaku [expect = genuine]
oops

lemma "(\<forall>x. \<exists>y. P x y) \<longrightarrow> (\<exists>y. \<forall>x. P x y)"
nunchaku [expect = genuine]
oops

lemma "(\<exists>x. P x) \<longrightarrow> (\<exists>!x. P x)"
nunchaku [expect = genuine]
oops

text {* A true statement (also testing names of free and bound variables being identical) *}

lemma "(\<forall>x y. P x y \<longrightarrow> P y x) \<longrightarrow> (\<forall>x. P x y) \<longrightarrow> P y x"
nunchaku [expect = none]
apply fast
done

text {* "A type has at most 4 elements." *}

lemma "\<not> distinct [a, b, c, d, e]"
nunchaku [expect = genuine]
apply simp
nunchaku [expect = genuine]
oops

lemma "distinct [a, b, c, d]"
nunchaku [expect = genuine]
apply simp
nunchaku [expect = genuine]
oops

text {* "Every reflexive and symmetric relation is transitive." *}

lemma "\<lbrakk>\<forall>x. P x x; \<forall>x y. P x y \<longrightarrow> P y x\<rbrakk> \<Longrightarrow> P x y \<longrightarrow> P y z \<longrightarrow> P x z"
nunchaku [expect = genuine]
oops

text {* The ``Drinker's theorem'' *}

lemma "\<exists>x. f x = g x \<longrightarrow> f = g"
nunchaku [expect = none]
apply (auto simp add: ext)
done

text {* And an incorrect version of it *}

lemma "(\<exists>x. f x = g x) \<longrightarrow> f = g"
nunchaku [expect = genuine]
oops

text {* "Every function has a fixed point." *}

lemma "\<exists>x. f x = x"
nunchaku [expect = genuine]
oops

text {* "Function composition is commutative." *}

lemma "f (g x) = g (f x)"
nunchaku [expect = genuine]
oops

text {* "Two functions that are equivalent wrt.\ the same predicate 'P' are equal." *}

lemma "((P::('a\<Rightarrow>'b)\<Rightarrow>bool) f = P g) \<longrightarrow> (f x = g x)"
nunchaku [expect = genuine]
oops

subsubsection {* Higher-Order Logic *}

lemma "\<exists>P. P"
nunchaku [expect = none]
apply auto
done

lemma "\<forall>P. P"
nunchaku [expect = genuine]
oops

lemma "\<exists>!P. P"
nunchaku [expect = none]
apply auto
done

lemma "\<exists>!P. P x"
nunchaku [expect = genuine]
oops

lemma "P Q \<or> Q x"
nunchaku [expect = genuine]
oops

lemma "x \<noteq> All"
nunchaku [expect = genuine]
oops

lemma "x \<noteq> Ex"
nunchaku [expect = genuine]
oops

lemma "x \<noteq> Ex1"
nunchaku [expect = genuine]
oops

text {* ``The transitive closure of an arbitrary relation is non-empty.'' *}

definition "trans" :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool" where
"trans P \<equiv> (ALL x y z. P x y \<longrightarrow> P y z \<longrightarrow> P x z)"

definition
"subset" :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool" where
"subset P Q \<equiv> (ALL x y. P x y \<longrightarrow> Q x y)"

definition
"trans_closure" :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool" where
"trans_closure P Q \<equiv> (subset Q P) \<and> (trans P) \<and> (ALL R. subset Q R \<longrightarrow> trans R \<longrightarrow> subset P R)"

lemma "trans_closure T P \<longrightarrow> (\<exists>x y. T x y)"
nunchaku [expect = genuine]
oops

text {* ``The union of transitive closures is equal to the transitive closure of unions.'' *}

lemma "(\<forall>x y. (P x y \<or> R x y) \<longrightarrow> T x y) \<longrightarrow> trans T \<longrightarrow> (\<forall>Q. (\<forall>x y. (P x y \<or> R x y) \<longrightarrow> Q x y) \<longrightarrow> trans Q \<longrightarrow> subset T Q)
 \<longrightarrow> trans_closure TP P
 \<longrightarrow> trans_closure TR R
 \<longrightarrow> (T x y = (TP x y \<or> TR x y))"
nunchaku [expect = genuine]
oops

text {* ``Every surjective function is invertible.'' *}

lemma "(\<forall>y. \<exists>x. y = f x) \<longrightarrow> (\<exists>g. \<forall>x. g (f x) = x)"
nunchaku [expect = genuine]
oops

text {* ``Every invertible function is surjective.'' *}

lemma "(\<exists>g. \<forall>x. g (f x) = x) \<longrightarrow> (\<forall>y. \<exists>x. y = f x)"
nunchaku [expect = genuine]
oops

text {* ``Every point is a fixed point of some function.'' *}

lemma "\<exists>f. f x = x"
nunchaku [card = 1-7, expect = none]
apply (rule_tac x = "\<lambda>x. x" in exI)
apply simp
done

text {* Axiom of Choice: first an incorrect version *}

lemma "(\<forall>x. \<exists>y. P x y) \<longrightarrow> (\<exists>!f. \<forall>x. P x (f x))"
nunchaku [expect = genuine]
oops

text {* And now two correct ones *}

lemma "(\<forall>x. \<exists>y. P x y) \<longrightarrow> (\<exists>f. \<forall>x. P x (f x))"
nunchaku [card = 1-4, expect = none]
apply (simp add: choice)
done

lemma "(\<forall>x. \<exists>!y. P x y) \<longrightarrow> (\<exists>!f. \<forall>x. P x (f x))"
nunchaku [card = 1-3, expect = none]
apply auto
 apply (simp add: ex1_implies_ex choice)
apply (fast intro: ext)
done

subsubsection {* Metalogic *}

lemma "\<And>x. P x"
nunchaku [expect = genuine]
oops

lemma "f x \<equiv> g x"
nunchaku [expect = genuine]
oops

lemma "P \<Longrightarrow> Q"
nunchaku [expect = genuine]
oops

lemma "\<lbrakk>P; Q; R\<rbrakk> \<Longrightarrow> S"
nunchaku [expect = genuine]
oops

lemma "(x \<equiv> Pure.all) \<Longrightarrow> False"
nunchaku [expect = genuine]
oops

lemma "(x \<equiv> (op \<equiv>)) \<Longrightarrow> False"
nunchaku [expect = genuine]
oops

lemma "(x \<equiv> (op \<Longrightarrow>)) \<Longrightarrow> False"
nunchaku [expect = genuine]
oops

subsubsection {* Schematic Variables *}

schematic_goal "?P"
nunchaku [expect = none]
apply auto
done

schematic_goal "x = ?y"
nunchaku [expect = none]
apply auto
done

subsubsection {* Abstractions *}

lemma "(\<lambda>x. x) = (\<lambda>x. y)"
nunchaku [expect = genuine]
oops

lemma "(\<lambda>f. f x) = (\<lambda>f. True)"
nunchaku [expect = genuine]
oops

lemma "(\<lambda>x. x) = (\<lambda>y. y)"
nunchaku [expect = none]
apply simp
done

subsubsection {* Sets *}

lemma "P (A::'a set)"
nunchaku [expect = genuine]
oops

lemma "P (A::'a set set)"
nunchaku [expect = genuine]
oops

lemma "{x. P x} = {y. P y}"
nunchaku [expect = none]
apply simp
done

lemma "x \<in> {x. P x}"
nunchaku [expect = genuine]
oops

lemma "P (op \<in>)"
nunchaku [expect = genuine]
oops

lemma "P (op \<in> x)"
nunchaku [expect = genuine]
oops

lemma "P Collect"
nunchaku [expect = genuine]
oops

lemma "A Un B = A Int B"
nunchaku [expect = genuine]
oops

lemma "(A Int B) Un C = (A Un C) Int B"
nunchaku [expect = genuine]
oops

lemma "Ball A P \<longrightarrow> Bex A P"
nunchaku [expect = genuine]
oops

subsubsection {* @{const undefined} *}

lemma "undefined"
nunchaku [expect = genuine]
oops

lemma "P undefined"
nunchaku [expect = genuine]
oops

lemma "undefined x"
nunchaku [expect = genuine]
oops

lemma "undefined undefined"
nunchaku [expect = genuine]
oops

subsubsection {* @{const The} *}

lemma "The P"
nunchaku [expect = genuine]
oops

lemma "P The"
nunchaku [expect = genuine]
oops

lemma "P (The P)"
nunchaku [expect = genuine]
oops

lemma "(THE x. x=y) = z"
nunchaku [expect = genuine]
oops

lemma "Ex P \<longrightarrow> P (The P)"
nunchaku [expect = genuine]
oops

subsubsection {* @{const Eps} *}

lemma "Eps P"
nunchaku [expect = genuine]
oops

lemma "P Eps"
nunchaku [expect = genuine]
oops

lemma "P (Eps P)"
nunchaku [expect = genuine]
oops

lemma "(SOME x. x=y) = z"
nunchaku [expect = genuine]
oops

lemma "Ex P \<longrightarrow> P (Eps P)"
nunchaku [expect = none]
apply (auto simp add: someI)
done

subsubsection {* Operations on Natural Numbers *}

lemma "(x::nat) + y = 0"
nunchaku [expect = genuine]
oops

lemma "(x::nat) = x + x"
nunchaku [expect = genuine]
oops

lemma "(x::nat) - y + y = x"
nunchaku [expect = genuine]
oops

lemma "(x::nat) = x * x"
nunchaku [expect = genuine]
oops

lemma "(x::nat) < x + y"
nunchaku [card = 1, expect = genuine]
oops

text {* \<times> *}

lemma "P (x::'a\<times>'b)"
nunchaku [expect = genuine]
oops

lemma "\<forall>x::'a\<times>'b. P x"
nunchaku [expect = genuine]
oops

lemma "P (x, y)"
nunchaku [expect = genuine]
oops

lemma "P (fst x)"
nunchaku [expect = genuine]
oops

lemma "P (snd x)"
nunchaku [expect = genuine]
oops

lemma "P Pair"
nunchaku [expect = genuine]
oops

lemma "P (case x of Pair a b \<Rightarrow> f a b)"
nunchaku [expect = genuine]
oops

subsubsection {* Subtypes (typedef), typedecl *}

text {* A completely unspecified non-empty subset of @{typ "'a"}: *}

definition "myTdef = insert (undefined::'a) (undefined::'a set)"

typedef 'a myTdef = "myTdef :: 'a set"
unfolding myTdef_def by auto

lemma "(x::'a myTdef) = y"
nunchaku [expect = genuine]
oops

typedecl myTdecl

definition "T_bij = {(f::'a\<Rightarrow>'a). \<forall>y. \<exists>!x. f x = y}"

typedef 'a T_bij = "T_bij :: ('a \<Rightarrow> 'a) set"
unfolding T_bij_def by auto

lemma "P (f::(myTdecl myTdef) T_bij)"
nunchaku [expect = genuine]
oops

subsubsection {* Inductive Datatypes *}

text {* unit *}

lemma "P (x::unit)"
nunchaku [expect = genuine]
oops

lemma "\<forall>x::unit. P x"
nunchaku [expect = genuine]
oops

lemma "P ()"
nunchaku [expect = genuine]
oops

lemma "P (case x of () \<Rightarrow> u)"
nunchaku [expect = genuine]
oops

text {* option *}

lemma "P (x::'a option)"
nunchaku [expect = genuine]
oops

lemma "\<forall>x::'a option. P x"
nunchaku [expect = genuine]
oops

lemma "P None"
nunchaku [expect = genuine]
oops

lemma "P (Some x)"
nunchaku [expect = genuine]
oops

lemma "P (case x of None \<Rightarrow> n | Some u \<Rightarrow> s u)"
nunchaku [expect = genuine]
oops

text {* + *}

lemma "P (x::'a+'b)"
nunchaku [expect = genuine]
oops

lemma "\<forall>x::'a+'b. P x"
nunchaku [expect = genuine]
oops

lemma "P (Inl x)"
nunchaku [expect = genuine]
oops

lemma "P (Inr x)"
nunchaku [expect = genuine]
oops

lemma "P Inl"
nunchaku [expect = genuine]
oops

lemma "P (case x of Inl a \<Rightarrow> l a | Inr b \<Rightarrow> r b)"
nunchaku [expect = genuine]
oops

text {* Non-recursive datatypes *}

datatype T1 = A | B

lemma "P (x::T1)"
nunchaku [expect = genuine]
oops

lemma "\<forall>x::T1. P x"
nunchaku [expect = genuine]
oops

lemma "P A"
nunchaku [expect = genuine]
oops

lemma "P B"
nunchaku [expect = genuine]
oops

lemma "rec_T1 a b A = a"
nunchaku [expect = none]
apply simp
done

lemma "rec_T1 a b B = b"
nunchaku [expect = none]
apply simp
done

lemma "P (rec_T1 a b x)"
nunchaku [expect = genuine]
oops

lemma "P (case x of A \<Rightarrow> a | B \<Rightarrow> b)"
nunchaku [expect = genuine]
oops

datatype 'a T2 = C T1 | D 'a

lemma "P (x::'a T2)"
nunchaku [expect = genuine]
oops

lemma "\<forall>x::'a T2. P x"
nunchaku [expect = genuine]
oops

lemma "P D"
nunchaku [expect = genuine]
oops

lemma "rec_T2 c d (C x) = c x"
nunchaku [expect = none]
apply simp
done

lemma "rec_T2 c d (D x) = d x"
nunchaku [expect = none]
apply simp
done

lemma "P (rec_T2 c d x)"
nunchaku [expect = genuine]
oops

lemma "P (case x of C u \<Rightarrow> c u | D v \<Rightarrow> d v)"
nunchaku [expect = genuine]
oops

datatype ('a, 'b) T3 = E "'a \<Rightarrow> 'b"

lemma "P (x::('a, 'b) T3)"
nunchaku [expect = genuine]
oops

lemma "\<forall>x::('a, 'b) T3. P x"
nunchaku [expect = genuine]
oops

lemma "P E"
nunchaku [expect = genuine]
oops

lemma "rec_T3 e (E x) = e x"
nunchaku [card = 1-4, expect = none]
apply simp
done

lemma "P (rec_T3 e x)"
nunchaku [expect = genuine]
oops

lemma "P (case x of E f \<Rightarrow> e f)"
nunchaku [expect = genuine]
oops

text {* Recursive datatypes *}

text {* nat *}

lemma "P (x::nat)"
nunchaku [expect = genuine]
oops

lemma "\<forall>x::nat. P x"
nunchaku [expect = genuine]
oops

lemma "P (Suc 0)"
nunchaku [expect = genuine]
oops

lemma "P Suc"
nunchaku [card = 1-7, expect = none]
oops

lemma "rec_nat zero suc 0 = zero"
nunchaku [expect = none]
apply simp
done

lemma "rec_nat zero suc (Suc x) = suc x (rec_nat zero suc x)"
nunchaku [expect = none]
apply simp
done

lemma "P (rec_nat zero suc x)"
nunchaku [expect = genuine]
oops

lemma "P (case x of 0 \<Rightarrow> zero | Suc n \<Rightarrow> suc n)"
nunchaku [expect = genuine]
oops

text {* 'a list *}

lemma "P (xs::'a list)"
nunchaku [expect = genuine]
oops

lemma "\<forall>xs::'a list. P xs"
nunchaku [expect = genuine]
oops

lemma "P [x, y]"
nunchaku [expect = genuine]
oops

lemma "rec_list nil cons [] = nil"
nunchaku [card = 1-5, expect = none]
apply simp
done

lemma "rec_list nil cons (x#xs) = cons x xs (rec_list nil cons xs)"
nunchaku [card = 1-5, expect = none]
apply simp
done

lemma "P (rec_list nil cons xs)"
nunchaku [expect = genuine]
oops

lemma "P (case x of Nil \<Rightarrow> nil | Cons a b \<Rightarrow> cons a b)"
nunchaku [expect = genuine]
oops

lemma "(xs::'a list) = ys"
nunchaku [expect = genuine]
oops

lemma "a # xs = b # xs"
nunchaku [expect = genuine]
oops

datatype BitList = BitListNil | Bit0 BitList | Bit1 BitList

lemma "P (x::BitList)"
nunchaku [expect = genuine]
oops

lemma "\<forall>x::BitList. P x"
nunchaku [expect = genuine]
oops

lemma "P (Bit0 (Bit1 BitListNil))"
nunchaku [expect = genuine]
oops

lemma "rec_BitList nil bit0 bit1 BitListNil = nil"
nunchaku [expect = none]
apply simp
done

lemma "rec_BitList nil bit0 bit1 (Bit0 xs) = bit0 xs (rec_BitList nil bit0 bit1 xs)"
nunchaku [expect = none]
apply simp
done

lemma "rec_BitList nil bit0 bit1 (Bit1 xs) = bit1 xs (rec_BitList nil bit0 bit1 xs)"
nunchaku [expect = none]
apply simp
done

lemma "P (rec_BitList nil bit0 bit1 x)"
nunchaku [expect = genuine]
oops

datatype 'a BinTree = Leaf 'a | Node "'a BinTree" "'a BinTree"

lemma "P (x::'a BinTree)"
nunchaku [expect = genuine]
oops

lemma "\<forall>x::'a BinTree. P x"
nunchaku [expect = genuine]
oops

lemma "P (Node (Leaf x) (Leaf y))"
nunchaku [expect = genuine]
oops

lemma "rec_BinTree l n (Leaf x) = l x"
nunchaku [expect = none]
apply simp
done

lemma "rec_BinTree l n (Node x y) = n x y (rec_BinTree l n x) (rec_BinTree l n y)"
nunchaku [card = 1-5, expect = none]
apply simp
done

lemma "P (rec_BinTree l n x)"
nunchaku [expect = genuine]
oops

lemma "P (case x of Leaf a \<Rightarrow> l a | Node a b \<Rightarrow> n a b)"
nunchaku [expect = genuine]
oops

text {* Mutually recursive datatypes *}

datatype 'a aexp = Number 'a | ITE "'a bexp" "'a aexp" "'a aexp"
 and 'a bexp = Equal "'a aexp" "'a aexp"

lemma "P (x::'a aexp)"
nunchaku [expect = genuine]
oops

lemma "\<forall>x::'a aexp. P x"
nunchaku [expect = genuine]
oops

lemma "P (ITE (Equal (Number x) (Number y)) (Number x) (Number y))"
nunchaku [expect = genuine]
oops

lemma "P (x::'a bexp)"
nunchaku [expect = genuine]
oops

lemma "\<forall>x::'a bexp. P x"
nunchaku [expect = genuine]
oops

lemma "rec_aexp number ite equal (Number x) = number x"
nunchaku [card = 1-3, expect = none]
apply simp
done

lemma "rec_aexp number ite equal (ITE x y z) = ite x y z (rec_bexp number ite equal x) (rec_aexp number ite equal y) (rec_aexp number ite equal z)"
nunchaku [card = 1-3, expect = none]
apply simp
done

lemma "P (rec_aexp number ite equal x)"
nunchaku [expect = genuine]
oops

lemma "P (case x of Number a \<Rightarrow> number a | ITE b a1 a2 \<Rightarrow> ite b a1 a2)"
nunchaku [expect = genuine]
oops

lemma "rec_bexp number ite equal (Equal x y) = equal x y (rec_aexp number ite equal x) (rec_aexp number ite equal y)"
nunchaku [card = 1-3, expect = none]
apply simp
done

lemma "P (rec_bexp number ite equal x)"
nunchaku [expect = genuine]
oops

lemma "P (case x of Equal a1 a2 \<Rightarrow> equal a1 a2)"
nunchaku [expect = genuine]
oops

datatype X = A | B X | C Y and Y = D X | E Y | F

lemma "P (x::X)"
nunchaku [expect = genuine]
oops

lemma "P (y::Y)"
nunchaku [expect = genuine]
oops

lemma "P (B (B A))"
nunchaku [expect = genuine]
oops

lemma "P (B (C F))"
nunchaku [expect = genuine]
oops

lemma "P (C (D A))"
nunchaku [expect = genuine]
oops

lemma "P (C (E F))"
nunchaku [expect = genuine]
oops

lemma "P (D (B A))"
nunchaku [expect = genuine]
oops

lemma "P (D (C F))"
nunchaku [expect = genuine]
oops

lemma "P (E (D A))"
nunchaku [expect = genuine]
oops

lemma "P (E (E F))"
nunchaku [expect = genuine]
oops

lemma "P (C (D (C F)))"
nunchaku [expect = genuine]
oops

lemma "rec_X a b c d e f A = a"
nunchaku [card = 1-5, expect = none]
apply simp
done

lemma "rec_X a b c d e f (B x) = b x (rec_X a b c d e f x)"
nunchaku [card = 1-5, expect = none]
apply simp
done

lemma "rec_X a b c d e f (C y) = c y (rec_Y a b c d e f y)"
nunchaku [card = 1-5, expect = none]
apply simp
done

lemma "rec_Y a b c d e f (D x) = d x (rec_X a b c d e f x)"
nunchaku [card = 1-5, expect = none]
apply simp
done

lemma "rec_Y a b c d e f (E y) = e y (rec_Y a b c d e f y)"
nunchaku [card = 1-5, expect = none]
apply simp
done

lemma "rec_Y a b c d e f F = f"
nunchaku [card = 1-5, expect = none]
apply simp
done

lemma "P (rec_X a b c d e f x)"
nunchaku [expect = genuine]
oops

lemma "P (rec_Y a b c d e f y)"
nunchaku [expect = genuine]
oops

text {* Other datatype examples *}

text {* Indirect recursion is implemented via mutual recursion. *}

datatype XOpt = CX "XOpt option" | DX "bool \<Rightarrow> XOpt option"

lemma "P (x::XOpt)"
nunchaku [expect = genuine]
oops

lemma "P (CX None)"
nunchaku [expect = genuine]
oops

lemma "P (CX (Some (CX None)))"
nunchaku [expect = genuine]
oops

lemma "P (rec_X cx dx n1 s1 n2 s2 x)"
nunchaku [expect = genuine]
oops

datatype 'a YOpt = CY "('a \<Rightarrow> 'a YOpt) option"

lemma "P (x::'a YOpt)"
nunchaku [expect = genuine]
oops

lemma "P (CY None)"
nunchaku [expect = genuine]
oops

lemma "P (CY (Some (\<lambda>a. CY None)))"
nunchaku [expect = genuine]
oops

datatype Trie = TR "Trie list"

lemma "P (x::Trie)"
nunchaku [expect = genuine]
oops

lemma "\<forall>x::Trie. P x"
nunchaku [expect = genuine]
oops

lemma "P (TR [TR []])"
nunchaku [expect = genuine]
oops

datatype InfTree = Leaf | Node "nat \<Rightarrow> InfTree"

lemma "P (x::InfTree)"
nunchaku [expect = genuine]
oops

lemma "\<forall>x::InfTree. P x"
nunchaku [expect = genuine]
oops

lemma "P (Node (\<lambda>n. Leaf))"
nunchaku [expect = genuine]
oops

lemma "rec_InfTree leaf node Leaf = leaf"
nunchaku [card = 1-3, expect = none]
apply simp
done

lemma "rec_InfTree leaf node (Node g) = node ((\<lambda>InfTree. (InfTree, rec_InfTree leaf node InfTree)) \<circ> g)"
nunchaku [card = 1-3, expect = none]
apply simp
done

lemma "P (rec_InfTree leaf node x)"
nunchaku [expect = genuine]
oops

datatype 'a lambda = Var 'a | App "'a lambda" "'a lambda" | Lam "'a \<Rightarrow> 'a lambda"

lemma "P (x::'a lambda)"
nunchaku [expect = genuine]
oops

lemma "\<forall>x::'a lambda. P x"
nunchaku [expect = genuine]
oops

lemma "P (Lam (\<lambda>a. Var a))"
nunchaku [card = 1-5, expect = none]
nunchaku [card 'a = 4, card "'a lambda" = 5, expect = genuine]
oops

lemma "rec_lambda var app lam (Var x) = var x"
nunchaku [card = 1-3, expect = none]
apply simp
done

lemma "rec_lambda var app lam (App x y) = app x y (rec_lambda var app lam x) (rec_lambda var app lam y)"
nunchaku [card = 1-3, expect = none]
apply simp
done

lemma "rec_lambda var app lam (Lam x) = lam ((\<lambda>lambda. (lambda, rec_lambda var app lam lambda)) \<circ> x)"
nunchaku [card = 1-3, expect = none]
apply simp
done

lemma "P (rec_lambda v a l x)"
nunchaku [expect = genuine]
oops

text {* Taken from "Inductive datatypes in HOL", p. 8: *}

datatype (dead 'a, 'b) T = C "'a \<Rightarrow> bool" | D "'b list"
datatype 'c U = E "('c, 'c U) T"

lemma "P (x::'c U)"
nunchaku [expect = genuine]
oops

lemma "\<forall>x::'c U. P x"
nunchaku [expect = genuine]
oops

lemma "P (E (C (\<lambda>a. True)))"
nunchaku [expect = genuine]
oops

subsubsection {* Records *}

record ('a, 'b) point =
  xpos :: 'a
  ypos :: 'b

lemma "(x::('a, 'b) point) = y"
nunchaku [expect = genuine]
oops

record ('a, 'b, 'c) extpoint = "('a, 'b) point" +
  ext :: 'c

lemma "(x::('a, 'b, 'c) extpoint) = y"
nunchaku [expect = genuine]
oops

subsubsection {* Inductively Defined Sets *}

inductive_set undefinedSet :: "'a set" where
"undefined \<in> undefinedSet"

lemma "x \<in> undefinedSet"
nunchaku [expect = genuine]
oops

inductive_set evenCard :: "'a set set"
where
"{} \<in> evenCard" |
"\<lbrakk>S \<in> evenCard; x \<notin> S; y \<notin> S; x \<noteq> y\<rbrakk> \<Longrightarrow> S \<union> {x, y} \<in> evenCard"

lemma "S \<in> evenCard"
nunchaku [expect = genuine]
oops

inductive_set
even :: "nat set"
and odd :: "nat set"
where
"0 \<in> even" |
"n \<in> even \<Longrightarrow> Suc n \<in> odd" |
"n \<in> odd \<Longrightarrow> Suc n \<in> even"

lemma "n \<in> odd"
nunchaku [expect = genuine]
oops

consts f :: "'a \<Rightarrow> 'a"

inductive_set a_even :: "'a set" and a_odd :: "'a set" where
"undefined \<in> a_even" |
"x \<in> a_even \<Longrightarrow> f x \<in> a_odd" |
"x \<in> a_odd \<Longrightarrow> f x \<in> a_even"

lemma "x \<in> a_odd"
nunchaku [expect = genuine]
oops

subsubsection {* Examples Involving Special Functions *}

lemma "card x = 0"
nunchaku [expect = genuine]
oops

lemma "finite x"
nunchaku [expect = none]
oops

lemma "xs @ [] = ys @ []"
nunchaku [expect = genuine]
oops

lemma "xs @ ys = ys @ xs"
nunchaku [expect = genuine]
oops

lemma "f (lfp f) = lfp f"
nunchaku [card = 2, expect = genuine]
oops

lemma "f (gfp f) = gfp f"
nunchaku [card = 2, expect = genuine]
oops

lemma "lfp f = gfp f"
nunchaku [card = 2, expect = genuine]
oops

subsubsection {* Axiomatic Type Classes and Overloading *}

text {* A type class without axioms: *}

class classA

lemma "P (x::'a::classA)"
nunchaku [expect = genuine]
oops

text {* An axiom with a type variable (denoting types which have at least two elements): *}

class classC =
  assumes classC_ax: "\<exists>x y. x \<noteq> y"

lemma "P (x::'a::classC)"
nunchaku [expect = genuine]
oops

lemma "\<exists>x y. (x::'a::classC) \<noteq> y"
nunchaku [expect = none]
sorry

text {* A type class for which a constant is defined: *}

class classD =
  fixes classD_const :: "'a \<Rightarrow> 'a"
  assumes classD_ax: "classD_const (classD_const x) = classD_const x"

lemma "P (x::'a::classD)"
nunchaku [expect = genuine]
oops

text {* A type class with multiple superclasses: *}

class classE = classC + classD

lemma "P (x::'a::classE)"
nunchaku [expect = genuine]
oops

text {* OFCLASS: *}

lemma "OFCLASS('a::type, type_class)"
nunchaku [expect = none]
apply intro_classes
done

lemma "OFCLASS('a::classC, type_class)"
nunchaku [expect = none]
apply intro_classes
done

lemma "OFCLASS('a::type, classC_class)"
nunchaku [expect = genuine]
oops

text {* Overloading: *}

consts inverse :: "'a \<Rightarrow> 'a"

defs (overloaded)
inverse_bool: "inverse (b::bool) \<equiv> \<not> b"
inverse_set: "inverse (S::'a set) \<equiv> -S"
inverse_pair: "inverse p \<equiv> (inverse (fst p), inverse (snd p))"

lemma "inverse b"
nunchaku [expect = genuine]
oops

lemma "P (inverse (S::'a set))"
nunchaku [expect = genuine]
oops

lemma "P (inverse (p::'a\<times>'b))"
nunchaku [expect = genuine]
oops

end
