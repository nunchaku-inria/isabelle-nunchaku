(*  Title:      HOL/Nunchaku_Examples/Pattern_Nuns.thy
    Author:     Jasmin Blanchette, Inria Nancy, LORIA, MPII
    Copyright   2009-2015

Examples featuring Nunchaku's "destroy_constrs" optimization.
*)

section {* Examples Featuring Nunchaku's \textit{destroy\_constrs} Optimization *}

theory Pattern_Nuns
imports Main
begin

nunchaku_params [verbose, max_potential = 0, sat_solver = MiniSat_JNI,
                timeout = 240]

lemma "x = (case u of () \<Rightarrow> y)"
nunchaku [expect = genuine]
oops

lemma "x = (case b of True \<Rightarrow> x | False \<Rightarrow> y)"
nunchaku [expect = genuine]
oops

lemma "x = (case p of (x, y) \<Rightarrow> y)"
nunchaku [expect = genuine]
oops

lemma "x = (case n of 0 \<Rightarrow> x | Suc n \<Rightarrow> n)"
nunchaku [expect = genuine]
oops

lemma "x = (case opt of None \<Rightarrow> x | Some y \<Rightarrow> y)"
nunchaku [expect = genuine]
oops

lemma "x = (case xs of [] \<Rightarrow> x | y # ys \<Rightarrow> y)"
nunchaku [expect = genuine]
oops

lemma "x = (case xs of
              [] \<Rightarrow> x
            | y # ys \<Rightarrow>
              (case ys of
                 [] \<Rightarrow> x
               | z # zs \<Rightarrow>
                 (case z of
                    None \<Rightarrow> x
                  | Some p \<Rightarrow>
                    (case p of
                       (a, b) \<Rightarrow> b))))"
nunchaku [expect = genuine]
oops

fun f1 where
"f1 x () = x"

lemma "x = f1 y u"
nunchaku [expect = genuine]
oops

fun f2 where
"f2 x _ True = x" |
"f2 _ y False = y"

lemma "x = f2 x y b"
nunchaku [expect = genuine]
oops

fun f3 where
"f3 (_, y) = y"

lemma "x = f3 p"
nunchaku [expect = genuine]
oops

fun f4 where
"f4 x 0 = x" |
"f4 _ (Suc n) = n"

lemma "x = f4 x n"
nunchaku [expect = genuine]
oops

fun f5 where
"f5 x None = x" |
"f5 _ (Some y) = y"

lemma "x = f5 x opt"
nunchaku [expect = genuine]
oops

fun f6 where
"f6 x [] = x" |
"f6 _ (y # ys) = y"

lemma "x = f6 x xs"
nunchaku [expect = genuine]
oops

fun f7 where
"f7 _ (y # Some (a, b) # zs) = b" |
"f7 x (y # None # zs) = x" |
"f7 x [y] = x" |
"f7 x [] = x"

lemma "x = f7 x xs"
nunchaku [expect = genuine]
oops

lemma "u = ()"
nunchaku [expect = none]
sorry

lemma "\<exists>y. (b::bool) = y"
nunchaku [expect = none]
sorry

lemma "\<exists>x y. p = (x, y)"
nunchaku [expect = none]
sorry

lemma "\<exists>x. n = Suc x"
nunchaku [expect = genuine]
oops

lemma "\<exists>y. x = Some y"
nunchaku [expect = genuine]
oops

lemma "\<exists>y ys. xs = y # ys"
nunchaku [expect = genuine]
oops

lemma "\<exists>y a b zs. x = y # Some (a, b) # zs"
nunchaku [expect = genuine]
oops

end
