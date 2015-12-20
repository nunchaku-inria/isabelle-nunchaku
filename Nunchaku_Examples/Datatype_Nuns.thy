(*  Title:      HOL/Nunchaku_Examples/Datatype_Nuns.thy
    Author:     Jasmin Blanchette, Inria Nancy, LORIA, MPII
    Copyright   2009-2015

Examples featuring Nunchaku applied to datatypes.
*)

section {* Examples Featuring Nunchaku Applied to Datatypes *}

theory Datatype_Nuns
imports Main
begin

nunchaku_params [verbose, max_potential = 0, timeout = 240]

primrec rot where
"rot Nibble0 = Nibble1" | "rot Nibble1 = Nibble2" | "rot Nibble2 = Nibble3" |
"rot Nibble3 = Nibble4" | "rot Nibble4 = Nibble5" | "rot Nibble5 = Nibble6" |
"rot Nibble6 = Nibble7" | "rot Nibble7 = Nibble8" | "rot Nibble8 = Nibble9" |
"rot Nibble9 = NibbleA" | "rot NibbleA = NibbleB" | "rot NibbleB = NibbleC" |
"rot NibbleC = NibbleD" | "rot NibbleD = NibbleE" | "rot NibbleE = NibbleF" |
"rot NibbleF = Nibble0"

lemma "rot n \<noteq> n"
nunchaku [card = 1-8,16, verbose, expect = none]
sorry

lemma "rot Nibble2 \<noteq> Nibble3"
nunchaku [card = 1, expect = none]
nunchaku [card = 2, max Nibble4 = 0, expect = genuine]
nunchaku [card = 2, max Nibble2 = 0, expect = none]
oops

lemma "(rot ^^ 15) n \<noteq> n"
nunchaku [card = 17, expect = none]
sorry

lemma "(rot ^^ 15) n = n"
nunchaku [card = 17, expect = genuine]
oops

lemma "(rot ^^ 16) n = n"
nunchaku [card = 17, expect = none]
oops

datatype ('a, 'b) pd = Pd "'a \<times> 'b"

fun fs where
"fs (Pd (a, _)) = a"

fun sn where
"sn (Pd (_, b)) = b"

lemma "fs (Pd p) = fst p"
nunchaku [card = 12, expect = none]
sorry

lemma "fs (Pd p) = snd p"
nunchaku [expect = genuine]
oops

lemma "sn (Pd p) = snd p"
nunchaku [card = 12, expect = none]
sorry

lemma "sn (Pd p) = fst p"
nunchaku [expect = genuine]
oops

lemma "fs (Pd ((a, b), (c, d))) = (a, b)"
nunchaku [expect = none]
sorry

lemma "fs (Pd ((a, b), (c, d))) = (c, d)"
nunchaku [expect = genuine]
oops

datatype ('a, 'b) fn = Fn "'a \<Rightarrow> 'b"

fun app where
"app (Fn f) x = f x"

lemma "app (Fn g) y = g y"
nunchaku [expect = none]
sorry

lemma "app (Fn g) y = g' y"
nunchaku [expect = genuine]
oops

lemma "app (Fn g) y = g y'"
nunchaku [expect = genuine]
oops

end
