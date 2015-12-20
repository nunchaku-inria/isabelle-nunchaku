(*  Title:      HOL/Nunchaku_Examples/Induct_Nuns.thy
    Author:     Jasmin Blanchette, Inria Nancy, LORIA, MPII
    Copyright   2009-2015

Examples featuring Nunchaku applied to (co)inductive definitions.
*)

section {* Examples Featuring Nunchaku Applied to (Co)inductive Definitions *}

theory Induct_Nuns
imports "../Nunchaku"
begin

nunchaku_params [verbose, timeout = 240]

inductive p1 :: "nat \<Rightarrow> bool" where
  "p1 0"
| "p1 n \<Longrightarrow> p1 (n + 2)"

coinductive q1 :: "nat \<Rightarrow> bool" where
  "q1 0"
| "q1 n \<Longrightarrow> q1 (n + 2)"

lemma "p1 = q1"
nunchaku [expect = none]
nunchaku [wf, expect = none]
nunchaku [non_wf, expect = none]
oops

lemma "p1 \<noteq> q1"
nunchaku [expect = potential]
nunchaku [wf, expect = potential]
nunchaku [non_wf, expect = potential]
oops

lemma "p1 (n - 2) \<Longrightarrow> p1 n"
nunchaku [expect = genuine]
nunchaku [non_wf, expect = genuine]
oops

lemma "q1 (n - 2) \<Longrightarrow> q1 n"
nunchaku [expect = genuine]
nunchaku [non_wf, expect = genuine]
oops

inductive p2 :: "nat \<Rightarrow> bool" where
  "p2 n \<Longrightarrow> p2 n"

coinductive q2 :: "nat \<Rightarrow> bool" where
  "q2 n \<Longrightarrow> q2 n"

lemma "p2 = bot"
nunchaku [expect = none]
sorry

lemma "q2 = bot"
nunchaku [expect = genuine]
nunchaku [wf, expect = quasi_genuine]
oops

lemma "p2 = top"
nunchaku [expect = genuine]
oops

lemma "q2 = top"
nunchaku [expect = none]
nunchaku [wf, expect = quasi_genuine]
sorry

lemma "p2 = q2"
nunchaku [expect = genuine]
oops

lemma "p2 n"
nunchaku [expect = genuine]
oops

lemma "q2 n"
nunchaku [expect = none]
sorry

lemma "\<not> p2 n"
nunchaku [expect = none]
sorry

lemma "\<not> q2 n"
nunchaku [expect = genuine]
oops

inductive p3 and p4 where
  "p3 0"
| "p3 n \<Longrightarrow> p4 (Suc n)"
| "p4 n \<Longrightarrow> p3 (Suc n)"

coinductive q3 and q4 where
  "q3 0"
| "q3 n \<Longrightarrow> q4 (Suc n)"
| "q4 n \<Longrightarrow> q3 (Suc n)"

lemma "p3 = q3"
nunchaku [expect = none]
nunchaku [non_wf, expect = none]
sorry

lemma "p4 = q4"
nunchaku [expect = none]
nunchaku [non_wf, expect = none]
sorry

lemma "p3 = top - p4"
nunchaku [expect = none]
nunchaku [non_wf, expect = none]
sorry

lemma "q3 = top - q4"
nunchaku [expect = none]
nunchaku [non_wf, expect = none]
sorry

lemma "inf p3 q4 \<noteq> bot"
nunchaku [expect = potential]
nunchaku [non_wf, expect = potential]
sorry

lemma "inf q3 p4 \<noteq> bot"
nunchaku [expect = potential]
nunchaku [non_wf, expect = potential]
sorry

lemma "sup p3 q4 \<noteq> top"
nunchaku [expect = potential]
nunchaku [non_wf, expect = potential]
sorry

lemma "sup q3 p4 \<noteq> top"
nunchaku [expect = potential]
nunchaku [non_wf, expect = potential]
sorry

end
