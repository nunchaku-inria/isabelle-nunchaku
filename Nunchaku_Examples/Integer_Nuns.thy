(*  Title:      HOL/Nunchaku_Examples/Integer_Nuns.thy
    Author:     Jasmin Blanchette, Inria Nancy, LORIA, MPII
    Copyright   2009-2012

Examples featuring Nunchaku applied to natural numbers and integers.
*)

section {* Examples Featuring Nunchaku Applied to Natural Numbers and Integers *}

theory Integer_Nuns
imports Main
begin

nunchaku_params [verbose, bits = 1,2,3,4,6,
                timeout = 240]

lemma "Suc x = x + 1"
nunchaku [unary_ints, expect = none]
nunchaku [binary_ints, expect = none]
sorry

lemma "x < Suc x"
nunchaku [unary_ints, expect = none]
nunchaku [binary_ints, expect = none]
sorry

lemma "x + y \<ge> (x::nat)"
nunchaku [unary_ints, expect = none]
nunchaku [binary_ints, expect = none]
sorry

lemma "y \<noteq> 0 \<Longrightarrow> x + y > (x::nat)"
nunchaku [unary_ints, expect = none]
nunchaku [binary_ints, expect = none]
sorry

lemma "x + y = y + (x::nat)"
nunchaku [unary_ints, expect = none]
nunchaku [binary_ints, expect = none]
sorry

lemma "x > y \<Longrightarrow> x - y \<noteq> (0::nat)"
nunchaku [unary_ints, expect = none]
nunchaku [binary_ints, expect = none]
sorry

lemma "x \<le> y \<Longrightarrow> x - y = (0::nat)"
nunchaku [unary_ints, expect = none]
nunchaku [binary_ints, expect = none]
sorry

lemma "x - (0::nat) = x"
nunchaku [unary_ints, expect = none]
nunchaku [binary_ints, expect = none]
sorry

lemma "\<lbrakk>x \<noteq> 0; y \<noteq> 0\<rbrakk> \<Longrightarrow> x * y \<noteq> (0::nat)"
nunchaku [unary_ints, expect = none]
nunchaku [binary_ints, expect = none]
sorry

lemma "0 * y = (0::nat)"
nunchaku [unary_ints, expect = none]
nunchaku [binary_ints, expect = none]
sorry

lemma "y * 0 = (0::nat)"
nunchaku [unary_ints, expect = none]
nunchaku [binary_ints, expect = none]
sorry

lemma "\<lbrakk>x \<noteq> 0; y \<noteq> 0\<rbrakk> \<Longrightarrow> x * y \<ge> (x::nat)"
nunchaku [unary_ints, expect = none]
nunchaku [binary_ints, expect = none]
sorry

lemma "\<lbrakk>x \<noteq> 0; y \<noteq> 0\<rbrakk> \<Longrightarrow> x * y \<ge> (y::nat)"
nunchaku [unary_ints, expect = none]
nunchaku [binary_ints, expect = none]
sorry

lemma "x * y div y = (x::nat)"
nunchaku [unary_ints, expect = genuine]
nunchaku [binary_ints, expect = genuine]
oops

lemma "y \<noteq> 0 \<Longrightarrow> x * y div y = (x::nat)"
nunchaku [unary_ints, expect = none]
nunchaku [binary_ints, expect = none]
sorry

lemma "5 * 55 < (260::nat)"
nunchaku [unary_ints, expect = none]
nunchaku [binary_ints, expect = none]
nunchaku [binary_ints, bits = 9, expect = genuine]
oops

lemma "nat (of_nat n) = n"
nunchaku [unary_ints, expect = none]
nunchaku [binary_ints, expect = none]
sorry

lemma "x + y \<ge> (x::int)"
nunchaku [unary_ints, expect = genuine]
nunchaku [binary_ints, expect = genuine]
oops

lemma "\<lbrakk>x \<ge> 0; y \<ge> 0\<rbrakk> \<Longrightarrow> x + y \<ge> (0::int)"
nunchaku [unary_ints, expect = none]
nunchaku [binary_ints, expect = none]
sorry

lemma "y \<ge> 0 \<Longrightarrow> x + y \<ge> (x::int)"
nunchaku [unary_ints, expect = none]
nunchaku [binary_ints, expect = none]
sorry

lemma "x \<ge> 0 \<Longrightarrow> x + y \<ge> (y::int)"
nunchaku [unary_ints, expect = none]
nunchaku [binary_ints, expect = none]
sorry

lemma "x \<ge> 0 \<Longrightarrow> x + y \<ge> (x::int)"
nunchaku [unary_ints, expect = genuine]
nunchaku [binary_ints, expect = genuine]
oops

lemma "\<lbrakk>x \<le> 0; y \<le> 0\<rbrakk> \<Longrightarrow> x + y \<le> (0::int)"
nunchaku [unary_ints, expect = none]
nunchaku [binary_ints, expect = none]
sorry

lemma "y \<noteq> 0 \<Longrightarrow> x + y > (x::int)"
nunchaku [unary_ints, expect = genuine]
nunchaku [binary_ints, expect = genuine]
oops

lemma "x + y = y + (x::int)"
nunchaku [unary_ints, expect = none]
nunchaku [binary_ints, expect = none]
sorry

lemma "x > y \<Longrightarrow> x - y \<noteq> (0::int)"
nunchaku [unary_ints, expect = none]
nunchaku [binary_ints, expect = none]
sorry

lemma "x \<le> y \<Longrightarrow> x - y = (0::int)"
nunchaku [unary_ints, expect = genuine]
nunchaku [binary_ints, expect = genuine]
oops

lemma "x - (0::int) = x"
nunchaku [unary_ints, expect = none]
nunchaku [binary_ints, expect = none]
sorry

lemma "\<lbrakk>x \<noteq> 0; y \<noteq> 0\<rbrakk> \<Longrightarrow> x * y \<noteq> (0::int)"
nunchaku [unary_ints, expect = none]
nunchaku [binary_ints, expect = none]
sorry

lemma "0 * y = (0::int)"
nunchaku [unary_ints, expect = none]
nunchaku [binary_ints, expect = none]
sorry

lemma "y * 0 = (0::int)"
nunchaku [unary_ints, expect = none]
nunchaku [binary_ints, expect = none]
sorry

lemma "\<lbrakk>x \<noteq> 0; y \<noteq> 0\<rbrakk> \<Longrightarrow> x * y \<ge> (x::int)"
nunchaku [unary_ints, expect = genuine]
nunchaku [binary_ints, expect = genuine]
oops

lemma "\<lbrakk>x \<noteq> 0; y \<noteq> 0\<rbrakk> \<Longrightarrow> x * y \<ge> (y::int)"
nunchaku [unary_ints, expect = genuine]
nunchaku [binary_ints, expect = genuine]
oops

lemma "x * y div y = (x::int)"
nunchaku [unary_ints, expect = genuine]
nunchaku [binary_ints, expect = genuine]
oops

lemma "y \<noteq> 0 \<Longrightarrow> x * y div y = (x::int)"
nunchaku [unary_ints, expect = none]
nunchaku [binary_ints, bits = 1-4, expect = none]
sorry

lemma "(x * y < 0) \<longleftrightarrow> (x > 0 \<and> y < 0) \<or> (x < 0 \<and> y > (0::int))"
nunchaku [unary_ints, expect = none]
nunchaku [binary_ints, expect = none]
sorry

lemma "-5 * 55 > (-260::int)"
nunchaku [unary_ints, expect = none]
nunchaku [binary_ints, expect = none]
nunchaku [binary_ints, bits = 9, expect = genuine]
oops

lemma "nat (of_nat n) = n"
nunchaku [unary_ints, expect = none]
nunchaku [binary_ints, expect = none]
sorry

datatype tree = Null | Node nat tree tree

primrec labels where
"labels Null = {}" |
"labels (Node x t u) = {x} \<union> labels t \<union> labels u"

lemma "labels (Node x t u) \<noteq> labels (Node y v w)"
nunchaku [expect = potential] (* unfortunate *)
oops

lemma "labels (Node x t u) \<noteq> {}"
nunchaku [expect = none]
oops

lemma "card (labels t) > 0"
nunchaku [expect = potential] (* unfortunate *)
oops

lemma "(\<Sum>n \<in> labels t. n + 2) \<ge> 2"
nunchaku [expect = potential] (* unfortunate *)
oops

lemma "t \<noteq> Null \<Longrightarrow> (\<Sum>n \<in> labels t. n + 2) \<ge> 2"
nunchaku [expect = potential] (* unfortunate *)
sorry

lemma "(\<Sum>i \<in> labels (Node x t u). f i::nat) = f x + (\<Sum>i \<in> labels t. f i) + (\<Sum>i \<in> labels u. f i)"
nunchaku [expect = potential] (* unfortunate *)
oops

end
