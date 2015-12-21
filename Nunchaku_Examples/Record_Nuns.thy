(*  Title:      HOL/Nunchaku_Examples/Record_Nuns.thy
    Author:     Jasmin Blanchette, Inria Nancy, LORIA, MPII
    Copyright   2009-2015

Examples featuring Nunchaku applied to records.
*)

section {* Examples Featuring Nunchaku Applied to Records *}

theory Record_Nuns
imports "../Nunchaku"
begin

nunchaku_params [verbose, max_potential = 0, timeout = 240]

record point2d =
  xc :: nat
  yc :: nat

lemma "\<lparr>xc = x, yc = y\<rparr> = p\<lparr>xc := x, yc := y\<rparr>"
nunchaku [expect = none]
sorry

lemma "\<lparr>xc = x, yc = y\<rparr> = p\<lparr>xc := x\<rparr>"
nunchaku [expect = genuine]
oops

lemma "p\<lparr>xc := x, yc := y\<rparr> \<noteq> p"
nunchaku [expect = genuine]
oops

lemma "p\<lparr>xc := x, yc := y\<rparr> = p"
nunchaku [expect = genuine]
oops

record point3d = point2d +
  zc :: nat

lemma "\<lparr>xc = x, yc = y, zc = z\<rparr> = p\<lparr>xc := x, yc := y, zc := z\<rparr>"
nunchaku [expect = none]
sorry

lemma "\<lparr>xc = x, yc = y, zc = z\<rparr> = p\<lparr>xc := x\<rparr>"
nunchaku [expect = genuine]
oops

lemma "\<lparr>xc = x, yc = y, zc = z\<rparr> = p\<lparr>zc := z\<rparr>"
nunchaku [expect = genuine]
oops

lemma "p\<lparr>xc := x, yc := y, zc := z\<rparr> \<noteq> p"
nunchaku [expect = genuine]
oops

lemma "p\<lparr>xc := x, yc := y, zc := z\<rparr> = p"
nunchaku [expect = genuine]
oops

record point4d = point3d +
  wc :: nat

lemma "\<lparr>xc = x, yc = y, zc = z, wc = w\<rparr> = p\<lparr>xc := x, yc := y, zc := z, wc := w\<rparr>"
nunchaku [expect = none]
sorry

lemma "\<lparr>xc = x, yc = y, zc = z, wc = w\<rparr> = p\<lparr>xc := x\<rparr>"
nunchaku [expect = genuine]
oops

lemma "\<lparr>xc = x, yc = y, zc = z, wc = w\<rparr> = p\<lparr>zc := z\<rparr>"
nunchaku [expect = genuine]
oops

lemma "\<lparr>xc = x, yc = y, zc = z, wc = w\<rparr> = p\<lparr>wc := w\<rparr>"
nunchaku [expect = genuine]
oops

lemma "p\<lparr>xc := x, yc := y, zc := z, wc := w\<rparr> \<noteq> p"
nunchaku [expect = genuine]
oops

lemma "p\<lparr>xc := x, yc := y, zc := z, wc := w\<rparr> = p"
nunchaku [expect = genuine]
oops

end
