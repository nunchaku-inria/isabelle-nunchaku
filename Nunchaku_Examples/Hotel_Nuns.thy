(*  Title:      HOL/Nunchaku_Examples/Hotel_Nuns.thy
    Author:     Jasmin Blanchette, Inria Nancy, LORIA, MPII
    Copyright   2010-2011

Nunchaku example based on Tobias Nipkow's hotel key card formalization.
*)

section {* Nunchaku Example Based on Tobias Nipkow's Hotel Key Card
          Formalization *}

theory Hotel_Nuns
imports Main
begin

nunchaku_params [verbose, max_potential = 0, sat_solver = MiniSat_JNI,
                timeout = 240]

typedecl guest
typedecl key
typedecl room

type_synonym keycurrk = initk, issued = range initk, cards = (\<lambda>g. {}),
  roomk = initk, isin = (\<lambda>r. {}), safe = (\<lambda>r. True)\<rparr> \<in> reach" |
check_in:
"\<lbrakk>s \<in> reach; k \<notin> issued s\<rbrakk> \<Longrightarrow>
 s\<lparr>currk := (currk s)(r := k), issued := issued s \<union> {k},
   cards := (cards s)(g := cards s g \<union> {(currk s r, k)}),
   owns :=  (owns s)(r := Some g), safe := (safe s)(r := False)\<rparr> \<in> reach" |
enter_room:
"\<lbrakk>s \<in> reach; (k,k') \<in> cards s g; roomk s r \<in> {k,k'}\<rbrakk> \<Longrightarrow>
 s\<lparr>isin := (isin s)(r := isin s r \<union> {g}),
   roomk := (roomk s)(r := k'),
   safe := (safe s)(r := owns s r = Some g \<and> isin s r = {} (* \<and> k' = currk s r *)
                         \<or> safe s r)\<rparr> \<in> reach" |
exit_room:
"\<lbrakk>s \<in> reach; g \<in> isin s r\<rbrakk> \<Longrightarrow> s\<lparr>isin := (isin s)(r := isin s r - {g})\<rparr> \<in> reach"

theorem safe: "s \<in> reach \<Longrightarrow> safe s r \<Longrightarrow> g \<in> isin s r \<Longrightarrow> owns s r = Some g"
nunchaku [card room = 1, card guest = 2, card "guest option" = 3,
         card key = 4, card state = 6, show_consts, format = 2,
         expect = genuine]
(* nunchaku [card room = 1, card guest = 2, expect = genuine] *) (* slow *)
oops

end
