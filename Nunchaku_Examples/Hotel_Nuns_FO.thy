(*  Title:      HOL/Nunchaku_Examples/Hotel_Nuns_FO.thy
    Author:     Jasmin Blanchette, Inria Nancy, LORIA, MPII
    Copyright   2010-2011

Nunchaku example based on Tobias Nipkow's hotel key card formalization.
*)

section {* Nunchaku Example Based on Tobias Nipkow's Hotel Key Card
          Formalization *}

theory Hotel_Nuns_FO
imports "../Nunchaku"
begin

nunchaku_params [verbose, max_potential = 0, timeout = 240]

(*
typedecl guest
typedecl key
typedecl room

typedecl card
typedecl state
*)

datatype room = R1
datatype guest = G1 | G2
datatype key = K1 | K2 | K3 | K4
datatype card = C1 | C2 | C3 | C4 | C5
datatype state = S1 | S2 | S3 | S4 | S5 | S6

(*
nitpick [card room = 1, card guest = 2, card "guest option" = 3,
         card key = 4, card state = 6,
*)


consts
  fst :: "card \<Rightarrow> key"
  snd :: "card \<Rightarrow> key"

consts
  owns :: "state \<Rightarrow> room \<Rightarrow> guest option"
  currk :: "state \<Rightarrow> room \<Rightarrow> key"
  issued :: "state \<Rightarrow> key \<Rightarrow> bool"
  cards :: "state \<Rightarrow> guest \<Rightarrow> card \<Rightarrow> bool"
  roomk :: "state \<Rightarrow> room \<Rightarrow> key"
  isin :: "state \<Rightarrow> room \<Rightarrow> guest \<Rightarrow> bool"
  safe :: "state \<Rightarrow> room \<Rightarrow> bool"

definition "next" where
  "next s s' =
   ((s = S1 \<and> s' = S2) \<or>
    (s = S2 \<and> s' = S3) \<or>
    (s = S3 \<and> s' = S4) \<or>
    (s = S4 \<and> s' = S5) \<or>
    (s = S5 \<and> s' = S6))"

consts buggy :: bool

inductive reach :: "state \<Rightarrow> bool" where
init:
  "s = S1 \<Longrightarrow>
   (\<forall>r. owns s r = None) \<Longrightarrow>
   (\<forall>r. \<forall>r'. currk s r = currk s r' \<longrightarrow> r = r') \<Longrightarrow>
   (\<forall>k. issued s k \<longleftrightarrow> (\<exists>r. currk s r = k)) \<Longrightarrow>
   (\<forall>g c. \<not> cards s g c) \<Longrightarrow>
   (\<forall>r. roomk s r = currk s r) \<Longrightarrow>
   (\<forall>r g. \<not> isin s r g) \<Longrightarrow>
   (\<forall>r. safe s r) \<Longrightarrow> reach s"
| check_in:
  "next s s' \<Longrightarrow>
   reach s \<Longrightarrow>
   \<not> issued s K \<Longrightarrow>
   fst C = currk s R \<Longrightarrow>
   snd C = K \<Longrightarrow>
   (\<forall>r. owns s' r = (if r = R then Some G else owns s r)) \<Longrightarrow>
   (\<forall>r. currk s' r = (if r = R then K else currk s r)) \<Longrightarrow>
   (\<forall>k. issued s' k = (k = K \<or> issued s k)) \<Longrightarrow>
   (\<forall>g c. cards s' g c = ((g = G \<and> c = C) \<or> cards s g c)) \<Longrightarrow>
   (\<forall>r. roomk s' r = roomk s r) \<Longrightarrow>
   (\<forall>r g. isin s' r g = isin s r g) \<Longrightarrow>
   (\<forall>r. safe s' r = (r \<noteq> R \<and> safe s r)) \<Longrightarrow>
   reach s'"
| enter_room:
  "next s s' \<Longrightarrow>
   reach s \<Longrightarrow>
   cards s G C \<Longrightarrow>
   fst C = K \<Longrightarrow>
   snd C = K' \<Longrightarrow>
   roomk s r = K \<or> roomk s r = K' \<Longrightarrow>
   (\<forall>r. owns s' r = owns s r) \<Longrightarrow>
   (\<forall>r. currk s' r = currk s r) \<Longrightarrow>
   (\<forall>k. issued s' k = issued s k) \<Longrightarrow>
   (\<forall>g c. cards s' g c = cards s g c) \<Longrightarrow>
   (\<forall>r. roomk s' r = (if r = R then K' else roomk s r)) \<Longrightarrow>
   (\<forall>r g. isin s' r g = ((r = R \<and> g = G) \<or> isin s r g)) \<Longrightarrow>
   (\<forall>r. safe s' r = (if r = R then (owns s R = Some G \<and> (\<forall>r g. \<not> isin s r g) \<and> (buggy \<or> K' = currk s R)) \<or> safe s R
      else safe s r)) \<Longrightarrow>
   reach s'"
| exit_room:
  "next s s' \<Longrightarrow>
   reach s \<Longrightarrow>
   isin s R G \<Longrightarrow>
   (\<forall>r. owns s' r = owns s r) \<Longrightarrow>
   (\<forall>r. currk s' r = currk s r) \<Longrightarrow>
   (\<forall>k. issued s' k = issued s k) \<Longrightarrow>
   (\<forall>g c. cards s' g c = cards s g c) \<Longrightarrow>
   (\<forall>r. roomk s' r = roomk s r) \<Longrightarrow>
   (\<forall>r g. isin s' r g = ((r \<noteq> R \<or> g \<noteq> G) \<and> isin s r g)) \<Longrightarrow>
   (\<forall>r. safe s' r = safe s r) \<Longrightarrow>
   reach s'"

axiomatization reach' where
reach': "reach' a \<Longrightarrow>
((\<exists>s. a = s \<and>
      s = S1 \<and>
      (\<forall>r. owns s r = None) \<and>
      (\<forall>r r'. currk s r = currk s r' \<longrightarrow> r = r') \<and>
      (\<forall>k. issued s k = (\<exists>r. currk s r = k)) \<and>
      (\<forall>g c. \<not> cards s g c) \<and> (\<forall>r. roomk s r = currk s r) \<and> (\<forall>r g. \<not> isin s r g) \<and> (\<forall>r. safe s r)) \<or>
 (\<exists>s s' K C R G.
     a = s' \<and>
     next s s' \<and>
     reach' s \<and>
     \<not> issued s K \<and>
     Hotel_Nuns_FO.fst C = currk s R \<and>
     Hotel_Nuns_FO.snd C = K \<and>
     (\<forall>r. owns s' r = (if r = R then Some G else owns s r)) \<and>
     (\<forall>r. currk s' r = (if r = R then K else currk s r)) \<and>
     (\<forall>k. issued s' k = (k = K \<or> issued s k)) \<and>
     (\<forall>g c. cards s' g c = (g = G \<and> c = C \<or> cards s g c)) \<and>
     (\<forall>r. roomk s' r = roomk s r) \<and>
     (\<forall>r g. isin s' r g = isin s r g) \<and> (\<forall>r. safe s' r = (r \<noteq> R \<and> safe s r))) \<or>
 (\<exists>s s' G C K K' r R.
     a = s' \<and>
     next s s' \<and>
     reach' s \<and>
     cards s G C \<and>
     Hotel_Nuns_FO.fst C = K \<and>
     Hotel_Nuns_FO.snd C = K' \<and>
     (roomk s r = K \<or> roomk s r = K') \<and>
     (\<forall>r. owns s' r = owns s r) \<and>
     (\<forall>r. currk s' r = currk s r) \<and>
     (\<forall>k. issued s' k = issued s k) \<and>
     (\<forall>g c. cards s' g c = cards s g c) \<and>
     (\<forall>r. roomk s' r = (if r = R then K' else roomk s r)) \<and>
     (\<forall>r g. isin s' r g = (r = R \<and> g = G \<or> isin s r g)) \<and>
     (\<forall>r. safe s' r =
          (if r = R then owns s R = Some G \<and> (\<forall>r g. \<not> isin s r g) \<and> (buggy \<or> K' = currk s R) \<or> safe s R
           else safe s r))) \<or>
 (\<exists>s s' R G.
     a = s' \<and>
     next s s' \<and>
     reach' s \<and>
     isin s R G \<and>
     (\<forall>r. owns s' r = owns s r) \<and>
     (\<forall>r. currk s' r = currk s r) \<and>
     (\<forall>k. issued s' k = issued s k) \<and>
     (\<forall>g c. cards s' g c = cards s g c) \<and>
     (\<forall>r. roomk s' r = roomk s r) \<and>
     (\<forall>r g. isin s' r g = ((r \<noteq> R \<or> g \<noteq> G) \<and> isin s r g)) \<and> (\<forall>r. safe s' r = safe s r)))"

theorem safe: "buggy \<Longrightarrow> reach' s \<Longrightarrow> safe s r \<Longrightarrow> isin s r g \<Longrightarrow> owns s r = Some g"
nunchaku [wf, overlord, timeout = 60]
(* nitpick[card = 100] *)
(* nitpick[wf, card = 100, debug] *)
(* nitpick[card = 10, datatype_sym_break = 0, kodkod_sym_break = 0, timeout = 300] *)
(*
*)
(* nitpick[card = 10] *)

oops

(*
inductive_set reach :: "state set" where
exit_room:

theorem safe: "s \<in> reach \<Longrightarrow> safe s r \<Longrightarrow> g \<in> isin s r \<Longrightarrow> owns s r = Some g"
nunchaku [expect = genuine]
oops
*)

end
