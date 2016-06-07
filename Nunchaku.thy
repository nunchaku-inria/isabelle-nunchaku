theory Nunchaku
imports Main
keywords
  "nunchaku" :: diag and
  "nunchaku_params" :: thy_decl
begin

definition The_unsafe :: "('a \<Rightarrow> bool) \<Rightarrow> 'a" where
  "The_unsafe = The"

definition unreachable :: 'a where
  "unreachable = The_unsafe (\<lambda>_. False)"

definition rmember :: "'a set \<Rightarrow> 'a \<Rightarrow> bool" where
  "rmember A x \<longleftrightarrow> x \<in> A"

ML_file "Tools/nunchaku_util.ML"
ML_file "Tools/nunchaku_collect.ML"
ML_file "Tools/nunchaku_problem.ML"
ML_file "Tools/nunchaku_translate.ML"
ML_file "Tools/nunchaku_model.ML"
ML_file "Tools/nunchaku_reconstruct.ML"
ML_file "Tools/nunchaku_display.ML"
ML_file "Tools/nunchaku_tool.ML"
ML_file "Tools/nunchaku.ML"
ML_file "Tools/nunchaku_commands.ML"

codatatype 'a llist = LNil | LCons 'a "'a llist"

(*
lemma "xs = LCons a ys \<Longrightarrow> ys = LCons b xs \<Longrightarrow> xs = ys"
nunchaku[overlord, debug]
*)

(*
(* FIXME: whack with "unreachable" is not a good idea *)
lemma "rev xs = xs \<or> xs = ys"
nunchaku[satisfy, whack rev, debug]
*)

hide_const (open) The_unsafe unreachable rmember

end
