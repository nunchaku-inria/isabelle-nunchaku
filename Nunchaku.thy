theory Nunchaku
imports Main
keywords
  "nunchaku" :: diag and
  "nunchaku_params" :: thy_decl
begin

ML_file "Tools/nunchaku_util.ML"
ML_file "Tools/nunchaku_collect.ML"
ML_file "Tools/nunchaku_problem.ML"
ML_file "Tools/nunchaku_tool.ML"
ML_file "Tools/nunchaku_translate.ML"
ML_file "Tools/nunchaku_model.ML"
ML_file "Tools/nunchaku.ML"
ML_file "Tools/nunchaku_commands.ML"

ML {*
Spec_Rules.retrieve @{context} @{term Collect}
*}

lemma "p {x. q x}"
nunchaku[overlord]



(*
declare [[ML_exception_trace]]

lemma "rev xs = xs \<and> rev ys = ys"
nunchaku[debug]
oops

lemma "rev xs = xs"
nunchaku[overlord]
oops

lemma "[x] @ ys = x # ys"
nunchaku[overlord]
oops
*)

end
