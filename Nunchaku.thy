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


(*
inductive even and odd where
  "even 0"
| "even m \<Longrightarrow> odd (Suc m)"
| "even n \<Longrightarrow> even (Suc (Suc n))"

lemma "even n"
nunchaku
oops

lemma "rev xs = ys \<and> rev ys = xs"
nunchaku[debug,overlord,satisfy]
oops
*)

(*
declare [[ML_exception_trace]]

oops

lemma "rev xs = xs"
nunchaku[overlord]
oops

lemma "[x] @ ys = x # ys"
nunchaku[overlord]
oops
*)

end
