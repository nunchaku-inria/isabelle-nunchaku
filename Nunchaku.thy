theory Nunchaku
imports Main
keywords
  "nunchaku" :: diag and
  "nunchaku_params" :: thy_decl
begin

ML_file "Tools/nunchaku_util.ML"
ML_file "Tools/nunchaku_tool.ML"
ML_file "Tools/nunchaku_problem.ML"
ML_file "Tools/nunchaku_model.ML"
ML_file "Tools/nunchaku.ML"
ML_file "Tools/nunchaku_commands.ML"

lemma "a = b"
nunchaku

end
