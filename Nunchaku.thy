theory Nunchaku
imports Main
keywords
  "nunchaku" :: diag and
  "nunchaku_params" :: thy_decl
begin

definition rmember :: "'a set \<Rightarrow> 'a \<Rightarrow> bool" where
  "rmember A x \<longleftrightarrow> x \<in> A"

ML \<open>
datatype token =
  Fun
| Val
| Ident of string
| Colon
| Assign
| Unknown
| Equal
| Period
| Left_Paren
| Right_Paren
| Left_Brace
| Right_Brace
| End_of_Stream
| Error;

fun maybe_ident s =
  if s = "fun" then Fun
  else if s = "val" then Val
  else Ident s;

fun is_ident_char s =
  Char.isAlphaNum s orelse s = #"_" orelse s = #"/";

fun next_token [] = (End_of_Stream, [])
  | next_token (c :: cs) =
    if Char.isSpace c then
      next_token cs
    else if Char.isAlpha c then
      (case find_index (not o is_ident_char) cs of
        ~1 => (maybe_ident (Char.toString c), [])
      | n => chop n cs |>> (cons c #> String.implode #> maybe_ident))
    else if c = #":" then
      if is_prefix (op =) [#"="] cs then (Assign, tl cs)
      else (Colon, cs)
    else if c = #"?" then
      if is_prefix (op =) [#"_", #"_"] cs then (Unknown, drop 2 cs)
      else (Error, [])
    else if c = #"=" then
      (Equal, cs)
    else if c = #"." then
      (Period, cs)
    else if c = #"(" then
      (Left_Paren, cs)
    else if c = #")" then
      (Right_Paren, cs)
    else if c = #"{" then
      (Left_Brace, cs)
    else if c = #"}" then
      (Right_Brace, cs)
    else
      (Error, []);
\<close>

ML {*
val tokenize =
  let
    fun toks cs =
      (case next_token cs of
        (End_of_Stream, []) => []
      | (tok, cs') => tok :: toks cs');
  in
    toks o String.explode
  end;
*}

ML {*
val toks =
  tokenize "SAT: {\n  val n := zero.\n  val odd := fun v_1/69. ?__. val even := fun v_1/71. if v_1/71 = zero then true  else ?__."
val toks =
  tokenize "SAT: {\n  X }\n \n"
*}

ML {*
open Nunchaku_Problem;
*}

ML {*
fun parse_token tok = Scan.one (curry (op =) tok);

val parse_ident = Scan.one (fn Ident _ => true | _ => false);

fun parse_term tok =
  (parse_token Fun |-- parse_term --| parse_token Period -- parse_term >> NAbs) tok;

val parse_val_entry = parse_token Val |-- parse_ident --| parse_token Assign -- parse_term --| parse_token Period;

val parse_model = parse_token (Ident "SAT") |-- parse_token Colon |-- parse_token Left_Brace |--
  Scan.repeat parse_val_entry  --| parse_token Right_Brace;
*}

ML {*
parse_model toks
*}





















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

hide_const (open) rmember

lemma "hd xs = [x]"
nunchaku
oops

end
