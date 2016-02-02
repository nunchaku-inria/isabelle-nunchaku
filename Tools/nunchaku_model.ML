(*  Title:      HOL/Tools/Nunchaku/nunchaku_model.ML
    Author:     Jasmin Blanchette, Inria Nancy, LORIA, MPII
    Copyright   2015, 2016

Abstract syntax tree for Nunchaku models.
*)

signature NUNCHAKU_MODEL =
sig
  type ty = Nunchaku_Problem.ty
  type tm = Nunchaku_Problem.tm
  type name_pool = Nunchaku_Problem.name_pool

  type ty_entry = ty * tm list
  type tm_entry = tm * tm

  type nun_model =
    {type_model: ty_entry list,
     const_model: tm_entry list,
     skolem_model: tm_entry list}

  val str_of_nun_model: nun_model -> string

  val allocate_ugly: name_pool -> string * string -> string * name_pool

  val ugly_nun_model: name_pool -> nun_model -> nun_model
  val nun_model_of_str: string -> nun_model
end;

structure Nunchaku_Model : NUNCHAKU_MODEL =
struct

open Nunchaku_Problem;

type ty_entry = ty * tm list;
type tm_entry = tm * tm;

type nun_model =
  {type_model: ty_entry list,
   const_model: tm_entry list,
   skolem_model: tm_entry list};

fun str_of_ty_entry (ty, tms) =
  "type " ^ str_of_ty ty ^ " := {" ^ commas (map str_of_tm tms) ^ "}.";

fun str_of_tm_entry (tm, value) =
  "val " ^ str_of_tm tm ^ " := " ^ str_of_tm value ^ ".";

fun str_of_nun_model {type_model, const_model, skolem_model} =
  map str_of_ty_entry type_model @ "" :: map str_of_tm_entry const_model @ "" ::
  map str_of_tm_entry skolem_model
  |> cat_lines;

fun fold_map_ty_entry_idents f (ty, atoms) =
  fold_map_ty_idents f ty
  ##>> fold_map (fold_map_tm_idents f) atoms;

fun fold_map_tm_entry_idents f (tm, value) =
  fold_map_tm_idents f tm
  ##>> fold_map_tm_idents f value;

fun fold_map_nun_model_idents f {type_model, const_model, skolem_model} =
  fold_map (fold_map_ty_entry_idents f) type_model
  ##>> fold_map (fold_map_tm_entry_idents f) const_model
  ##>> fold_map (fold_map_tm_entry_idents f) skolem_model
  #>> (fn ((type_model, const_model), skolem_model) =>
    {type_model = type_model, const_model = const_model, skolem_model = skolem_model});

fun swap_name_pool ({nice_of_ugly, ugly_of_nice} : name_pool) =
  {nice_of_ugly = ugly_of_nice, ugly_of_nice = nice_of_ugly};

fun allocate_ugly pool (nice, ugly_sugg) =
  allocate_nice (swap_name_pool pool) (nice, ugly_sugg) ||> swap_name_pool;

fun ugly_ident nice (pool as {ugly_of_nice, ...}) =
  (case Symtab.lookup ugly_of_nice nice of
    NONE => allocate_ugly pool (nice, nice)
  | SOME ugly => (ugly, pool));

fun ugly_nun_model pool model =
  fst (fold_map_nun_model_idents ugly_ident model pool);

datatype token =
  Fun
| Type
| Val
| Atom of ident * int
| Ident of ident
| Colon
| Assign
| Unknown
| Equal
| Comma
| Period
| Left_Paren
| Right_Paren
| Left_Brace
| Right_Brace
| End_of_Stream
| Error;

fun maybe_ident s =
  if s = "fun" then
    Fun
  else if s = "type" then
    Type
  else if s = "val" then
    Val
  else
    (case first_field "__" s of
      SOME (pre, suf) =>
      if pre <> "" then
        (case Int.fromString suf of
          SOME j => Atom (ident_of_str (pre ^ "_"), j)
        | _ => Ident (ident_of_str s))
      else
        Ident (ident_of_str s)
    | NONE => Ident (ident_of_str s));

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
    else if c = #"," then
      (Comma, cs)
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

val tokenize =
  let
    fun toks cs =
      (case next_token cs of
        (End_of_Stream, []) => []
      | (tok, cs') => tok :: toks cs');
  in
    toks o String.explode
  end;

fun parse_tok tok = Scan.one (curry (op =) tok);

fun parse_enum sep scan = scan ::: Scan.repeat (sep |-- scan);

val parse_atom = Scan.some (try (fn Atom id_j => id_j));
val parse_ident = Scan.some (try (fn Ident id => id));

fun parse_ty tok =
  (parse_ident >> (rpair [] #> NType)) tok;

fun parse_tm tok =
  (parse_atom >> (fn (id, j) => NAtom (j, NType (id, [])))
   || parse_ident >> (fn id => NConst (id, [], nun_dummy_ty))
   || parse_tok Fun |-- parse_tm --| parse_tok Period -- parse_tm >> NAbs) tok;

datatype entry =
  Type_Entry of ty_entry
| Skolem_Entry of tm_entry
| Const_Entry of tm_entry;

val parse_entry =
  (parse_tok Type |-- parse_ty --| parse_tok Assign --| parse_tok Left_Brace --
       parse_enum (parse_tok Comma) parse_tm --| parse_tok Right_Brace
     >> Type_Entry
   || parse_tok Val |-- parse_tm --| parse_tok Assign -- parse_tm >> Const_Entry)
  --| parse_tok Period;

val parse_model =
  parse_ident (* "SAT" *) |-- parse_tok Colon |-- parse_tok Left_Brace |--
  Scan.repeat parse_entry --| parse_tok Right_Brace;

fun add_entry entry ({type_model, const_model, skolem_model} : nun_model) =
  (case entry of
    Type_Entry e =>
    {type_model = e :: type_model, const_model = const_model, skolem_model = skolem_model}
  | Skolem_Entry e =>
    {type_model = type_model, const_model = const_model, skolem_model = e :: skolem_model}
  | Const_Entry e =>
    {type_model = type_model, const_model = e :: const_model, skolem_model = skolem_model});

fun nun_model_of_str str =
  let val entries = fst (parse_model (tokenize str)) in
    fold_rev add_entry entries {type_model = [], const_model = [], skolem_model = []}
  end;

end;
