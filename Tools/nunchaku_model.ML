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
  val nun_model_of_str: string -> nun_model option
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

val nun_SAT = str_of_ident "SAT";

val napps = Library.foldl NApp;

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
  Ident of ident
| Symbol of ident
| Atom of ident * int
| End_of_Stream;

fun ident_or_atom s =
  (case first_field "__" s of
    SOME (pre, suf) =>
    if pre <> "" then
      (case Int.fromString suf of
        SOME j => Atom (ident_of_str (pre ^ "_"), j)
      | _ => Ident (ident_of_str s))
    else
      Ident (ident_of_str s)
  | NONE => Ident (ident_of_str s));

fun is_alnum_etc_char c = Char.isAlphaNum c orelse c = #"_" orelse c = #"/";

fun next_token [] = (End_of_Stream, [])
  | next_token (c :: cs) =
    if Char.isSpace c then
      next_token cs
    else if Char.isAlpha c then
      let val n = find_index (not o is_alnum_etc_char) cs in
        (if n = ~1 then (cs, []) else chop n cs) |>> (cons c #> String.implode #> ident_or_atom)
      end
    else if c = #"?" andalso is_prefix (op =) [#"_", #"_"] cs then
      (Symbol (ident_of_str nun_unknown), drop 2 cs)
    else if c = #":" andalso is_prefix (op =) [#"="] cs then
      (Symbol (ident_of_str nun_assign), tl cs)
    else
      (Symbol (ident_of_str (String.str c)), cs);

val tokenize =
  let
    fun toks cs =
      (case next_token cs of
        (End_of_Stream, []) => []
      | (tok, cs') => tok :: toks cs');
  in
    toks o String.explode
  end;

fun parse_enum sep scan = scan ::: Scan.repeat (sep |-- scan);

fun parse_tok tok = Scan.one (curry (op =) tok);

val parse_ident = Scan.some (try (fn Ident id => id));
val parse_id = parse_tok o Ident;
val parse_sym = parse_tok o Symbol;
val parse_atom = Scan.some (try (fn Atom id_j => id_j));

fun parse_ty toks =
  (parse_ident >> (rpair [] #> NType)) toks;

fun parse_tm toks =
  (parse_id nun_fun |-- parse_tm --| parse_sym nun_dot -- parse_tm >> NAbs
   || parse_comb -- Scan.option (parse_sym nun_equals |-- parse_comb)
      >> (fn (tm, NONE) => tm
        | (lhs, SOME rhs) => napps (NConst (nun_equals, [], nun_dummy_ty), [lhs, rhs]))) toks
and parse_comb toks =
  (parse_arg -- Scan.repeat (Scan.unless (parse_id nun_then || parse_id nun_with) parse_arg)
   >> napps) toks
and parse_arg toks =
  (parse_id nun_if |-- parse_tm --| parse_id nun_then -- parse_tm --| parse_id nun_else -- parse_tm
     >> (fn ((cond, th), el) => napps (NConst (nun_if, [], ty_of th), [cond, th, el]))
   || parse_ident >> (fn id => NConst (id, [], nun_dummy_ty))
   || parse_sym nun_lparen |-- parse_tm --| parse_sym nun_rparen
   || parse_atom >> (fn (id, j) => NAtom (j, NType (id, [])))) toks;

datatype entry =
  Type_Entry of ty_entry
| Skolem_Entry of tm_entry
| Const_Entry of tm_entry;

val parse_entry =
  (parse_id nun_type |-- parse_ty --| parse_sym nun_assign --| parse_sym nun_lbrace --
       parse_enum (parse_sym nun_comma) parse_tm --| parse_sym nun_rbrace
     >> Type_Entry
   || parse_id nun_val |-- parse_tm --| parse_sym nun_assign -- parse_tm >> Const_Entry)
  --| parse_sym nun_dot;

val parse_model =
  parse_id nun_SAT |-- parse_sym nun_colon |-- parse_sym nun_lbrace |-- Scan.repeat parse_entry
  --| parse_sym nun_rbrace;

fun add_entry entry ({type_model, const_model, skolem_model} : nun_model) =
  (case entry of
    Type_Entry e =>
    {type_model = e :: type_model, const_model = const_model, skolem_model = skolem_model}
  | Skolem_Entry e =>
    {type_model = type_model, const_model = const_model, skolem_model = e :: skolem_model}
  | Const_Entry e =>
    {type_model = type_model, const_model = e :: const_model, skolem_model = skolem_model});

fun nun_model_of_str str =
  let val str = "SAT:{val f_ := fun f_. f_.}"
val _ = tracing (@{make_string} (drop 6 (tokenize str)))
in
  try (parse_model o tokenize) str
  |> Option.map (fn (entries, _) =>
    fold_rev add_entry entries {type_model = [], const_model = [], skolem_model = []})
end;

end;
