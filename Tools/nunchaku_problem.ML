(*  Title:      HOL/Tools/Nunchaku/nunchaku_problem.ML
    Author:     Jasmin Blanchette, Inria Nancy, LORIA, MPII
    Copyright   2015

Abstract syntax tree for Nunchaku problems.
*)

signature NUNCHAKU_PROBLEM =
sig
  type ident

  datatype ty =
    NType of ident * ty list
  | NTVar of ident

  datatype tm =
    NConst of ident * ty list * ty
  | NVar of ident * ty
  | NAbs of tm * tm
  | NApp of tm * tm

  type nun_ctr_spec =
    {ctr_id: ident,
     arg_tys: ty list}

  type nun_co_data_spec =
    {ty: ty,
     ctrs: nun_ctr_spec list}

  type nun_rec_spec =
    {func: tm,
     eqs: tm list}

  type nun_aliased_func =
    {func: tm,
     alias_id: ident}

  type nun_spec_spec =
    {funcs: nun_aliased_func list,
     props: tm list}

  datatype nun_command =
    NTVal of ty
  | NData of nun_co_data_spec list
  | NCodata of nun_co_data_spec list
  | NVal of tm * ty
  | NRec of nun_rec_spec list
  | NSpec of nun_spec_spec
  | NAxiom of tm
  | NGoal of tm

  type nun_problem = nun_command list

  val nun_fun_ident: ident

  val nun_const_of_str: string -> ident
  val nun_var_of_str: string -> ident

  val str_of_nun_problem: nun_problem -> string
end;

structure Nunchaku_Problem : NUNCHAKU_PROBLEM =
struct

open Nunchaku_Util;

type ident = string;

datatype ty =
  NType of ident * ty list
| NTVar of ident;

datatype tm =
  NConst of ident * ty list * ty
| NVar of ident * ty
| NAbs of tm * tm
| NApp of tm * tm;

type nun_ctr_spec =
  {ctr_id: ident,
   arg_tys: ty list};

type nun_co_data_spec =
  {ty: ty,
   ctrs: nun_ctr_spec list};

type nun_rec_spec =
  {func: tm,
   eqs: tm list};

type nun_aliased_func =
  {func: tm,
   alias_id: ident};

type nun_spec_spec =
  {funcs: nun_aliased_func list,
   props: tm list};

datatype nun_command =
  NTVal of ty
| NData of nun_co_data_spec list
| NCodata of nun_co_data_spec list
| NVal of tm * ty
| NRec of nun_rec_spec list
| NSpec of nun_spec_spec
| NAxiom of tm
| NGoal of tm;

type nun_problem = nun_command list;

val nun_fun_ident = "->";

fun nun_const_of_str s =
  let val s' = ascii_of s ^ "_" in
    if Char.isLower (String.sub (s', 0)) then s'
    else "c" ^ s' ^ "_"
  end;

fun nun_var_of_str s =
  let val s' = ascii_of s in
    if Char.isUpper (String.sub (s', 0)) then s'
    else "V" ^ s' ^ "_"
  end;

fun nun_range_ty (NType (id, [_, ty])) = if id = nun_fun_ident then ty else raise Fail "non-fun"
  | nun_range_ty _ = raise Fail "non-fun";

fun nun_ty_of (NConst (_, _, ty)) = ty
  | nun_ty_of (NVar (_, ty)) = ty
  | nun_ty_of (NAbs (tm, tm')) = NType (nun_fun_ident, [nun_ty_of tm, nun_ty_of tm'])
  | nun_ty_of (NApp (tm, _)) = nun_range_ty (nun_ty_of tm);

val parens = enclose "(" ")";

fun maybe_parens s =
  s |> String.isSubstring " " s ? parens;

fun str_of_arg_list str_of_arg =
  map (prefix " " o maybe_parens o str_of_arg) #> space_implode "";

fun str_of_and_list str_of_elem =
  map str_of_elem #> space_implode "\nand ";

fun str_of_nun_ident id = id;

val str_of_nun_ty =
  let
    fun str_of maybe_parens (NType (id, tys)) =
      if id = nun_fun_ident then
        (case tys of
          [ty, ty'] =>
          str_of parens ty ^ " " ^ nun_fun_ident ^ " " ^ str_of maybe_parens ty'
          |> maybe_parens)
      else
        id ^ str_of_arg_list (str_of I) tys
    | str_of _ (NTVar id) = str_of_nun_ident id
  in
    str_of I
  end;

val str_of_nun_tm =
  let
    fun str_of_at_const id tys =
      "@" ^ str_of_nun_ident id ^ str_of_arg_list str_of_nun_ty tys;

    fun str_of _ (NConst (id, [], _)) = str_of_nun_ident id
      | str_of (SOME ty0) (NConst (id, tys, ty)) =
        if ty = ty0 then str_of_nun_ident id else str_of_at_const id tys
      | str_of _ (NConst (id, tys, _)) = str_of_at_const id tys
      | str_of _ (NVar (id, _)) = str_of_nun_ident id
      | str_of ty_opt (NAbs (tm, tm')) =
        "fn " ^ str_of NONE tm ^ " => " ^ str_of (Option.map nun_range_ty ty_opt) tm'
      | str_of ty_opt (NApp (tm, tm')) =
        str_of (Option.map (fn ty => NType (nun_fun_ident, [nun_ty_of tm', ty])) ty_opt) tm ^
        str_of_arg_list (str_of NONE) [tm']
  in
    str_of NONE
  end;

fun str_of_nun_ctr_spec {ctr_id, arg_tys} =
  str_of_nun_ident ctr_id ^ str_of_arg_list str_of_nun_ty arg_tys;

fun str_of_nun_co_data_spec {ty, ctrs} =
  str_of_nun_ty ty ^ " =\n  " ^ space_implode "\n| " (map str_of_nun_ctr_spec ctrs);

fun str_of_nun_rec_spec {func, eqs} =
  str_of_nun_tm func ^ " :=\n  " ^ space_implode ";\n  " (map str_of_nun_tm eqs);

fun str_of_nun_aliased_func {func, alias_id} =
  str_of_nun_tm func ^ " as " ^ str_of_nun_ident alias_id;

fun str_of_nun_spec_spec {funcs, props} =
  space_implode " and " (map str_of_nun_aliased_func funcs) ^ " :=\n" ^
  space_implode ";\n  " (map str_of_nun_tm props);

fun str_of_nun_command (NTVal ty) = "val " ^ str_of_nun_ty ty ^ " : type"
  | str_of_nun_command (NData specs) = "data " ^ str_of_and_list str_of_nun_co_data_spec specs
  | str_of_nun_command (NCodata specs) = "codata " ^ str_of_and_list str_of_nun_co_data_spec specs
  | str_of_nun_command (NVal (tm, ty)) = "val " ^ str_of_nun_tm tm ^ " : " ^ str_of_nun_ty ty
  | str_of_nun_command (NRec specs) = "rec " ^ str_of_and_list str_of_nun_rec_spec specs
  | str_of_nun_command (NSpec spec) = "spec " ^ str_of_nun_spec_spec spec
  | str_of_nun_command (NAxiom tm) = "axiom " ^ str_of_nun_tm tm
  | str_of_nun_command (NGoal tm) = "goal " ^ str_of_nun_tm tm

val str_of_nun_problem = map str_of_nun_command #> cat_lines;

end;
