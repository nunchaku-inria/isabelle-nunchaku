(*  Title:      HOL/Tools/Nunchaku/nunchaku_problem.ML
    Author:     Jasmin Blanchette, Inria Nancy, LORIA, MPII
    Copyright   2015

Abstract syntax tree for Nunchaku problems.
*)

signature NUNCHAKU_PROBLEM =
sig
  type ident = string

  datatype ty =
    NType of ident * ty list
  | NTVar of ident

  datatype tm =
    NConst of ident * ty list * ty
  | NVar of ident * ty
  | NAbs of tm * tm
  | NApp of tm * tm

  type ctr_spec =
    {ctr_id: ident,
     arg_tys: ty list}

  type co_data_spec =
    {ty: ty,
     ctrs: ctr_spec list}

  type rec_spec =
    {func: tm,
     eqs: tm list}

  type aliased_func =
    {func: tm,
     alias_id: ident}

  type spec_spec =
    {funcs: aliased_func list,
     props: tm list}

  datatype command =
    Val of tm * ty
  | Data of co_data_spec list
  | Codata of co_data_spec list
  | Rec of rec_spec list
  | Spec of spec_spec
  | Axiom of tm
  | Goal of tm

  type problem = command list

  val fun_ident: string

  val str_of_problem: problem -> string
end;

structure Nunchaku_Problem : NUNCHAKU_PROBLEM =
struct

type ident = string;

datatype ty =
  NType of ident * ty list
| NTVar of ident;

datatype tm =
  NConst of ident * ty list * ty
| NVar of ident * ty
| NAbs of tm * tm
| NApp of tm * tm;

type ctr_spec =
  {ctr_id: ident,
   arg_tys: ty list};

type co_data_spec =
  {ty: ty,
   ctrs: ctr_spec list};

type rec_spec =
  {func: tm,
   eqs: tm list};

type aliased_func =
  {func: tm,
   alias_id: ident};

type spec_spec =
  {funcs: aliased_func list,
   props: tm list};

datatype command =
  Val of tm * ty
| Data of co_data_spec list
| Codata of co_data_spec list
| Rec of rec_spec list
| Spec of spec_spec
| Axiom of tm
| Goal of tm;

type problem = command list;

val fun_ident = "->";

fun range_ty (NType (id, [_, ty])) = if id = fun_ident then ty else raise Fail "non-fun"
  | range_ty _ = raise Fail "non-fun";

fun ty_of (NConst (_, _, ty)) = ty
  | ty_of (NVar (_, ty)) = ty
  | ty_of (NAbs (tm, tm')) = NType (fun_ident, [ty_of tm, ty_of tm'])
  | ty_of (NApp (tm, _)) = range_ty (ty_of tm);

val parens = enclose "(" ")";

fun maybe_parens s =
  s |> String.isSubstring " " s ? parens;

fun str_of_arg_list str_of_arg =
  map (prefix " " o maybe_parens o str_of_arg) #> space_implode "";

fun str_of_and_list str_of_elem =
  map str_of_elem #> space_implode "\nand ";

fun str_of_ident id = id;

val str_of_ty =
  let
    fun str_of maybe_parens (NType (id, tys)) =
      if id = fun_ident then
        (case tys of
          [ty, ty'] =>
          str_of parens ty ^ " " ^ fun_ident ^ " " ^ str_of maybe_parens ty'
          |> maybe_parens)
      else
        id ^ str_of_arg_list (str_of I) tys
    | str_of _ (NTVar id) = str_of_ident id
  in
    str_of I
  end;

fun str_of_at_const id tys =
  "@" ^ str_of_ident id ^ str_of_arg_list str_of_ty tys;

val str_of_tm =
  let
    fun str_of _ (NConst (id, [], _)) = str_of_ident id
      | str_of (SOME ty0) (NConst (id, tys, ty)) =
        if ty = ty0 then str_of_ident id else str_of_at_const id tys
      | str_of _ (NConst (id, tys, _)) = str_of_at_const id tys
      | str_of _ (NVar (id, _)) = str_of_ident id
      | str_of ty_opt (NAbs (tm, tm')) =
        "fn " ^ str_of NONE tm ^ " => " ^ str_of (Option.map range_ty ty_opt) tm'
      | str_of ty_opt (NApp (tm, tm')) =
        str_of (Option.map (fn ty => NType (fun_ident, [ty_of tm', ty])) ty_opt) tm ^
        str_of_arg_list (str_of NONE) [tm']
  in
    str_of NONE
  end;

fun str_of_ctr_spec {ctr_id, arg_tys} =
  str_of_ident ctr_id ^ str_of_arg_list str_of_ty arg_tys;

fun str_of_co_data_spec {ty, ctrs} =
  str_of_ty ty ^ " =\n  " ^ space_implode "\n| " (map str_of_ctr_spec ctrs);

fun str_of_rec_spec {func, eqs} =
  str_of_tm func ^ " :=\n  " ^ space_implode ";\n  " (map str_of_tm eqs);

fun str_of_aliased_func {func, alias_id} =
  str_of_tm func ^ " as " ^ str_of_ident alias_id;

fun str_of_spec_spec {funcs, props} =
  space_implode " and " (map str_of_aliased_func funcs) ^ " :=\n" ^
  space_implode ";\n  " (map str_of_tm props);

fun str_of_command (Val (tm, ty)) = "val " ^ str_of_tm tm ^ " : " ^ str_of_ty ty
  | str_of_command (Data specs) = "data " ^ str_of_and_list str_of_co_data_spec specs
  | str_of_command (Codata specs) = "codata " ^ str_of_and_list str_of_co_data_spec specs
  | str_of_command (Rec specs) = "rec " ^ str_of_and_list str_of_rec_spec specs
  | str_of_command (Spec spec) = "spec " ^ str_of_spec_spec spec
  | str_of_command (Axiom tm) = "axiom " ^ str_of_tm tm
  | str_of_command (Goal tm) = "goal " ^ str_of_tm tm

val str_of_problem = map str_of_command #> cat_lines;

end;
