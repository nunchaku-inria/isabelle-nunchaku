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
     alias: tm}

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

  val nun_fun: ident
  val nun_prop: ident

  val nun_conj: ident
  val nun_disj: ident
  val nun_equals: ident
  val nun_false: ident
  val nun_implies: ident
  val nun_not: ident
  val nun_true: ident

  val nun_tconst_of_str: string -> ident
  val nun_tvar_of_str: string -> ident
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
   alias: tm};

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

val nun_type = "type";

val nun_fun = "->";
val nun_prop = "prop";

val nun_conj = "&&";
val nun_disj = "||";
val nun_equals = "=";
val nun_false = "false";
val nun_implies = "=>";
val nun_not = "~";
val nun_true = "true";

val is_nun_const_infix = member (op =) [nun_conj, nun_disj, nun_equals, nun_implies];

fun gen_nun_const_of_str pre suf s =
  let val s' = ascii_of s ^ suf in
    if Char.isLower (String.sub (s', 0)) then s' else pre ^ s'
  end;

fun gen_nun_var_of_str pre suf s =
  let val s' = ascii_of s ^ suf in
    if Char.isUpper (String.sub (s', 0)) then s' else pre ^ s'
  end;

val nun_tconst_of_str = gen_nun_const_of_str "y" "__";
val nun_tvar_of_str = gen_nun_var_of_str "A" "__";
val nun_const_of_str = gen_nun_const_of_str "c" "_";
val nun_var_of_str = gen_nun_var_of_str "V" "_";

fun nun_range_ty (NType (id, [_, ty])) = if id = nun_fun then ty else raise Fail "non-fun"
  | nun_range_ty _ = raise Fail "non-fun";

fun nun_ty_of (NConst (_, _, ty)) = ty
  | nun_ty_of (NVar (_, ty)) = ty
  | nun_ty_of (NAbs (tm, tm')) = NType (nun_fun, [nun_ty_of tm, nun_ty_of tm'])
  | nun_ty_of (NApp (tm, _)) = nun_range_ty (nun_ty_of tm);

fun str_of_ident id = id;

val str_of_nun_ty =
  let
    fun str_of maybe_parens (NType (id, tys)) =
      if id = nun_fun then
        (case tys of
          [ty, ty'] =>
          maybe_parens (str_of parens ty ^ " " ^ nun_fun ^ " " ^ str_of maybe_parens ty'))
      else
        id ^ str_of_arg_list (str_of I) tys
    | str_of _ (NTVar id) = str_of_ident id
  in
    str_of I
  end;

val str_of_nun_tm =
  let
    fun str_of_at_const id tys =
      "@" ^ str_of_ident id ^ str_of_arg_list str_of_nun_ty tys;

    fun str_of_app ty_opt tm tm' =
      let
        val ty_opt' =
          try (Option.map (fn ty => NType (nun_fun, [nun_ty_of tm', ty]))) ty_opt
          |> the_default NONE;
      in
        str_of ty_opt' tm ^ str_of_arg_list (str_of NONE) [tm']
      end
    and str_of _ (NConst (id, [], _)) = str_of_ident id
      | str_of (SOME ty0) (NConst (id, tys, ty)) =
        if ty = ty0 then str_of_ident id else str_of_at_const id tys
      | str_of _ (NConst (id, tys, _)) =
        str_of_at_const id tys
      | str_of _ (NVar (id, _)) = str_of_ident id
      | str_of ty_opt (NAbs (tm, tm')) =
        "fn " ^ str_of NONE tm ^ " => " ^ str_of (Option.map nun_range_ty ty_opt) tm'
      | str_of ty_opt (NApp (tm, tm')) =
        (case tm of
          NApp (NConst (id, _, _), tm1) =>
          if is_nun_const_infix id then
            let val ty_opt' = try nun_ty_of tm' in
              str_of NONE tm1 ^ " " ^ id ^ " " ^ str_of ty_opt' tm'
            end
          else
            str_of_app ty_opt tm tm'
        | _ => str_of_app ty_opt tm tm');
  in
    str_of NONE
  end;

fun str_of_nun_ctr_spec {ctr_id, arg_tys} =
  str_of_ident ctr_id ^ str_of_arg_list str_of_nun_ty arg_tys;

fun str_of_nun_co_data_spec {ty, ctrs} =
  str_of_nun_ty ty ^ " =\n  " ^ space_implode "\n| " (map str_of_nun_ctr_spec ctrs);

fun str_of_nun_rec_spec {func, eqs} =
  str_of_nun_tm func ^ " :=\n  " ^ space_implode ";\n  " (map str_of_nun_tm eqs);

fun str_of_nun_aliased_func {func, alias} =
  str_of_nun_tm func ^ " as " ^ str_of_nun_tm alias;

fun str_of_nun_spec_spec {funcs, props} =
  space_implode " and " (map str_of_nun_aliased_func funcs) ^ " :=\n" ^
  space_implode ";\n  " (map str_of_nun_tm props);

fun str_of_nun_command (NTVal ty) =
    (case ty of
      NType (id, tys) =>
      "val " ^ str_of_ident id ^ " : " ^
      fold (K (prefix (nun_type ^ " " ^ nun_fun ^ " "))) tys nun_type
    | _ => raise Fail "non-NType")
  | str_of_nun_command (NData specs) = "data " ^ str_of_and_list str_of_nun_co_data_spec specs
  | str_of_nun_command (NCodata specs) = "codata " ^ str_of_and_list str_of_nun_co_data_spec specs
  | str_of_nun_command (NVal (tm, ty)) = "val " ^ str_of_nun_tm tm ^ " : " ^ str_of_nun_ty ty
  | str_of_nun_command (NRec specs) = "rec " ^ str_of_and_list str_of_nun_rec_spec specs
  | str_of_nun_command (NSpec spec) = "spec " ^ str_of_nun_spec_spec spec
  | str_of_nun_command (NAxiom tm) = "axiom " ^ str_of_nun_tm tm
  | str_of_nun_command (NGoal tm) = "goal " ^ str_of_nun_tm tm

val str_of_nun_problem = map (suffix "." o str_of_nun_command) #> cat_lines #> suffix "\n";

end;
