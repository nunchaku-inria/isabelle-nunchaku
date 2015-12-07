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

  type nun_type_spec =
    {ty: ty,
     pred: tm,
     abs: tm,
     rep: tm}

  type nun_ctr_spec =
    {ctr: tm,
     arg_tys: ty list}

  type nun_co_data_spec =
    {ty: ty,
     ctrs: nun_ctr_spec list}

  type nun_const_spec =
    {const: tm,
     props: tm list}

  type nun_consts_spec =
    {consts: tm list,
     props: tm list}

  datatype nun_command =
    NTVal of ty
  | NCopy of nun_type_spec
  | NQuotient of nun_type_spec
  | NData of nun_co_data_spec list
  | NCodata of nun_co_data_spec list
  | NVal of tm * ty
  | NPred of nun_const_spec list
  | NCopred of nun_const_spec list
  | NRec of nun_const_spec list
  | NSpec of nun_consts_spec
  | NAxiom of tm
  | NGoal of tm

  type nun_problem = nun_command list list

  type name_pool =
    {nice_of_ugly: string Symtab.table,
     nice_but_taken: unit Symtab.table}

  val nun_fun: ident
  val nun_prop: ident

  val nun_conj: ident
  val nun_disj: ident
  val nun_equals: ident
  val nun_exists: ident
  val nun_false: ident
  val nun_forall: ident
  val nun_if: ident
  val nun_implies: ident
  val nun_not: ident
  val nun_true: ident

  val nun_tconst_of_str: string -> ident
  val nun_tvar_of_str: string -> ident
  val nun_const_of_str: string -> ident
  val nun_var_of_str: string -> ident

  val nun_prop_ty: ty

  val fold_map_nun_problem_idents: (string -> 'a -> string * 'a) -> nun_problem -> 'a ->
    nun_problem * 'a

  val beta_reduce_tm: tm -> tm

  val str_of_ident: ident -> string
  val str_of_ty: ty -> string
  val str_of_tm: tm -> string
  val str_of_tmty: tm -> string

  val nice_nun_problem: nun_problem -> nun_problem * name_pool
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

type nun_type_spec =
  {ty: ty,
   pred: tm,
   abs: tm,
   rep: tm};

type nun_ctr_spec =
  {ctr: tm,
   arg_tys: ty list};

type nun_co_data_spec =
  {ty: ty,
   ctrs: nun_ctr_spec list};

type nun_const_spec =
  {const: tm,
   props: tm list};

type nun_consts_spec =
  {consts: tm list,
   props: tm list};

datatype nun_command =
  NTVal of ty
| NCopy of nun_type_spec
| NQuotient of nun_type_spec
| NData of nun_co_data_spec list
| NCodata of nun_co_data_spec list
| NVal of tm * ty
| NPred of nun_const_spec list
| NCopred of nun_const_spec list
| NRec of nun_const_spec list
| NSpec of nun_consts_spec
| NAxiom of tm
| NGoal of tm;

type nun_problem = nun_command list list;

type name_pool =
  {nice_of_ugly: string Symtab.table,
   nice_but_taken: unit Symtab.table};

val nun_type = "type";

val nun_fun = "->";
val nun_prop = "prop";

val nun_conj = "&&";
val nun_disj = "||";
val nun_equals = "=";
val nun_exists = "exists";
val nun_false = "false";
val nun_forall = "forall";
val nun_if = "if";
val nun_implies = "=>";
val nun_not = "~";
val nun_true = "true";

val nun_else = "else";
val nun_then = "then";

val is_nun_const_quantifier = member (op =) [nun_forall, nun_exists];
val is_nun_const_truth_value = member (op =) [nun_false, nun_true];
val is_nun_const_connective = member (op =) [nun_conj, nun_disj, nun_implies];
val is_nun_const_infix = is_nun_const_connective orf curry (op =) nun_equals;

fun gen_nun_const_of_str pre suf s =
  let val s' = ascii_of s ^ suf in
    if Char.isLower (String.sub (s', 0)) then s' else pre ^ s'
  end;

fun gen_nun_var_of_str pre suf s =
  let val s' = ascii_of s ^ suf in
    if Char.isUpper (String.sub (s', 0)) then s' else pre ^ s'
  end;

fun is_non_builtin_ident s = String.isSuffix "_" s;

val nun_tconst_of_str = gen_nun_const_of_str "y." "__";
val nun_tvar_of_str = gen_nun_var_of_str "A." "__";
val nun_const_of_str = gen_nun_const_of_str "c." "_";
val nun_var_of_str = gen_nun_var_of_str "V." "_";

val nun_prop_ty = NType (nun_prop, []);

fun nun_domain_ty (NType (id, [ty, _])) = if id = nun_fun then ty else raise Fail "non-fun"
  | nun_domain_ty _ = raise Fail "non-fun";

fun nun_range_ty (NType (id, [_, ty])) = if id = nun_fun then ty else raise Fail "non-fun"
  | nun_range_ty _ = raise Fail "non-fun";

fun nun_ty_of (NConst (_, _, ty)) = ty
  | nun_ty_of (NVar (_, ty)) = ty
  | nun_ty_of (NAbs (var, body)) = NType (nun_fun, [nun_ty_of var, nun_ty_of body])
  | nun_ty_of (NApp (const, _)) = nun_range_ty (nun_ty_of const);

fun strip_nun_binders binder (app as NApp (NConst (id, _, _), NAbs (var, body))) =
    if id = binder then
      strip_nun_binders binder body
      |>> cons var
    else
      ([], app)
  | strip_nun_binders _ tm = ([], tm);

fun fold_map_ty_idents f (NType (id, tys)) =
    f id
    ##>> fold_map (fold_map_ty_idents f) tys
    #>> NType
  | fold_map_ty_idents f (NTVar id) =
    f id
    #>> NTVar;

fun fold_map_tm_idents f (NConst (id, tys, ty)) =
    f id
    ##>> fold_map (fold_map_ty_idents f) tys
    ##>> fold_map_ty_idents f ty
    #>> (Scan.triple1 #> NConst)
  | fold_map_tm_idents f (NVar (id, ty)) =
    f id
    ##>> fold_map_ty_idents f ty
    #>> NVar
  | fold_map_tm_idents f (NAbs (var, body)) =
    fold_map_tm_idents f var
    ##>> fold_map_tm_idents f body
    #>> NAbs
  | fold_map_tm_idents f (NApp (const, arg)) =
    fold_map_tm_idents f const
    ##>> fold_map_tm_idents f arg
    #>> NApp;

fun fold_map_nun_type_spec_idents f {ty, pred, abs, rep} =
  fold_map_ty_idents f ty
  ##>> fold_map_tm_idents f pred
  ##>> fold_map_tm_idents f abs
  ##>> fold_map_tm_idents f rep
  #>> (fn (((ty, pred), abs), rep) => {ty = ty, pred = pred, abs = abs, rep = rep});

fun fold_map_nun_ctr_spec_idents f {ctr, arg_tys} =
  fold_map_tm_idents f ctr
  ##>> fold_map (fold_map_ty_idents f) arg_tys
  #>> (fn (ctr, arg_tys) => {ctr = ctr, arg_tys = arg_tys});

fun fold_map_nun_co_data_spec_idents f {ty, ctrs} =
  fold_map_ty_idents f ty
  ##>> fold_map (fold_map_nun_ctr_spec_idents f) ctrs
  #>> (fn (ty, ctrs) => {ty = ty, ctrs = ctrs});

fun fold_map_nun_const_spec_idents f {const, props} =
  fold_map_tm_idents f const
  ##>> fold_map (fold_map_tm_idents f) props
  #>> (fn (const, props) => {const = const, props = props});

fun fold_map_nun_consts_spec_idents f {consts, props} =
  fold_map (fold_map_tm_idents f) consts
  ##>> fold_map (fold_map_tm_idents f) props
  #>> (fn (consts, props) => {consts = consts, props = props});

fun fold_map_nun_command_idents f (NTVal ty) =
    fold_map_ty_idents f ty
    #>> NTVal
  | fold_map_nun_command_idents f (NCopy spec) =
    fold_map_nun_type_spec_idents f spec
    #>> NCopy
  | fold_map_nun_command_idents f (NQuotient spec) =
    fold_map_nun_type_spec_idents f spec
    #>> NQuotient
  | fold_map_nun_command_idents f (NData specs) =
    fold_map (fold_map_nun_co_data_spec_idents f) specs
    #>> NData
  | fold_map_nun_command_idents f (NCodata specs) =
    fold_map (fold_map_nun_co_data_spec_idents f) specs
    #>> NCodata
  | fold_map_nun_command_idents f (NVal (tm, ty)) =
    fold_map_tm_idents f tm
    ##>> fold_map_ty_idents f ty
    #>> NVal
  | fold_map_nun_command_idents f (NPred specs) =
    fold_map (fold_map_nun_const_spec_idents f) specs
    #>> NPred
  | fold_map_nun_command_idents f (NCopred specs) =
    fold_map (fold_map_nun_const_spec_idents f) specs
    #>> NCopred
  | fold_map_nun_command_idents f (NRec specs) =
    fold_map (fold_map_nun_const_spec_idents f) specs
    #>> NRec
  | fold_map_nun_command_idents f (NSpec spec) =
    fold_map_nun_consts_spec_idents f spec
    #>> NSpec
  | fold_map_nun_command_idents f (NAxiom tm) =
    fold_map_tm_idents f tm
    #>> NAxiom
  | fold_map_nun_command_idents f (NGoal tm) =
    fold_map_tm_idents f tm
    #>> NGoal;

fun fold_map_nun_problem_idents f =
  fold_map (fold_map (fold_map_nun_command_idents f));

fun dest_rassoc_args oper arg0 rest =
  (case rest of
    NApp (NApp (oper', arg1), rest') =>
    if oper' = oper then arg0 :: dest_rassoc_args oper arg1 rest' else [arg0, rest]
  | _ => [arg0, rest]);

fun replace_tm from to =
  let
    (* This code assumes all enclosing binders bind distinct variables and bound variables are
       distinct from any other variables. *)
    fun replace (NApp (const, arg)) = NApp (replace const, replace arg)
      | replace (NAbs (var, body)) = NAbs (var, replace body)
      | replace tm = if tm = from then to else tm;
  in
    replace
  end;

fun beta_reduce_tm (NApp (NAbs (var, body), arg)) = beta_reduce_tm (replace_tm var arg body)
  | beta_reduce_tm (NApp (const, arg)) =
    (case beta_reduce_tm const of
      const' as NAbs _ => beta_reduce_tm (NApp (const', arg))
    | const' => NApp (const', beta_reduce_tm arg))
  | beta_reduce_tm (NAbs (var, body)) = NAbs (var, beta_reduce_tm body)
  | beta_reduce_tm tm = tm;

fun str_of_ident id = id;

val str_of_ty =
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

val str_of_tm =
  let
    fun is_triv_head (NConst (id, _, ty)) =
        is_non_builtin_ident id orelse is_nun_const_truth_value id
      | is_triv_head (NVar _) = true
      | is_triv_head (NApp (const, _)) = is_triv_head const
      | is_triv_head (NAbs _) = false

    fun str_of_at_const id tys =
      "@" ^ str_of_ident id ^ str_of_arg_list str_of_ty tys;

    fun str_of_app ty_opt const arg =
      let
        val ty_opt' =
          try (Option.map (fn ty => NType (nun_fun, [nun_ty_of arg, ty]))) ty_opt
          |> the_default NONE;
      in
        (str_of ty_opt' const |> (case const of NAbs _ => parens | _ => I)) ^
        str_of_arg_list (str_of NONE) [arg]
      end
    and str_of _ (NConst (id, [], _)) = str_of_ident id
      | str_of (SOME ty0) (NConst (id, tys, ty)) =
        if ty = ty0 then str_of_ident id else str_of_at_const id tys
      | str_of _ (NConst (id, tys, _)) =
        str_of_at_const id tys
      | str_of _ (NVar (id, _)) = str_of_ident id
      | str_of ty_opt (NAbs (var, body)) =
        "fun " ^ str_of (Option.map nun_domain_ty ty_opt) var ^ ". " ^
        str_of (Option.map nun_range_ty ty_opt) body
      | str_of ty_opt (app as NApp (const, argN)) =
        (case (const, argN) of
          (NApp (oper as NConst (id, _, _), arg1), arg2) =>
          if id = nun_equals then
            (str_of NONE arg1 |> not (is_triv_head arg1) ? parens) ^ " " ^ id ^ " " ^
            (str_of (try nun_ty_of arg2) arg2 |> not (is_triv_head arg2) ? parens)
          else if is_nun_const_connective id then
            let
              val ty_opt' = SOME nun_prop_ty;
              val args = dest_rassoc_args oper arg1 arg2;
            in
              space_implode (" " ^ id ^ " ")
                (map (fn arg => str_of NONE arg |> not (is_triv_head arg) ? parens) args)
            end
          else
            str_of_app ty_opt const argN
        | (NApp (NApp (oper as NConst (id, _, _), arg1), arg2), arg3) =>
          if id = nun_if then
            nun_if ^ " " ^ str_of NONE arg1 ^ " " ^ nun_then ^ " " ^ str_of NONE arg2 ^ " " ^
            nun_else ^ " " ^ str_of NONE arg3
            |> parens
          else
            str_of_app ty_opt const argN
        | (NConst (id, _, _), NAbs _) =>
          if is_nun_const_quantifier id then
            let val (vars, body) = strip_nun_binders id app in
              id ^ " " ^ space_implode " " (map (str_of NONE) vars) ^ ". " ^ str_of NONE body
            end
          else
            str_of_app ty_opt const argN
        | _ => str_of_app ty_opt const argN);
  in
    str_of NONE
  end;

fun str_of_tmty tm = str_of_tm tm ^ " : " ^ str_of_ty (nun_ty_of tm);

val empty_name_pool = {nice_of_ugly = Symtab.empty, nice_but_taken = Symtab.empty};

val nice_of_ugly_suggestion =
  unascii_of #> Long_Name.base_name #> ascii_of #> unsuffix "_";

fun index_name 1 s = s
  | index_name j s =
    let
      val n = size s;
      val m = n - 1;
    in
      String.substring (s, 0, m) ^ string_of_int j ^ String.substring (s, m, n - m)
    end;

fun allocate_nice ugly ({nice_of_ugly, nice_but_taken} : name_pool) nice_sugg0 =
  let
    fun alloc j =
      let val nice_sugg = index_name j nice_sugg0 in
        (case Symtab.lookup nice_but_taken nice_sugg of
          NONE =>
          (nice_sugg,
           {nice_of_ugly = Symtab.update_new (ugly, nice_sugg) nice_of_ugly,
            nice_but_taken = Symtab.update_new (nice_sugg, ()) nice_but_taken})
        | SOME () => alloc (j + 1))
      end;
  in
    alloc 1
  end;

fun nice_ident ugly (pool as {nice_of_ugly, ...}) =
  if is_non_builtin_ident ugly then
    (case Symtab.lookup nice_of_ugly ugly of
      NONE =>
      let val nice_sugg = nice_of_ugly_suggestion ugly in
        allocate_nice ugly pool nice_sugg
      end
    | SOME nice => (nice, pool))
  else
    (ugly, pool);

fun nice_nun_problem prob =
  fold_map_nun_problem_idents nice_ident prob empty_name_pool;

fun str_of_tval (NType (id, tys)) =
    str_of_ident id ^ " : " ^ fold (K (prefix (nun_type ^ " " ^ nun_fun ^ " "))) tys nun_type
  | str_of_tval _ = raise Fail "non-NType";

fun str_of_nun_type_spec {ty, pred, abs, rep} =
  str_of_ty ty ^ " := " ^ str_of_tm pred ^ "\n  abs " ^ str_of_tm abs ^ "\n  rep " ^ str_of_tm rep;

fun str_of_nun_ctr_spec {ctr, arg_tys} =
  str_of_tm ctr ^ str_of_arg_list str_of_ty arg_tys;

fun str_of_nun_co_data_spec {ty, ctrs} =
  str_of_ty ty ^ " :=\n  " ^ space_implode "\n| " (map str_of_nun_ctr_spec ctrs);

fun str_of_nun_const_spec {const, props} =
  str_of_tmty const ^ " :=\n  " ^ space_implode ";\n  " (map str_of_tm props);

fun str_of_nun_consts_spec {consts, props} =
  space_implode " and\n     " (map str_of_tmty consts) ^ " :=\n  " ^
  space_implode ";\n  " (map str_of_tm props);

fun str_of_nun_command (NTVal ty) = "val " ^ str_of_tval ty
  | str_of_nun_command (NCopy spec) = "copy " ^ str_of_nun_type_spec spec
  | str_of_nun_command (NQuotient spec) = "quotient " ^ str_of_nun_type_spec spec
  | str_of_nun_command (NData specs) = "data " ^ str_of_and_list str_of_nun_co_data_spec specs
  | str_of_nun_command (NCodata specs) = "codata " ^ str_of_and_list str_of_nun_co_data_spec specs
  | str_of_nun_command (NVal (tm, ty)) = "val " ^ str_of_tm tm ^ " : " ^ str_of_ty ty
  | str_of_nun_command (NPred specs) = "pred " ^ str_of_and_list str_of_nun_const_spec specs
  | str_of_nun_command (NCopred specs) = "copred " ^ str_of_and_list str_of_nun_const_spec specs
  | str_of_nun_command (NRec specs) = "rec " ^ str_of_and_list str_of_nun_const_spec specs
  | str_of_nun_command (NSpec spec) = "spec " ^ str_of_nun_consts_spec spec
  | str_of_nun_command (NAxiom tm) = "axiom " ^ str_of_tm tm
  | str_of_nun_command (NGoal tm) = "goal " ^ str_of_tm tm;

val str_of_nun_problem =
  map (cat_lines o map (suffix "." o str_of_nun_command))
  #> space_implode "\n\n" #> suffix "\n";

end;
