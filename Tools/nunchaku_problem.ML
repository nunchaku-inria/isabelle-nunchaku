(*  Title:      HOL/Tools/Nunchaku/nunchaku_problem.ML
    Author:     Jasmin Blanchette, Inria Nancy, LORIA, MPII
    Copyright   2015, 2016

Abstract syntax tree for Nunchaku problems.
*)

signature NUNCHAKU_PROBLEM =
sig
  eqtype ident

  datatype ty =
    NType of ident * ty list

  datatype tm =
    NAtom of int * ty
  | NConst of ident * ty list * ty
  | NVar of ident * ty
  | NAbs of tm * tm
  | NMatch of tm * (ident * tm list * tm) list
  | NApp of tm * tm

  type nun_type_spec =
    {abs_ty: ty,
     rep_ty: ty,
     wrt: tm,
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
  | NPred of bool * nun_const_spec list
  | NCopred of nun_const_spec list
  | NRec of nun_const_spec list
  | NSpec of nun_consts_spec
  | NAxiom of tm
  | NGoal of tm
  | NEval of tm

  type nun_problem = nun_command list list

  type name_pool =
    {nice_of_ugly: string Symtab.table,
     ugly_of_nice: string Symtab.table}

  val nun_dummy: ident

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
  val nun_match: ident
  val nun_mu: ident
  val nun_not: ident
  val nun_true: ident

  val ident_of_str: string -> ident
  val str_of_ident: ident -> string
  val nun_const_of_str: string list -> string -> ident
  val nun_var_of_str: string -> ident
  val str_of_nun_const: ident -> string list * string
  val str_of_nun_var: ident -> string

  val nun_dummy_ty: ty
  val nun_prop_ty: ty

  val ty_of: tm -> ty

  val fold_map_ty_idents: (string -> 'a -> string * 'a) -> ty -> 'a -> ty * 'a
  val fold_map_tm_idents: (string -> 'a -> string * 'a) -> tm -> 'a -> tm * 'a
  val fold_map_nun_command_idents: (string -> 'a -> string * 'a) -> nun_command -> 'a ->
    nun_command * 'a
  val fold_map_nun_problem_idents: (string -> 'a -> string * 'a) -> nun_problem -> 'a ->
    nun_problem * 'a

  val allocate_nice: name_pool -> string * string -> string * name_pool

  val rcomb_tms: tm list -> tm -> tm
  val abs_tms: tm list -> tm -> tm
  val beta_reduce_tm: tm -> tm
  val eta_expandN_tm: int -> tm -> tm
  val eta_expand_builtin_tm: tm -> tm

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
  NType of ident * ty list;

datatype tm =
  NAtom of int * ty
| NConst of ident * ty list * ty
| NVar of ident * ty
| NAbs of tm * tm
| NMatch of tm * (ident * tm list * tm) list
| NApp of tm * tm;

type nun_type_spec =
  {abs_ty: ty,
   rep_ty: ty,
   wrt: tm,
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
| NPred of bool * nun_const_spec list
| NCopred of nun_const_spec list
| NRec of nun_const_spec list
| NSpec of nun_consts_spec
| NAxiom of tm
| NGoal of tm
| NEval of tm;

type nun_problem = nun_command list list;

type name_pool =
  {nice_of_ugly: string Symtab.table,
   ugly_of_nice: string Symtab.table};

val nun_dummy = "_";

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
val nun_match = "match";
val nun_mu = "mu";
val nun_not = "~";
val nun_true = "true";

val is_nun_const_quantifier = member (op =) [nun_forall, nun_exists];
val is_nun_const_connective = member (op =) [nun_conj, nun_disj, nun_implies];

val nun_builtin_arity =
  [(nun_conj, 2),
   (nun_disj, 2),
   (nun_equals, 2),
   (nun_exists, 1),
   (nun_false, 0),
   (nun_forall, 1),
   (nun_if, 3),
   (nun_implies, 2),
   (nun_not, 1),
   (nun_true, 0)];

val arity_of_nun_builtin = AList.lookup (op =) nun_builtin_arity #> the_default 0;

val nun_const_prefix = "c.";
val nun_var_prefix = "V.";
val nun_custom_id_suffix = "_";

val ident_of_str = I : string -> ident;
val str_of_ident = I : ident -> string;

val encode_args = enclose "(" ")" o commas;

fun decode_args s =
  let
    fun delta #"(" = 1
      | delta #")" = ~1
      | delta _ = 0;

    fun dec _ [] _ = raise Fail ("ill-formed arguments in " ^ quote s)
      | dec 0 (#"(" :: #")" :: cs) _ = ([], String.implode cs)
      | dec 0 (#"(" :: cs) [] = dec 1 cs [[]]
      | dec 0 _ _ = raise Fail ("ill-formed arguments in " ^ quote s)
      | dec 1 (#")" :: cs) args = (rev (map (String.implode o rev) args), String.implode cs)
      | dec n (#"," :: cs) args = dec n cs ([] :: args)
      | dec n (c :: cs) (arg :: args) = dec (n + delta c) cs ((c :: arg) :: args);
  in
    dec 0 (String.explode s) []
  end;

fun nun_const_of_str args =
  suffix nun_custom_id_suffix #> prefix nun_const_prefix #> prefix (encode_args args);

val nun_var_of_str = suffix nun_custom_id_suffix #> prefix nun_var_prefix;
val str_of_nun_const = decode_args ##> unprefix nun_const_prefix ##> unsuffix nun_custom_id_suffix;
val str_of_nun_var = unprefix nun_var_prefix #> unsuffix nun_custom_id_suffix;

fun index_name s 0 = s
  | index_name s j =
    let
      val n = size s;
      val m = n - 1;
    in
      String.substring (s, 0, m) ^ string_of_int j ^ String.substring (s, m, n - m)
    end;

val nun_dummy_ty = NType (nun_dummy, []);
val nun_prop_ty = NType (nun_prop, []);

fun domain_ty (NType (id, [ty, _])) = if id = nun_fun then ty else raise Fail "non-fun"
  | domain_ty _ = raise Fail "non-fun";

fun range_ty (NType (id, [_, ty])) = if id = nun_fun then ty else raise Fail "non-fun"
  | range_ty _ = raise Fail "non-fun";

fun domain_tys 0 _ = []
  | domain_tys n ty = domain_ty ty :: domain_tys (n - 1) (range_ty ty);

fun ty_of (NAtom (_, ty)) = ty
  | ty_of (NConst (_, _, ty)) = ty
  | ty_of (NVar (_, ty)) = ty
  | ty_of (NAbs (var, body)) = NType (nun_fun, [ty_of var, ty_of body])
  | ty_of (NMatch (obj, (_, _, body1) :: _)) = ty_of body1
  | ty_of (NApp (const, _)) = range_ty (ty_of const);

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
    #>> NType;

fun fold_map_match_branch_idents f (id, vars, body) =
    f id
    ##>> fold_map (fold_map_tm_idents f) vars
    ##>> fold_map_tm_idents f body
    #>> Scan.triple1
and fold_map_tm_idents f (NAtom (j, ty)) =
    fold_map_ty_idents f ty
    #>> curry NAtom j
  | fold_map_tm_idents f (NConst (id, tys, ty)) =
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
  | fold_map_tm_idents f (NMatch (obj, branches)) =
    fold_map_tm_idents f obj
    ##>> fold_map (fold_map_match_branch_idents f) branches
    #>> NMatch
  | fold_map_tm_idents f (NApp (const, arg)) =
    fold_map_tm_idents f const
    ##>> fold_map_tm_idents f arg
    #>> NApp;

fun fold_map_nun_type_spec_idents f {abs_ty, rep_ty, wrt, abs, rep} =
  fold_map_ty_idents f abs_ty
  ##>> fold_map_ty_idents f rep_ty
  ##>> fold_map_tm_idents f wrt
  ##>> fold_map_tm_idents f abs
  ##>> fold_map_tm_idents f rep
  #>> (fn ((((abs_ty, rep_ty), wrt), abs), rep) =>
    {abs_ty = abs_ty, rep_ty = rep_ty, wrt = wrt, abs = abs, rep = rep});

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
  | fold_map_nun_command_idents f (NPred (wf, specs)) =
    fold_map (fold_map_nun_const_spec_idents f) specs
    #>> curry NPred wf
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
    #>> NGoal
  | fold_map_nun_command_idents f (NEval tm) =
    fold_map_tm_idents f tm
    #>> NEval;

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
    fun repl_br (id, vars, body) = (id, map repl vars, repl body)
    and repl (NApp (const, arg)) = NApp (repl const, repl arg)
      | repl (NAbs (var, body)) = NAbs (var, repl body)
      | repl (NMatch (obj, branches)) = NMatch (repl obj, map repl_br branches)
      | repl tm = if tm = from then to else tm;
  in
    repl
  end;

val rcomb_tms = fold (fn arg => fn func => NApp (func, arg));
val abs_tms = fold_rev (curry NAbs);

fun fresh_var_names_wrt_tm n tm =
  let
    fun max_var_br (_, vars, body) = fold max_var (body :: vars)
    and max_var (NAtom _) = I
      | max_var (NConst _) = I
      | max_var (NVar (id, _)) = (fn max => if size id > size max then id else max)
      | max_var (NApp (func, arg)) = fold max_var [func, arg]
      | max_var (NAbs (var, body)) = fold max_var [var, body]
      | max_var (NMatch (obj, branches)) = max_var obj #> fold max_var_br branches;

    val dummy_name = nun_var_of_str Name.uu;
    val max_name = max_var tm dummy_name;
  in
    map (index_name max_name) (1 upto n)
  end;

val fresh_var_name_wrt_tm = the_single o fresh_var_names_wrt_tm 1;

fun beta_reduce_tm (NApp (NAbs (var, body), arg)) = beta_reduce_tm (replace_tm var arg body)
  | beta_reduce_tm (NApp (const, arg)) =
    (case beta_reduce_tm const of
      const' as NAbs _ => beta_reduce_tm (NApp (const', arg))
    | const' => NApp (const', beta_reduce_tm arg))
  | beta_reduce_tm (NAbs (var, body)) = NAbs (var, beta_reduce_tm body)
  | beta_reduce_tm (NMatch (obj, branches)) =
    NMatch (beta_reduce_tm obj, map (@{apply 3(3)} beta_reduce_tm) branches)
  | beta_reduce_tm tm = tm;

fun eta_expandN_tm 0 tm = tm
  | eta_expandN_tm n tm =
    let
      val var_names = fresh_var_names_wrt_tm n tm;
      val arg_tys = domain_tys n (ty_of tm);
      val vars = map2 (curry NVar) var_names arg_tys;
    in
      abs_tms vars (rcomb_tms vars tm)
    end;

val eta_expand_builtin_tm =
  let
    fun expand_quant_arg (NAbs (var, body)) = NAbs (var, expand_quant_arg body)
      | expand_quant_arg (NMatch (obj, branches)) =
        NMatch (obj, map (@{apply 3(3)} expand_quant_arg) branches)
      | expand_quant_arg (tm as NApp (_, NAbs _)) = tm
      | expand_quant_arg (NApp (quant, arg)) = NApp (quant, eta_expandN_tm 1 arg)
      | expand_quant_arg tm = tm;

    fun expand args (NApp (func, arg)) = expand (expand [] arg :: args) func
      | expand args (func as NConst (id, _, _)) =
        let val missing = Int.max (0, arity_of_nun_builtin id - length args) in
          rcomb_tms args func
          |> eta_expandN_tm missing
          |> is_nun_const_quantifier id ? expand_quant_arg
        end
      | expand args (func as NAtom _) = rcomb_tms args func
      | expand args (func as NVar _) = rcomb_tms args func
      | expand args (NAbs (var, body)) = rcomb_tms args (NAbs (var, expand [] body))
      | expand args (NMatch (obj, branches)) =
        rcomb_tms args (NMatch (obj, map (@{apply 3(3)} (expand [])) branches));
  in
    expand []
  end;

val str_of_ty =
  let
    fun str_of maybe_parens (NType (id, tys)) =
      if id = nun_fun then
        (case tys of
          [ty, ty'] => maybe_parens (str_of parens ty ^ " " ^ nun_fun ^ " " ^ str_of I ty'))
      else
        id ^ str_of_arg_list (str_of I) tys
  in
    str_of I
  end;

val (str_of_tmty, str_of_tm) =
  let
    fun is_triv_head (NConst (id, _, ty)) = (arity_of_nun_builtin id = 0)
      | is_triv_head (NAtom _) = true
      | is_triv_head (NVar _) = true
      | is_triv_head (NApp (const, _)) = is_triv_head const
      | is_triv_head (NAbs _) = false
      | is_triv_head (NMatch _) = false;

    fun str_of_at_const id tys =
      "@" ^ str_of_ident id ^ str_of_arg_list str_of_ty tys;

    fun str_of_app ty_opt const arg =
      let
        val ty_opt' =
          try (Option.map (fn ty => NType (nun_fun, [ty_of arg, ty]))) ty_opt
          |> the_default NONE;
      in
        (str_of ty_opt' const |> (case const of NAbs _ => parens | _ => I)) ^
        str_of_arg_list (str_of NONE) [arg]
      end
    and str_of_br ty_opt (id, vars, body) =
      " | " ^ id ^ space_implode "" (map (prefix " " o str_of NONE) vars) ^ " -> " ^
      str_of ty_opt body
    and str_of_tmty tm =
      let val ty = ty_of tm in
        str_of (SOME ty) tm ^ " : " ^ str_of_ty ty
      end
    and str_of _ (NAtom (j, _)) = "@" ^ string_of_int j
      | str_of _ (NConst (id, [], _)) = str_of_ident id
      | str_of (SOME ty0) (NConst (id, tys, ty)) =
        if ty = ty0 then str_of_ident id else str_of_at_const id tys
      | str_of _ (NConst (id, tys, _)) = str_of_at_const id tys
      | str_of _ (NVar (id, _)) = str_of_ident id
      | str_of ty_opt (NAbs (var, body)) =
        "fun " ^
        (case ty_opt of
          SOME ty => str_of (SOME (domain_ty ty))
        | NONE => parens o str_of_tmty) var ^
        ". " ^ str_of (Option.map range_ty ty_opt) body
      | str_of ty_opt (NMatch (obj, branches)) =
        nun_match ^ " " ^ str_of NONE obj ^ " with" ^
        space_implode "" (map (str_of_br ty_opt) branches) ^ " end"
      | str_of ty_opt (app as NApp (func, argN)) =
        (case (func, argN) of
          (NApp (oper as NConst (id, _, _), arg1), arg2) =>
          if id = nun_equals then
            (str_of NONE arg1 |> not (is_triv_head arg1) ? parens) ^ " " ^ id ^ " " ^
            (str_of (try ty_of arg2) arg2 |> not (is_triv_head arg2) ? parens)
          else if is_nun_const_connective id then
            let
              val ty_opt' = SOME nun_prop_ty;
              val args = dest_rassoc_args oper arg1 arg2;
            in
              space_implode (" " ^ id ^ " ")
                (map (fn arg => str_of NONE arg |> not (is_triv_head arg) ? parens) args)
            end
          else
            str_of_app ty_opt func argN
        | (NApp (NApp (oper as NConst (id, _, _), arg1), arg2), arg3) =>
          if id = nun_if then
            nun_if ^ " " ^ str_of NONE arg1 ^ " then " ^ str_of NONE arg2 ^ " else " ^
            str_of NONE arg3
            |> parens
          else
            str_of_app ty_opt func argN
        | (NConst (id, _, _), NAbs _) =>
          if is_nun_const_quantifier id then
            let val (vars, body) = strip_nun_binders id app in
              id ^ " " ^ space_implode " " (map (parens o str_of_tmty) vars) ^ ". " ^
              str_of NONE body
            end
          else
            str_of_app ty_opt func argN
        | _ => str_of_app ty_opt func argN);
  in
    (str_of_tmty, str_of NONE)
  end;

val empty_name_pool = {nice_of_ugly = Symtab.empty, ugly_of_nice = Symtab.empty};

val nice_of_ugly_suggestion =
  unascii_of #> Long_Name.base_name #> ascii_of #> unsuffix nun_custom_id_suffix
  #> (fn s => if s = "" orelse not (Char.isAlpha (String.sub (s, 0))) then "x" ^ s else s);

fun allocate_nice ({nice_of_ugly, ugly_of_nice} : name_pool) (ugly, nice_sugg0) =
  let
    fun alloc j =
      let val nice_sugg = index_name nice_sugg0 j in
        (case Symtab.lookup ugly_of_nice nice_sugg of
          NONE =>
          (nice_sugg,
           {nice_of_ugly = Symtab.update_new (ugly, nice_sugg) nice_of_ugly,
            ugly_of_nice = Symtab.update_new (nice_sugg, ugly) ugly_of_nice})
        | SOME _ => alloc (j + 1))
      end;
  in
    alloc 0
  end;

fun nice_ident ugly (pool as {nice_of_ugly, ...}) =
  if String.isSuffix nun_custom_id_suffix ugly then
    (case Symtab.lookup nice_of_ugly ugly of
      NONE => allocate_nice pool (ugly, nice_of_ugly_suggestion ugly)
    | SOME nice => (nice, pool))
  else
    (ugly, pool);

fun nice_nun_problem problem =
  fold_map_nun_problem_idents nice_ident problem empty_name_pool;

fun str_of_tval (NType (id, tys)) =
    str_of_ident id ^ " : " ^ fold (K (prefix (nun_type ^ " " ^ nun_fun ^ " "))) tys nun_type
  | str_of_tval _ = raise Fail "non-NType";

fun is_triv_wrt (NAbs (_, body)) = is_triv_wrt body
  | is_triv_wrt (NConst (id, _, _)) = (id = nun_true)
  | is_triv_wrt _ = false;

fun str_of_nun_type_spec {abs_ty, rep_ty, wrt, abs, rep} =
  str_of_ty abs_ty ^ " := " ^ str_of_ty rep_ty ^
  (if is_triv_wrt wrt then "" else "\n  wrt " ^ str_of_tm wrt) ^
  "\n  abs " ^ str_of_tm abs ^
  "\n  rep " ^ str_of_tm rep;

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
  | str_of_nun_command (NPred (wf, specs)) =
    "pred " ^ (if wf then "[wf] " else "") ^ str_of_and_list str_of_nun_const_spec specs
  | str_of_nun_command (NCopred specs) = "copred " ^ str_of_and_list str_of_nun_const_spec specs
  | str_of_nun_command (NRec specs) = "rec " ^ str_of_and_list str_of_nun_const_spec specs
  | str_of_nun_command (NSpec spec) = "spec " ^ str_of_nun_consts_spec spec
  | str_of_nun_command (NAxiom tm) = "axiom " ^ str_of_tm tm
  | str_of_nun_command (NGoal tm) = "goal " ^ str_of_tm tm
  | str_of_nun_command (NEval tm) = "eval " ^ str_of_tm tm;

val str_of_nun_problem =
  map (cat_lines o map (suffix "." o str_of_nun_command))
  #> space_implode "\n\n" #> suffix "\n";

end;
