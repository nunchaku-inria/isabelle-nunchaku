(*  Title:      HOL/Tools/Nunchaku/nunchaku_collect.ML
    Author:     Jasmin Blanchette, Inria Nancy, LORIA, MPII
    Copyright   2015

Collection of Isabelle/HOL definitions etc. for Nunchaku.
*)

signature NUNCHAKU_COLLECT =
sig
  type isa_co_data_spec =
    {typ: typ,
     ctrs: term list}

  type isa_rec_spec =
    {func: term,
     eqs: term list}

  type isa_spec_spec =
    {funcs: term list,
     props: term list}

  datatype isa_command =
    ITypedecl of typ
  | IData of isa_co_data_spec list
  | ICodata of isa_co_data_spec list
  | IConst of term
  | IRec of isa_rec_spec list
  | ISpec of isa_spec_spec
  | IAxiom of term
  | IGoal of term

  type isa_problem = isa_command list list

  val isa_problem_of_goal: Proof.context -> term -> isa_problem
  val str_of_isa_problem: Proof.context -> isa_problem -> string
end;

structure Nunchaku_Collect : NUNCHAKU_COLLECT =
struct

open Nunchaku_Util;

type isa_co_data_spec =
  {typ: typ,
   ctrs: term list};

type isa_rec_spec =
  {func: term,
   eqs: term list};

type isa_spec_spec =
  {funcs: term list,
   props: term list};

datatype isa_command =
  ITypedecl of typ
| IData of isa_co_data_spec list
| ICodata of isa_co_data_spec list
| IConst of term
| IRec of isa_rec_spec list
| ISpec of isa_spec_spec
| IAxiom of term
| IGoal of term;

type isa_problem = isa_command list list;

fun key_of_typ (Type (s, [])) = s
  | key_of_typ (Type (s, Ts)) = s ^ "(" ^ commas (map key_of_typ Ts) ^ ")"
  | key_of_typ (TFree (s, _)) = s;

fun key_of_func (Const (s, T)) = s ^ "(" ^ key_of_typ T ^ ")"
  | key_of_func (Free (s, _)) = s;

val add_type_keys = fold_subtypes (insert (op =) o key_of_typ);
val add_func_keys =
  fold_aterms (fn t => if is_Const t orelse is_Free t then insert (op =) (key_of_func t) else I);

fun atomize_toward_False ctxt t =
  let val t' = Object_Logic.atomize_term ctxt t in
    if fastype_of t' = HOLogic.boolT then t' else @{const False}
  end;

fun close_form t =
  fold (fn ((s, i), T) => fn t' =>
      HOLogic.all_const T $ Abs (s, T, abstract_over (Var ((s, i), T), t')))
    (Term.add_vars t []) t;

fun preprocess_prop ctxt = atomize_toward_False ctxt #> close_form;

fun mutual_co_datatypes_of ctxt T_name =
  (case BNF_FP_Def_Sugar.fp_sugar_of ctxt T_name of
    SOME (fp_sugar as {fp, fp_res = {Ts, ...}, ...}) =>
    SOME (fp,
      (case Ts of
        [_] => [fp_sugar]
      | _ => map (the o BNF_FP_Def_Sugar.fp_sugar_of ctxt o fst o dest_Type) Ts)
      |> map (#ctr_sugar o #fp_ctr_sugar))
  | NONE =>
    (case Ctr_Sugar.ctr_sugar_of ctxt T_name of
      SOME (ctr_sugar as {kind, ...}) =>
      (* Any freely constructed type that is not a codatatype is considered a datatype. This is
         sound (but incomplete) for model finding. *)
      SOME (if kind = Ctr_Sugar.Codatatype then BNF_Util.Greatest_FP else BNF_Util.Least_FP,
        [ctr_sugar])
    | NONE => NONE));

fun is_co_datatype_ctr ctxt (s, T) =
  (case body_type T of
    dataT as Type (dataT_name, Ts) =>
    let
      fun is_right_ctr (t' as Const (s', T')) =
        s = s' andalso fastype_of (Ctr_Sugar.mk_ctr Ts t') = T;

      val ctrs =
        (case Ctr_Sugar.ctr_sugar_of ctxt dataT_name of
          SOME {ctrs, ...} => ctrs
        | _ => []);
    in
      exists is_right_ctr ctrs
    end
  | _  => false);

fun head_of_def_lhs (Const (@{const_name HOL.eq}, _) $ t $ _) = head_of t
  | head_of_def_lhs t = head_of t;

fun instantiate_constant_type_in_term ctxt const target =
  let
    val thy = Proof_Context.theory_of ctxt;

    fun subst_for (Const (s', T')) =
        (case const of
          Const (s, T) =>
          if s = s' then
            SOME (Sign.typ_match thy (T', T) Vartab.empty)
            handle Type.TYPE_MATCH => NONE
          else
            NONE
        | _ => NONE)
      | subst_for (t as Free _) = if t = const then SOME Vartab.empty else NONE
      | subst_for (t1 $ t2) = (case subst_for t1 of SOME subst => SOME subst | NONE => subst_for t2)
      | subst_for (Abs (_, _, t')) = subst_for t'
      | subst_for _ = NONE;
  in
    (case subst_for target of
      SOME subst => Envir.subst_term_types subst target
    | NONE => raise Type.TYPE_MATCH)
  end;

fun mutual_recs_or_spec_of ctxt const =
  let
    val thy = Proof_Context.theory_of ctxt;

    val const_T = fastype_of const;

    fun subst_of t0 =
      try (Sign.typ_match thy (fastype_of t0, const_T)) Vartab.empty;

    fun process_spec is_rec (ts0, ths) =
      (case get_first subst_of ts0 of
        SOME subst =>
        (let
           val ts = map (Envir.subst_term_types subst) ts0;
           val props = map (instantiate_constant_type_in_term ctxt const o Thm.prop_of) ths;
         in
           if exists (exists (exists_type (exists_subtype is_TVar))) [ts, props] then NONE
           else SOME (is_rec, ts, props)
         end
         handle Type.TYPE_MATCH => NONE)
      | NONE => NONE);

    val specs = Spec_Rules.retrieve ctxt const;
  in
    (case find_first (fn (class, _) => class = Spec_Rules.Equational) specs of
      SOME (_, spec) => process_spec true spec
    | NONE =>
      (case find_first (fn (class, _) => class = Spec_Rules.Unknown (* risky *)) specs of
        SOME (_, spec) => process_spec false spec
      | NONE => NONE))
  end;

val is_typ_builtin = member (op =) [@{type_name bool}, @{type_name fun}];

val is_const_builtin =
  member (op =) [@{const_name All}, @{const_name conj}, @{const_name disj}, @{const_name HOL.eq},
    @{const_name Ex}, @{const_name False}, @{const_name implies}, @{const_name Not},
    @{const_name True}];

fun co_data_spec_key_of ({typ, ...} : isa_co_data_spec) = key_of_typ typ;

fun rec_spec_key_of ({func, ...} : isa_rec_spec) = key_of_func func;
fun spec_spec_keys_of ({funcs, ...} : isa_spec_spec) = map key_of_func funcs;

fun co_data_keys_of (IData specs) = map co_data_spec_key_of specs
  | co_data_keys_of (ICodata specs) = map co_data_spec_key_of specs
  | co_data_keys_of _ = [];

fun rec_or_spec_keys_of (IRec specs) = map rec_spec_key_of specs
  | rec_or_spec_keys_of (ISpec spec) = spec_spec_keys_of spec
  | rec_or_spec_keys_of _ = [];

fun co_data_spec_deps_of ({ctrs, ...} : isa_co_data_spec) =
  fold (add_type_keys o fastype_of) ctrs [];

fun rec_spec_deps_of ({eqs, ...} : isa_rec_spec) = fold add_func_keys eqs [];
fun spec_spec_deps_of ({props, ...} : isa_spec_spec) = fold add_func_keys props [];

fun co_data_deps_of (IData specs) = maps co_data_spec_deps_of specs
  | co_data_deps_of (ICodata specs) = maps co_data_spec_deps_of specs
  | co_data_deps_of _ = [];

fun rec_or_spec_deps_of (IRec specs) = maps rec_spec_deps_of specs
  | rec_or_spec_deps_of (ISpec spec) = spec_spec_deps_of spec
  | rec_or_spec_deps_of _ = [];

fun sort_isa_subproblem_topologically keys_of deps_of cmds =
  let
    fun normal_pairs [] = []
      | normal_pairs (all as normal :: others) = map (rpair normal) all;

    val keyss = map keys_of cmds;
    val normal_keys = Symtab.make (maps normal_pairs keyss);
    val normalize = Symtab.lookup normal_keys;

    fun add_node [] _ = I
      | add_node (normal :: _) cmd = Graph.new_node (normal, cmd);

    fun add_deps [] _ = I
      | add_deps (normal :: _) cmd =
        let
          val deps = deps_of cmd
            |> map_filter normalize
            |> remove1 (op =) normal;
        in
          Graph.add_deps_acyclic (normal, deps)
        end;

    val G = Graph.empty
      |> fold2 add_node keyss cmds
      |> fold2 add_deps keyss cmds;
  in
    Graph.schedule (K snd) G
  end;

fun sort_and_group_isa_problem cmds =
  let
    val typedecls = filter (can (fn ITypedecl _ => ())) cmds;
    val co_datas = filter (can (fn IData _ => () | ICodata _ => ())) cmds
      |> sort_isa_subproblem_topologically co_data_keys_of co_data_deps_of;
    val consts = filter (can (fn IConst _ => ())) cmds;
    val recs_specs = filter (can (fn IRec _ => () | ISpec _ => ())) cmds
      |> sort_isa_subproblem_topologically rec_or_spec_keys_of rec_or_spec_deps_of;
    val axioms = filter (can (fn IAxiom _ => ())) cmds;
    val goals = filter (can (fn IGoal _ => ())) cmds;
  in
    [typedecls, co_datas, consts, recs_specs, axioms, goals]
    |> filter_out null
  end;

(* Prevents divergence in case of cyclic or infinite axiom dependencies. *)
val axioms_max_depth = 255

fun isa_problem_of_goal ctxt goal0 =
  let
    fun consider_sort depth T S = I;

    fun consider_type depth T =
      (case T of
        Type (@{type_name fun}, Ts) => fold (consider_type depth) Ts
      | @{typ prop} => I
      | @{typ bool} => I
      | _ =>
        (fn (seens as (seenS, seenT, seen), prob) =>
            if member (op =) seenT T then
              (seens, prob)
            else
              let
                val seenT = T :: seenT;
                val seens = (seenS, seenT, seen);
              in
                (case T of
                  TFree (_, S) =>
                  (fn (seen, prob) =>
                      (seen, ITypedecl T :: prob)
                      |> consider_sort depth T S)
                | TVar (_, S) => consider_sort depth T S
                | Type (s, Ts) =>
                  fold (consider_type depth) Ts
                  #> (case mutual_co_datatypes_of ctxt s of
                       SOME (fp, ctr_sugars) =>
                       (fn ((seenS, seenT, seen), prob) =>
                           let
                             val dataTs = map ((fn Type (s, _) => Type (s, Ts)) o #T) ctr_sugars;
                             val ctrss = map (map (Ctr_Sugar.mk_ctr Ts) o #ctrs) ctr_sugars;
                             val co_data =
                               (case fp of
                                 BNF_Util.Least_FP => IData
                               | BNF_Util.Greatest_FP => ICodata)
                                 (map2 (fn T => fn ctrs => {typ = T, ctrs = ctrs}) dataTs ctrss);

                             val prob = co_data :: prob;
                           in
                             ((seenS, union (op =) dataTs seenT, seen), prob)
                             |> fold (fold (consider_type (depth + 1) o fastype_of)) ctrss
                           end)
                     | NONE => (fn (seen, prob) => (seen, ITypedecl T :: prob))))
                  (seens, prob)
              end));

    fun consider_term depth t =
      (case t of
        t1 $ t2 => fold (consider_term depth) [t1, t2]
      | Var (_, T) => consider_type depth T
      | Bound _ => I
      | Abs (_, T, t') =>
        consider_term depth t'
        #> consider_type depth T
      | _ => (fn (seens as (seenS, seenT, seen), prob) =>
          if member (op aconv) seen t then
            (seens, prob)
          else if depth > axioms_max_depth then
            raise Fail "too many nested axioms"
          else
            let
              val seen = t :: seen;
              val seens = (seenS, seenT, seen);
            in
              (case t of
                Const (x as (s, T)) =>
                (if is_const_builtin s orelse is_co_datatype_ctr ctxt x then
                   (seens, prob)
                 else
                   let val specs = Spec_Rules.retrieve ctxt t in
                     (case mutual_recs_or_spec_of ctxt t of
                       SOME (is_rec, funcs, props0) =>
                       let
                         val props = map (preprocess_prop ctxt) props0;

                         fun partition_eqs eqs =
                           if length funcs = 1 then
                             SOME [eqs]
                           else
                             let
                               fun eqs_of_func func =
                                 filter (fn prop => head_of_def_lhs prop aconv func) props;

                               val eqss = map eqs_of_func funcs;
                             in
                               if eq_set (op aconv) (eqs, flat eqss) then SOME eqss else NONE
                             end;

                         val rec_or_spec =
                           (if is_rec then
                              (case partition_eqs props of
                                SOME eqss =>
                                IRec (map2 (fn func => fn eqs => {func = func, eqs = eqs})
                                  funcs eqss)
                              | NONE => ISpec {funcs = funcs, props = props})
                            else
                              ISpec {funcs = funcs, props = props});

                         val prob = rec_or_spec :: prob;
                       in
                         ((seenS, seenT, union (op aconv) funcs seen), prob)
                         |> fold (consider_term (depth + 1)) props
                       end
                     | NONE => (seens, IConst t :: prob))
                   end)
                |> consider_type depth T
              | Free (_, T) =>
                (seens, IConst t :: prob)
                |> consider_type depth T)
            end));

    val goal = preprocess_prop ctxt goal0;
  in
    (([], [], []), [IGoal goal])
    |> consider_term 0 goal
    |> snd
    |> rev (* prettier *)
    |> sort_and_group_isa_problem
  end;

fun str_of_isa_term_with_type ctxt t =
  Syntax.string_of_term ctxt t ^ " : " ^ Syntax.string_of_typ ctxt (fastype_of t);

fun str_of_isa_co_data_spec ctxt {typ, ctrs} =
  Syntax.string_of_typ ctxt typ ^ " =\n  " ^
  space_implode "\n| " (map (str_of_isa_term_with_type ctxt) ctrs);

fun str_of_isa_rec_spec ctxt {func, eqs} =
  str_of_isa_term_with_type ctxt func ^ " :=\n  " ^
  space_implode ";\n  " (map (Syntax.string_of_term ctxt) eqs);

fun str_of_isa_spec_spec ctxt {funcs, props} =
  space_implode " and " (map (str_of_isa_term_with_type ctxt) funcs) ^ " :=\n" ^
  space_implode ";\n  " (map (Syntax.string_of_term ctxt) props);

fun str_of_isa_command ctxt (ITypedecl T) = "typedecl " ^ Syntax.string_of_typ ctxt T
  | str_of_isa_command ctxt (IData specs) =
    "data " ^ str_of_and_list (str_of_isa_co_data_spec ctxt) specs
  | str_of_isa_command ctxt (ICodata specs) = 
    "data " ^ str_of_and_list (str_of_isa_co_data_spec ctxt) specs
  | str_of_isa_command ctxt (IConst t) = "const " ^ str_of_isa_term_with_type ctxt t
  | str_of_isa_command ctxt (IRec specs) = "rec " ^ str_of_and_list (str_of_isa_rec_spec ctxt) specs
  | str_of_isa_command ctxt (ISpec spec) = "spec " ^ str_of_isa_spec_spec ctxt spec
  | str_of_isa_command ctxt (IAxiom t) = "axiom " ^ Syntax.string_of_term ctxt t
  | str_of_isa_command ctxt (IGoal t) = "goal " ^ Syntax.string_of_term ctxt t;

fun str_of_isa_problem ctxt =
  map (cat_lines o map (suffix "." o str_of_isa_command ctxt))
  #> space_implode "\n\n"
  #> suffix "\n";

end;
