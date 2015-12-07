(*  Title:      HOL/Tools/Nunchaku/nunchaku_collect.ML
    Author:     Jasmin Blanchette, Inria Nancy, LORIA, MPII
    Copyright   2015

Collection of Isabelle/HOL definitions etc. for Nunchaku.
*)

signature NUNCHAKU_COLLECT =
sig
  type fp_kind = BNF_Util.fp_kind

  type isa_co_data_spec =
    {typ: typ,
     ctrs: term list}

  type isa_func_spec =
    {func: term,
     props: term list}

  type isa_spec_spec =
    {funcs: term list,
     props: term list}

  datatype isa_command =
    ITypedecl of typ
  | ICopy of typ * term
  | IQuotient of typ * term
  | ICoData of fp_kind * isa_co_data_spec list
  | IConst of term
  | ICoPred of fp_kind * isa_func_spec list
  | IRec of isa_func_spec list
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

type fp_kind = BNF_Util.fp_kind;

type isa_co_data_spec =
  {typ: typ,
   ctrs: term list};

type isa_func_spec =
  {func: term,
   props: term list};

type isa_spec_spec =
  {funcs: term list,
   props: term list};

datatype isa_command =
  ITypedecl of typ
| ICopy of typ * term
| IQuotient of typ * term
| ICoData of fp_kind * isa_co_data_spec list
| IConst of term
| ICoPred of fp_kind * isa_func_spec list
| IRec of isa_func_spec list
| ISpec of isa_spec_spec
| IAxiom of term
| IGoal of term;

type isa_problem = isa_command list list;

val key_of_typ =
  let
    fun key_of (Type (s, [])) = s
      | key_of (Type (s, Ts)) = s ^ "(" ^ commas (map key_of Ts) ^ ")"
      | key_of (TFree (s, _)) = s
  in
    prefix "y" o key_of
  end;

fun key_of_func ctxt =
  let
    val thy = Proof_Context.theory_of ctxt;

    fun key_of (Const (x as (s, _))) =
        (case Sign.const_typargs thy x of
          [] => s
        | Ts => s ^ "(" ^ commas (map key_of_typ Ts) ^ ")")
      | key_of (Free (s, _)) = s;
  in
    prefix "t" o key_of
  end;

val add_type_keys = fold_subtypes (insert (op =) o key_of_typ);

fun add_func_keys ctxt =
  fold_aterms (fn t =>
    if is_Const t orelse is_Free t then insert (op =) (key_of_func ctxt t) else I);

fun atomize_towards_False ctxt t =
  let
    val t' = t
      |> attach_typeS
      |> Object_Logic.atomize_term ctxt;
  in
    if fastype_of t' = HOLogic.boolT then t' else @{const False}
  end;

fun close_form t =
  fold (fn ((s, i), T) => fn t' =>
      HOLogic.all_const T $ Abs (s, T, abstract_over (Var ((s, i), T), t')))
    (Term.add_vars t []) t;

val basic_defs =
  @{thms Ex1_def Let_def} @ map (fn th => th RS @{thm eq_reflection}) @{thms Ball_def Bex_def};

fun unfold_basic_def ctxt =
  let val thy = Proof_Context.theory_of ctxt in
    Pattern.rewrite_term thy (map (Logic.dest_equals o Thm.prop_of) basic_defs) []
  end;

fun preprocess_prop ctxt =
  atomize_towards_False ctxt #> unfold_basic_def ctxt #> close_form;

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

    fun is_right_spec class (class', (ts, _)) =
      class' = class andalso exists (fn t => Pattern.matches thy (t, const)) ts;

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
           else if null props then SOME (false, [const], [])
           else SOME (is_rec, ts, props)
         end
         handle Type.TYPE_MATCH => NONE)
      | NONE => NONE);

    val specs = Spec_Rules.retrieve ctxt const;
  in
    (case find_first (is_right_spec Spec_Rules.Equational) specs of
      SOME (_, spec) => process_spec true spec
    | NONE =>
      (case find_first (is_right_spec Spec_Rules.Unknown) specs of
        SOME (_, spec) => process_spec false spec
      | NONE => NONE))
  end;

val is_type_builtin = member (op =) [@{type_name bool}, @{type_name fun}, @{type_name set}];

val is_const_builtin =
  member (op =) [@{const_name All}, @{const_name Collect}, @{const_name conj}, @{const_name disj},
    @{const_name HOL.eq}, @{const_name Ex}, @{const_name False}, @{const_name If},
    @{const_name implies}, @{const_name Set.member}, @{const_name Not}, @{const_name True}];

fun is_term_builtin (Const (s, _)) = is_const_builtin s
  | is_term_builtin _ = false;

fun keys_of _ (ITypedecl T) = [key_of_typ T]
  | keys_of _ (ICopy (T, _)) = [key_of_typ T]
  | keys_of _ (IQuotient (T, _)) = [key_of_typ T]
  | keys_of _ (ICoData (_, specs)) = map (key_of_typ o #typ) specs
  | keys_of ctxt (IConst func) = [key_of_func ctxt func]
  | keys_of ctxt (ICoPred (_, specs)) = map (key_of_func ctxt o #func) specs
  | keys_of ctxt (IRec specs) = map (key_of_func ctxt o #func) specs
  | keys_of ctxt (ISpec {funcs, ...}) = map (key_of_func ctxt) funcs
  | keys_of _ (IAxiom _) = []
  | keys_of _ (IGoal _) = [];

fun co_data_spec_deps_of ({ctrs, ...} : isa_co_data_spec) =
  fold (add_type_keys o fastype_of) ctrs [];
fun func_spec_deps_of ctxt funcs props =
  fold (add_func_keys ctxt) props [] |> subtract (op =) (map (key_of_func ctxt) funcs);
fun spec_spec_deps_of ctxt {funcs, props} =
  fold (add_func_keys ctxt) props [] |> subtract (op =) (map (key_of_func ctxt) funcs);

fun deps_of _ (ITypedecl _) = []
  | deps_of ctxt (ICopy (_, pred)) = add_func_keys ctxt pred []
  | deps_of ctxt (IQuotient (_, rel)) = add_func_keys ctxt rel []
  | deps_of _ (ICoData (_, specs)) = maps co_data_spec_deps_of specs
  | deps_of _ (IConst func) = add_type_keys (fastype_of func) []
  | deps_of ctxt (ICoPred (_, specs)) =
    maps (func_spec_deps_of ctxt (map #func specs) o #props) specs
  | deps_of ctxt (IRec specs) = maps (func_spec_deps_of ctxt (map #func specs) o #props) specs
  | deps_of ctxt (ISpec spec) = spec_spec_deps_of ctxt spec
  | deps_of ctxt (IAxiom prop) = add_func_keys ctxt prop []
  | deps_of ctxt (IGoal prop) = add_func_keys ctxt prop [];

fun funcs_of_rec_or_spec (IRec specs) = map #func specs
  | funcs_of_rec_or_spec (ISpec {funcs, ...}) = funcs;

fun props_of_rec_or_spec (IRec specs) = maps #props specs
  | props_of_rec_or_spec (ISpec {props, ...}) = props;

fun merge_two_rec_or_spec cmd cmd' =
  ISpec {funcs = funcs_of_rec_or_spec cmd @ funcs_of_rec_or_spec cmd',
        props = props_of_rec_or_spec cmd @ props_of_rec_or_spec cmd'};

fun merge_two (ICoData (fp, specs)) (ICoData (fp', specs')) =
    ICoData (BNF_Util.case_fp fp fp fp', specs @ specs')
  | merge_two (IRec specs) (IRec specs') = IRec (specs @ specs')
  | merge_two (cmd as IRec _) (cmd' as ISpec _) = merge_two_rec_or_spec cmd cmd'
  | merge_two (cmd as ISpec _) (cmd' as IRec _) = merge_two_rec_or_spec cmd cmd'
  | merge_two (cmd as ISpec _) (cmd' as ISpec _) = merge_two_rec_or_spec cmd cmd'
  | merge_two cmd cmd' = raise Fail "cannot merge mutually dependent commands";

fun sort_isa_problem_topologically ctxt cmds =
  let
    fun normal_pairs [] = []
      | normal_pairs (all as normal :: others) = map (rpair normal) all;

    fun add_node [] _ = I
      | add_node (normal :: _) cmd = Graph.new_node (normal, cmd);

    fun merge_scc (cmd :: cmds) = fold merge_two cmds cmd;

    fun sort_prob cmds =
      let
        val keyss = map (keys_of ctxt) cmds;
        val normal_keys = Symtab.make (maps normal_pairs keyss);
        val normalize = Symtab.lookup normal_keys;

        fun add_deps [] _ = I
          | add_deps (normal :: _) cmd =
            let
              val deps = deps_of ctxt cmd
                |> map_filter normalize
                |> remove (op =) normal;
            in
              fold (fn dep => Graph.add_edge (dep, normal)) deps
            end;

        val cmd_of_key = the o AList.lookup (op =) (map hd keyss ~~ cmds);

        val G = Graph.empty
          |> fold2 add_node keyss cmds
          |> fold2 add_deps keyss cmds;

        val cmd_sccs = rev (Graph.strong_conn G)
          |> map (map cmd_of_key);
      in
        if exists (can (fn _ :: _ :: _ => ())) cmd_sccs then sort_prob (map merge_scc cmd_sccs)
        else Graph.schedule (K snd) G
      end;

    val typedecls = filter (can (fn ITypedecl _ => ())) cmds;
    val mixed =
      filter (can (fn ICoData _ => () | IConst _ => () | ICoPred _ => () | IRec _ => ()
        | ISpec _ => ())) cmds
      |> sort_prob;
    val axioms = filter (can (fn IAxiom _ => ())) cmds;
    val goals = filter (can (fn IGoal _ => ())) cmds;
  in
    typedecls @ mixed @ axioms @ goals
  end;

fun group_of (ITypedecl _) = 1
  | group_of (ICopy _) = 2
  | group_of (IQuotient _) = 3
  | group_of (ICoData _) = 4
  | group_of (IConst _) = 5
  | group_of (ICoPred _) = 6
  | group_of (IRec _) = 7
  | group_of (ISpec _) = 8
  | group_of (IAxiom _) = 9
  | group_of (IGoal _) = 10;

fun group_isa_commands [] = []
  | group_isa_commands [cmd] = [[cmd]]
  | group_isa_commands (cmd :: cmd' :: cmds) =
    let val (group :: groups) = group_isa_commands (cmd' :: cmds) in
      if group_of cmd = group_of cmd' then
        (cmd :: group) :: groups
      else
        [cmd] :: (group :: groups)
    end;

(* Prevents divergence in case of cyclic or infinite axiom dependencies. *)
val axioms_max_depth = 255

fun isa_problem_of_goal ctxt goal0 =
  let
    fun consider_sort depth T S = I;

    fun consider_type depth T =
      (case T of
        Type (s, Ts) =>
        if is_type_builtin s then fold (consider_type depth) Ts
        else consider_non_builtin_type depth T
      | _ => consider_non_builtin_type depth T)
    and consider_non_builtin_type depth T (seens as (seenS, seenT, seen), prob) =
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
                       val co_data = ICoData (fp,
                         map2 (fn T => fn ctrs => {typ = T, ctrs = ctrs}) dataTs ctrss);

                       val prob = co_data :: prob;
                     in
                       ((seenS, union (op =) dataTs seenT, seen), prob)
                       |> fold (fold (consider_type (depth + 1) o fastype_of)) ctrss
                     end)
               | NONE => (fn (seen, prob) => (seen, ITypedecl T :: prob))))
            (seens, prob)
        end;

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

                         fun partition_props props =
                           if length funcs = 1 then
                             SOME [props]
                           else
                             let
                               fun props_of_func func =
                                 filter (fn prop => head_of_def_lhs prop aconv func) props;

                               val propss = map props_of_func funcs;
                             in
                               if eq_set (op aconv) (props, flat propss) andalso
                                  forall (not o null) propss then
                                SOME propss
                              else
                                NONE
                             end;

                         val cmds =
                           if null props then
                             map IConst funcs
                           else if is_rec then
                             (case partition_props props of
                               SOME propss =>
                               [IRec (map2 (fn func => fn props => {func = func, props = props})
                                  funcs propss)]
                             | NONE => [ISpec {funcs = funcs, props = props}])
                           else
                             [ISpec {funcs = funcs, props = props}];

                         val prob = cmds @ prob;
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
    |> sort_isa_problem_topologically ctxt
    |> group_isa_commands
  end;

fun str_of_isa_term_with_type ctxt t =
  Syntax.string_of_term ctxt t ^ " : " ^ Syntax.string_of_typ ctxt (fastype_of t);

fun str_of_isa_co_data_spec ctxt {typ, ctrs} =
  Syntax.string_of_typ ctxt typ ^ " =\n  " ^
  space_implode "\n| " (map (str_of_isa_term_with_type ctxt) ctrs);

fun str_of_isa_func_spec ctxt {func, props} =
  str_of_isa_term_with_type ctxt func ^ " :=\n  " ^
  space_implode ";\n  " (map (Syntax.string_of_term ctxt) props);

fun str_of_isa_spec_spec ctxt {funcs, props} =
  space_implode " and\n     " (map (str_of_isa_term_with_type ctxt) funcs) ^ " :=\n  " ^
  space_implode ";\n  " (map (Syntax.string_of_term ctxt) props);

fun str_of_isa_command ctxt (ITypedecl T) = "typedecl " ^ Syntax.string_of_typ ctxt T
  | str_of_isa_command ctxt (ICopy (T, pred)) =
    "copy " ^ Syntax.string_of_typ ctxt T ^ " := " ^ Syntax.string_of_term ctxt pred
  | str_of_isa_command ctxt (IQuotient (T, rel)) =
    "quotient " ^ Syntax.string_of_typ ctxt T ^ " := " ^ Syntax.string_of_term ctxt rel
  | str_of_isa_command ctxt (ICoData (fp, specs)) =
    BNF_Util.case_fp fp "data" "codata" ^ " " ^ str_of_and_list (str_of_isa_co_data_spec ctxt) specs
  | str_of_isa_command ctxt (IConst t) = "const " ^ str_of_isa_term_with_type ctxt t
  | str_of_isa_command ctxt (ICoPred (fp, specs)) =
    BNF_Util.case_fp fp "induct" "coinduct" ^ " " ^
    str_of_and_list (str_of_isa_func_spec ctxt) specs
  | str_of_isa_command ctxt (IRec specs) =
    "rec " ^ str_of_and_list (str_of_isa_func_spec ctxt) specs
  | str_of_isa_command ctxt (ISpec spec) = "spec " ^ str_of_isa_spec_spec ctxt spec
  | str_of_isa_command ctxt (IAxiom t) = "axiom " ^ Syntax.string_of_term ctxt t
  | str_of_isa_command ctxt (IGoal t) = "goal " ^ Syntax.string_of_term ctxt t;

fun str_of_isa_problem ctxt =
  map (cat_lines o map (suffix "." o str_of_isa_command ctxt))
  #> space_implode "\n\n"
  #> suffix "\n";

end;
