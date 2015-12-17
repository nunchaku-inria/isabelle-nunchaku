(*  Title:      HOL/Tools/Nunchaku/nunchaku_collect.ML
    Author:     Jasmin Blanchette, Inria Nancy, LORIA, MPII
    Copyright   2015

Collecting of Isabelle/HOL definitions etc. for Nunchaku.
*)

signature NUNCHAKU_COLLECT =
sig
  val dest_co_datatype_case: Proof.context -> string * typ -> (string * typ) list

  type isa_type_spec =
    {abs_typ: typ,
     rep_typ: typ,
     wrt: term,
     abs: term,
     rep: term}

  type isa_co_data_spec =
    {typ: typ,
     ctrs: term list}

  type isa_const_spec =
    {const: term,
     props: term list}

  type isa_consts_spec =
    {consts: term list,
     props: term list}

  datatype isa_command =
    ITVal of typ
  | ICopy of isa_type_spec
  | IQuotient of isa_type_spec
  | ICoData of BNF_Util.fp_kind * isa_co_data_spec list
  | IVal of term
  | ICoPred of BNF_Util.fp_kind * isa_const_spec list
  | IRec of isa_const_spec list
  | ISpec of isa_consts_spec
  | IAxiom of term
  | IGoal of term

  type isa_problem = isa_command list list

  val isa_problem_of_goal: Proof.context -> bool -> term -> isa_problem
  val str_of_isa_problem: Proof.context -> isa_problem -> string
end;

structure Nunchaku_Collect : NUNCHAKU_COLLECT =
struct

open Nunchaku_Util;

type isa_type_spec =
  {abs_typ: typ,
   rep_typ: typ,
   wrt: term,
   abs: term,
   rep: term};

type isa_co_data_spec =
  {typ: typ,
   ctrs: term list};

type isa_const_spec =
  {const: term,
   props: term list};

type isa_consts_spec =
  {consts: term list,
   props: term list};

datatype isa_command =
  ITVal of typ
| ICopy of isa_type_spec
| IQuotient of isa_type_spec
| ICoData of BNF_Util.fp_kind * isa_co_data_spec list
| IVal of term
| ICoPred of BNF_Util.fp_kind * isa_const_spec list
| IRec of isa_const_spec list
| ISpec of isa_consts_spec
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

fun key_of_const ctxt =
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

fun add_aterm_keys ctxt t =
  if is_Const t orelse is_Free t then insert (op =) (key_of_const ctxt t) else I;

fun add_keys ctxt t =
  fold_aterms (add_aterm_keys ctxt) t
  #> fold_types add_type_keys t;

fun atomize_and_maybe_falsify ctxt falsify t =
  let
    val t' = t
      |> attach_typeS
      |> Object_Logic.atomize_term ctxt;
  in
    if fastype_of t' = HOLogic.boolT then t' |> falsify ? HOLogic.mk_not else @{const False}
  end;

fun close_form t =
  fold (fn ((s, i), T) => fn t' =>
      HOLogic.all_const T $ Abs (s, T, abstract_over (Var ((s, i), T), t')))
    (Term.add_vars t []) t;

val basic_defs =
  @{thms Ex1_def Let_def} @
  map (fn th => th RS @{thm eq_reflection}) @{thms Ball_def Bex_def rmember_def[symmetric]};

fun unfold_basic_def ctxt =
  let val thy = Proof_Context.theory_of ctxt in
    Pattern.rewrite_term thy (map (Logic.dest_equals o Thm.prop_of) basic_defs) []
  end;

fun preprocess_prop falsify ctxt =
  atomize_and_maybe_falsify ctxt falsify
  #> unfold_basic_def ctxt
  #> close_form;

datatype type_classification = TVal | Copy | Quotient | Co_Datatype;

fun classify_type_name ctxt T_name =
  (case BNF_FP_Def_Sugar.fp_sugar_of ctxt T_name of
    SOME _ => Co_Datatype
  | NONE =>
    (case Ctr_Sugar.ctr_sugar_of ctxt T_name of
      SOME _ => Co_Datatype
    | NONE =>
      (case Quotient_Info.lookup_quotients ctxt T_name of
        SOME _ => Quotient
      | NONE =>
        if T_name = @{type_name set} then
          Copy
        else
          (case Typedef.get_info ctxt T_name of
            _ :: _ => Copy
          | [] => TVal))));

fun fp_kind_of_ctr_sugar_kind Ctr_Sugar.Codatatype = BNF_Util.Greatest_FP
  | fp_kind_of_ctr_sugar_kind _ = BNF_Util.Least_FP;

fun mutual_co_datatypes_of ctxt T_name =
  (case BNF_FP_Def_Sugar.fp_sugar_of ctxt T_name of
    SOME (fp_sugar as {fp, fp_res = {Ts, ...}, ...}) =>
    (fp,
     (case Ts of
       [_] => [fp_sugar]
     | _ => map (the o BNF_FP_Def_Sugar.fp_sugar_of ctxt o fst o dest_Type) Ts)
     |> map (#ctr_sugar o #fp_ctr_sugar))
  | NONE =>
    (case Ctr_Sugar.ctr_sugar_of ctxt T_name of
      SOME (ctr_sugar as {kind, ...}) =>
      (* Any freely constructed type that is not a codatatype is considered a datatype. This is
         sound (but incomplete) for model finding. *)
      (fp_kind_of_ctr_sugar_kind kind, [ctr_sugar])));

fun quotient_of ctxt T_name =
  (case Quotient_Info.lookup_quotients ctxt T_name of
    SOME {equiv_rel, qtyp, rtyp, quot_thm, ...} =>
    let val _ $ (_ $ _ $ abs $ rep) = Thm.prop_of quot_thm in
      (qtyp, rtyp, equiv_rel, abs, rep)
    end);

fun copy_of ctxt T_name =
  if T_name = @{type_name set} then
    let
      val A = Logic.varifyT_global @{typ 'a};
      val absT = Type (@{type_name set}, [A]);
      val repT = A --> HOLogic.boolT;
      val wrt = Abs (Name.uu, repT, @{const True});
      val abs = Const (@{const_name Collect}, repT --> absT);
      val rep = Const (@{const_name rmember}, absT --> repT);
    in
      (absT, repT, wrt, abs, rep)
    end
  else
    (case Typedef.get_info ctxt T_name of
      (* When several entries are returned, it shouldn't matter much which one we take (according to
         Florian Haftmann). The "Logic.varifyT_global" calls are a workaround because these types'
         variables sometimes clash with locally fixed type variables. *)
      ({abs_type, rep_type, Abs_name, Rep_name, ...}, {Rep, ...}) :: _ =>
      let
        val absT = Logic.varifyT_global abs_type;
        val repT = Logic.varifyT_global rep_type;
        val wrt = Thm.prop_of Rep
          |> HOLogic.dest_Trueprop
          |> HOLogic.dest_mem
          |> snd;
        val abs = Const (Abs_name, repT --> absT);
        val rep = Const (Rep_name, absT --> repT);
      in
        (absT, repT, wrt, abs, rep)
      end);

fun is_co_datatype_ctr ctxt (s, T) =
  (case body_type T of
    Type (fpT_name, Ts) =>
    classify_type_name ctxt fpT_name = Co_Datatype andalso
    let
      val ctrs =
        (case BNF_FP_Def_Sugar.fp_sugar_of ctxt fpT_name of
          SOME {fp_ctr_sugar = {ctr_sugar = {ctrs, ...}, ...}, ...} => ctrs
        | NONE =>
          (case Ctr_Sugar.ctr_sugar_of ctxt fpT_name of
            SOME {ctrs, ...} => ctrs
          | _ => []));

      fun is_right_ctr (t' as Const (s', _)) =
        s = s' andalso fastype_of (Ctr_Sugar.mk_ctr Ts t') = T;
    in
      exists is_right_ctr ctrs
    end
  | _  => false);

fun dest_co_datatype_case ctxt (s, T) =
  let val thy = Proof_Context.theory_of ctxt in
    (case strip_fun_type (Sign.the_const_type thy s) of
      (gen_branch_Ts, gen_body_fun_T) =>
      (case gen_body_fun_T of
        Type (@{type_name fun}, [Type (fpT_name, _), _]) =>
        if classify_type_name ctxt fpT_name = Co_Datatype then
          let
            val Type (_, fpTs) = domain_type (funpow (length gen_branch_Ts) range_type T);
            val (ctrs0, Const (case_name, _)) =
              (case BNF_FP_Def_Sugar.fp_sugar_of ctxt fpT_name of
                SOME {fp_ctr_sugar = {ctr_sugar = {ctrs, casex, ...}, ...}, ...} => (ctrs, casex)
              | NONE =>
                (case Ctr_Sugar.ctr_sugar_of ctxt fpT_name of
                  SOME {ctrs, casex, ...} => (ctrs, casex)));
          in
            if s = case_name then map (dest_Const o Ctr_Sugar.mk_ctr fpTs) ctrs0
            else raise Fail "non-case"
          end
        else
          raise Fail "non-case"))
  end;

val is_co_datatype_case = can o dest_co_datatype_case;

fun is_quotient_abs ctxt (s, T) =
  (case T of
    Type (@{type_name fun}, [_, Type (absT_name, _)]) =>
    classify_type_name ctxt absT_name = Quotient andalso
    (case quotient_of ctxt absT_name of
      (_, _, _, Const (s', _), _) => s' = s)
  | _ => false);

fun is_quotient_rep ctxt (s, T) =
  (case T of
    Type (@{type_name fun}, [Type (absT_name, _), _]) =>
    classify_type_name ctxt absT_name = Quotient andalso
    (case quotient_of ctxt absT_name of
      (_, _, _, _, Const (s', _)) => s' = s)
  | _ => false);

fun is_maybe_copy_abs ctxt absT_name s =
  if absT_name = @{type_name set} then
    s = @{const_name Collect}
  else
    (case try (copy_of ctxt) absT_name of
      SOME (_, _, _, Const (s', _), _) => s' = s
    | NONE => false);

fun is_maybe_copy_rep ctxt absT_name s =
  if absT_name = @{type_name set} then
    s = @{const_name rmember}
  else
    (case try (copy_of ctxt) absT_name of
      SOME (_, _, _, _, Const (s', _)) => s' = s
    | NONE => false);

fun is_copy_abs ctxt (s, T) =
  (case T of
    Type (@{type_name fun}, [_, Type (absT_name, _)]) =>
    classify_type_name ctxt absT_name = Copy andalso is_maybe_copy_abs ctxt absT_name s
  | _ => false);

fun is_copy_rep ctxt (s, T) =
  (case T of
    Type (@{type_name fun}, [Type (absT_name, _), _]) =>
    classify_type_name ctxt absT_name = Copy andalso is_maybe_copy_rep ctxt absT_name s
  | _ => false);

fun is_stale_copy_abs ctxt (s, T) =
  (case T of
    Type (@{type_name fun}, [_, Type (absT_name, _)]) =>
    classify_type_name ctxt absT_name <> Copy andalso is_maybe_copy_abs ctxt absT_name s
  | _ => false);

fun is_stale_copy_rep ctxt (s, T) =
  (case T of
    Type (@{type_name fun}, [Type (absT_name, _), _]) =>
    classify_type_name ctxt absT_name <> Copy andalso is_maybe_copy_rep ctxt absT_name s
  | _ => false);

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

fun int_of_classif Spec_Rules.Equational = 1
  | int_of_classif Spec_Rules.Inductive = 2
  | int_of_classif Spec_Rules.Co_Inductive = 3
  | int_of_classif Spec_Rules.Unknown = 4;

val classif_ord = int_ord o apply2 int_of_classif;

fun spec_rules_of ctxt const =
  let
    val thy = Proof_Context.theory_of ctxt;

    val const_T = fastype_of const;

    fun subst_of t0 =
      try (Sign.typ_match thy (fastype_of t0, const_T)) Vartab.empty;

    fun process_spec _ (res as SOME _) = res
      | process_spec (classif, (ts0, ths)) NONE =
        (case get_first subst_of ts0 of
          SOME subst =>
          (let
             val ts = map (Envir.subst_term_types subst) ts0;
             val props = map (instantiate_constant_type_in_term ctxt const o Thm.prop_of) ths;
           in
             if exists (exists (exists_type (exists_subtype is_TVar))) [ts, props] then NONE
             else SOME (classif, ts, props)
           end
           handle Type.TYPE_MATCH => NONE)
        | NONE => NONE);

    val specs =
      Spec_Rules.retrieve ctxt const
      |> sort (classif_ord o apply2 fst);
  in
    fold process_spec specs NONE
  end;

val is_type_builtin = member (op =) [@{type_name bool}, @{type_name fun}];

val is_const_builtin =
  member (op =) [@{const_name All}, @{const_name conj}, @{const_name disj}, @{const_name HOL.eq},
    @{const_name Ex}, @{const_name False}, @{const_name If}, @{const_name implies},
    @{const_name Not}, @{const_name True}];

fun keys_of _ (ITVal T) = [key_of_typ T]
  | keys_of _ (ICopy {abs_typ, ...}) = [key_of_typ abs_typ]
  | keys_of _ (IQuotient {abs_typ, ...}) = [key_of_typ abs_typ]
  | keys_of _ (ICoData (_, specs)) = map (key_of_typ o #typ) specs
  | keys_of ctxt (IVal const) = [key_of_const ctxt const]
  | keys_of ctxt (ICoPred (_, specs)) = map (key_of_const ctxt o #const) specs
  | keys_of ctxt (IRec specs) = map (key_of_const ctxt o #const) specs
  | keys_of ctxt (ISpec {consts, ...}) = map (key_of_const ctxt) consts
  | keys_of _ (IAxiom _) = []
  | keys_of _ (IGoal _) = [];

fun co_data_spec_deps_of ctxt ({ctrs, ...} : isa_co_data_spec) =
  fold (add_keys ctxt) ctrs [];
fun const_spec_deps_of ctxt consts props =
  fold (add_keys ctxt) props [] |> subtract (op =) (map (key_of_const ctxt) consts);
fun consts_spec_deps_of ctxt {consts, props} =
  fold (add_keys ctxt) props [] |> subtract (op =) (map (key_of_const ctxt) consts);

fun deps_of _ (ITVal _) = []
  | deps_of ctxt (ICopy {wrt, ...}) = add_keys ctxt wrt []
  | deps_of ctxt (IQuotient {wrt, ...}) = add_keys ctxt wrt []
  | deps_of ctxt (ICoData (_, specs)) = maps (co_data_spec_deps_of ctxt) specs
  | deps_of _ (IVal const) = add_type_keys (fastype_of const) []
  | deps_of ctxt (ICoPred (_, specs)) =
    maps (const_spec_deps_of ctxt (map #const specs) o #props) specs
  | deps_of ctxt (IRec specs) = maps (const_spec_deps_of ctxt (map #const specs) o #props) specs
  | deps_of ctxt (ISpec spec) = consts_spec_deps_of ctxt spec
  | deps_of ctxt (IAxiom prop) = add_keys ctxt prop []
  | deps_of ctxt (IGoal prop) = add_keys ctxt prop [];

fun consts_of_rec_or_spec (IRec specs) = map #const specs
  | consts_of_rec_or_spec (ISpec {consts, ...}) = consts;

fun props_of_rec_or_spec (IRec specs) = maps #props specs
  | props_of_rec_or_spec (ISpec {props, ...}) = props;

fun merge_two_rec_or_spec cmd cmd' =
  ISpec {consts = consts_of_rec_or_spec cmd @ consts_of_rec_or_spec cmd',
        props = props_of_rec_or_spec cmd @ props_of_rec_or_spec cmd'};

fun merge_two (ICoData (fp, specs)) (ICoData (fp', specs')) =
    ICoData (BNF_Util.case_fp fp fp fp', specs @ specs')
  | merge_two (IRec specs) (IRec specs') = IRec (specs @ specs')
  | merge_two (cmd as IRec _) (cmd' as ISpec _) = merge_two_rec_or_spec cmd cmd'
  | merge_two (cmd as ISpec _) (cmd' as IRec _) = merge_two_rec_or_spec cmd cmd'
  | merge_two (cmd as ISpec _) (cmd' as ISpec _) = merge_two_rec_or_spec cmd cmd'
  | merge_two _ _ = raise Fail "cannot merge mutually dependent commands";

fun sort_isa_problem_topologically ctxt cmds =
  let
    fun normal_pairs [] = []
      | normal_pairs (all as normal :: _) = map (rpair normal) all;

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

    val typedecls = filter (can (fn ITVal _ => ())) cmds;
    val mixed =
      filter (can (fn ICopy _ => () | IQuotient _ => () | ICoData _ => () | IVal _ => ()
        | ICoPred _ => () | IRec _ => () | ISpec _ => ())) cmds
      |> sort_prob;
    val axioms = filter (can (fn IAxiom _ => ())) cmds;
    val goals = filter (can (fn IGoal _ => ())) cmds;
  in
    typedecls @ mixed @ axioms @ goals
  end;

fun group_of (ITVal _) = 1
  | group_of (ICopy _) = 2
  | group_of (IQuotient _) = 3
  | group_of (ICoData _) = 4
  | group_of (IVal _) = 5
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

fun defined_by (Const (@{const_name All}, _) $ t) = defined_by t
  | defined_by (Abs (_, _, t)) = defined_by t
  | defined_by (@{const implies} $ _ $ u) = defined_by u
  | defined_by (Const (@{const_name HOL.eq}, _) $ t $ _) = head_of t
  | defined_by t = head_of t;

fun partition_props [_] props = SOME [props]
  | partition_props consts props =
    let
      val propss = map (fn const => filter (fn prop => defined_by prop aconv const) props) consts;
    in
      if eq_set (op aconv) (props, flat propss) andalso forall (not o null) propss then SOME propss
      else NONE
    end;

(* Prevents divergence in case of cyclic or infinite axiom dependencies. *)
val axioms_max_depth = 255

fun isa_problem_of_goal ctxt falsify goal0 =
  let
    val thy = Proof_Context.theory_of ctxt;

    fun consider_sort depth T S = I; (* FIXME *)

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

          fun consider_quotient_or_copy tuple_of s =
            let
              val (T0, repT0, wrt0, abs0, rep0) = tuple_of ctxt s;
              val tyenv = Sign.typ_match thy (T0, T) Vartab.empty;
              val substT = Envir.subst_type tyenv;
              val subst = Envir.subst_term_types tyenv;
              val repT = substT repT0;
              val wrt = subst wrt0;
              val abs = subst abs0;
              val rep = subst rep0;
            in
              apsnd (cons (ICopy {abs_typ = T, rep_typ = repT, wrt = wrt, abs = abs,
                rep = rep}))
              #> consider_term (depth + 1) wrt
            end;
        in
          (seens, prob)
          |> (case T of
               TFree (_, S) =>
               apsnd (cons (ITVal T))
               #> consider_sort depth T S
             | TVar (_, S) => consider_sort depth T S
             | Type (s, Ts) =>
               fold (consider_type depth) Ts
               #> (case classify_type_name ctxt s of
                    Co_Datatype =>
                    let
                      val (fp, ctr_sugars0) = mutual_co_datatypes_of ctxt s;
                      val fpTs = map ((fn Type (s, _) => Type (s, Ts)) o #T) ctr_sugars0;
                      val ctrss = map (map (Ctr_Sugar.mk_ctr Ts) o #ctrs) ctr_sugars0;
                      val co_data = ICoData (fp,
                        map2 (fn T => fn ctrs => {typ = T, ctrs = ctrs}) fpTs ctrss);
                    in
                      (fn ((seenS, seenT, seen), prob) =>
                          ((seenS, union (op =) fpTs seenT, seen), co_data :: prob))
                      #> fold (fold (consider_type (depth + 1) o fastype_of)) ctrss
                    end
                  | Quotient => consider_quotient_or_copy quotient_of s
                  | Copy => consider_quotient_or_copy copy_of s
                  | TVal => apsnd (cons (ITVal T))))
        end
    and consider_term depth t =
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
                (if is_const_builtin s orelse is_co_datatype_ctr ctxt x orelse
                    is_co_datatype_case ctxt x orelse is_quotient_abs ctxt x orelse
                    is_quotient_rep ctxt x orelse is_copy_abs ctxt x orelse
                    is_copy_rep ctxt x then
                   (seens, prob)
                 else if is_stale_copy_abs ctxt x orelse is_stale_copy_rep ctxt x then
                   raise Fail "stale abs or rep function"
                 else
                   (case spec_rules_of ctxt t of
                     SOME (classif, consts, props0) =>
                     let
                       val props = map (preprocess_prop false ctxt) props0;

                       fun specs () = [ISpec {consts = consts, props = props}];

                       val cmds =
                         if null props then
                           map IVal consts
                         else if classif = Spec_Rules.Equational then
                           (case partition_props consts props of
                             SOME propss =>
                             [IRec (map2 (fn const => fn props => {const = const, props = props})
                                consts propss)]
                           | NONE => specs ())
                         else if member (op =) [Spec_Rules.Inductive, Spec_Rules.Co_Inductive]
                             classif then
                           (case partition_props consts props of
                             SOME propss =>
                             [ICoPred (if classif = Spec_Rules.Inductive then BNF_Util.Least_FP
                                  else BNF_Util.Greatest_FP,
                                map2 (fn const => fn props => {const = const, props = props})
                                  consts propss)]
                           | NONE => specs ())
                         else
                           specs ();
                       val prob = cmds @ prob;
                     in
                       ((seenS, seenT, union (op aconv) consts seen), prob)
                       |> fold (consider_term (depth + 1)) props
                     end
                   | NONE =>
                     (seens, IVal t :: prob)))
                |> consider_type depth T
              | Free (_, T) =>
                (seens, IVal t :: prob)
                |> consider_type depth T)
            end));

    val goal = preprocess_prop falsify ctxt goal0;
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

fun str_of_isa_type_spec ctxt {abs_typ, rep_typ, wrt, abs, rep} =
  Syntax.string_of_typ ctxt abs_typ ^ " := " ^ Syntax.string_of_typ ctxt rep_typ ^
  "\n  wrt " ^ Syntax.string_of_term ctxt wrt ^
  "\n  abs " ^ Syntax.string_of_term ctxt abs ^
  "\n  rep " ^ Syntax.string_of_term ctxt rep;

fun str_of_isa_co_data_spec ctxt {typ, ctrs} =
  Syntax.string_of_typ ctxt typ ^ " :=\n  " ^
  space_implode "\n| " (map (str_of_isa_term_with_type ctxt) ctrs);

fun str_of_isa_const_spec ctxt {const, props} =
  str_of_isa_term_with_type ctxt const ^ " :=\n  " ^
  space_implode ";\n  " (map (Syntax.string_of_term ctxt) props);

fun str_of_isa_consts_spec ctxt {consts, props} =
  space_implode " and\n     " (map (str_of_isa_term_with_type ctxt) consts) ^ " :=\n  " ^
  space_implode ";\n  " (map (Syntax.string_of_term ctxt) props);

fun str_of_isa_command ctxt (ITVal T) = "type " ^ Syntax.string_of_typ ctxt T
  | str_of_isa_command ctxt (ICopy spec) = "copy " ^ str_of_isa_type_spec ctxt spec
  | str_of_isa_command ctxt (IQuotient spec) = "quotient " ^ str_of_isa_type_spec ctxt spec
  | str_of_isa_command ctxt (ICoData (fp, specs)) =
    BNF_Util.case_fp fp "data" "codata" ^ " " ^ str_of_and_list (str_of_isa_co_data_spec ctxt) specs
  | str_of_isa_command ctxt (IVal t) = "val " ^ str_of_isa_term_with_type ctxt t
  | str_of_isa_command ctxt (ICoPred (fp, specs)) =
    BNF_Util.case_fp fp "pred" "copred" ^ " " ^ str_of_and_list (str_of_isa_const_spec ctxt) specs
  | str_of_isa_command ctxt (IRec specs) =
    "rec " ^ str_of_and_list (str_of_isa_const_spec ctxt) specs
  | str_of_isa_command ctxt (ISpec spec) = "spec " ^ str_of_isa_consts_spec ctxt spec
  | str_of_isa_command ctxt (IAxiom t) = "axiom " ^ Syntax.string_of_term ctxt t
  | str_of_isa_command ctxt (IGoal t) = "goal " ^ Syntax.string_of_term ctxt t;

fun str_of_isa_problem ctxt =
  map (cat_lines o map (suffix "." o str_of_isa_command ctxt))
  #> space_implode "\n\n"
  #> suffix "\n";

end;
