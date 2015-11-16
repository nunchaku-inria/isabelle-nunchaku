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

  type isa_problem = isa_command list

  val isa_problem_of_goal: Proof.context -> term -> isa_problem
end;

structure Nunchaku_Collect : NUNCHAKU_COLLECT =
struct

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

type isa_problem = isa_command list;

fun isa_cmd_fold_terms_types f_ty f_tm0 =
  let
    fun f_tm t = f_tm0 t #> fold_types f_ty t;

    fun co_data_spec_fold {typ, ctrs} = f_ty typ #> fold f_tm ctrs;
    fun rec_spec_fold {func, eqs} = f_tm func #> fold f_tm eqs;
    fun spec_spec_fold {funcs, props} = fold f_tm funcs #> fold f_tm props;

    fun cmd_fold (ITypedecl T) = f_ty T
      | cmd_fold (IData specs) = fold co_data_spec_fold specs
      | cmd_fold (ICodata specs) = fold co_data_spec_fold specs
      | cmd_fold (IConst t) = f_tm t
      | cmd_fold (IRec specs) = fold rec_spec_fold specs
      | cmd_fold (ISpec spec) = spec_spec_fold spec
      | cmd_fold (IAxiom t) = f_tm t
      | cmd_fold (IGoal t) = f_tm t;
  in
    cmd_fold
  end;

fun atomize_toward_False ctxt t =
  let val t' = Object_Logic.atomize_term ctxt t in
    if fastype_of t' = HOLogic.boolT then t' else @{const False}
  end;

fun eq_Type_root (Type (s, _), Type (s', _)) = (s = s')
  | eq_Type_root (T, T') = (T = T');

fun tyvars_of_arity n =
  map (fn i => TVar (("'a", i), @{sort type})) (1 upto n);

fun varify_Type_leaves (Type (s, Ts)) = Type (s, tyvars_of_arity (length Ts))
  | varify_Type_leaves T = T;

fun is_typ_builtin s = member (op =) [@{type_name bool}, @{type_name fun}] s;
fun is_const_builtin s = (s = @{const_name HOL.eq});

fun isa_problem_of_goal ctxt goal0 =
  let
    val goal = atomize_toward_False ctxt goal0;
    val isa_prob0 = [IGoal goal];

    fun add_types (T as Type (s, Ts)) =
        (not (is_typ_builtin s) ? insert eq_Type_root T) #> fold add_types Ts
      | add_types (T as TFree _) = insert (op =) T;

    fun add_consts (t as Const (s, _)) = not (is_const_builtin s) ? insert (op aconv) t
      | add_consts (t as Free _) = insert (op aconv) t
      | add_consts (t $ u) = add_consts t #> add_consts u
      | add_consts (Abs (_, _, t)) = add_consts t
      | add_consts _ = I;

    val (types, consts) =
      fold (isa_cmd_fold_terms_types (apfst o add_types) (apsnd o add_consts)) isa_prob0 ([], []);

    val isa_typedecls = map (ITypedecl o varify_Type_leaves) types;
    val isa_consts = map IConst consts;
  in
    isa_typedecls @ isa_consts @ isa_prob0
  end;

end;
