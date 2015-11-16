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

fun isa_co_data_spec_fold_terms f ({ctrs, ...} : isa_co_data_spec) = fold f ctrs;
fun isa_rec_spec_fold_terms f ({eqs, ...} : isa_rec_spec) = fold f eqs;
fun isa_spec_spec_fold_terms f ({props, ...} : isa_spec_spec) = fold f props;

fun isa_cmd_fold_terms _ (ITypedecl _) = I
  | isa_cmd_fold_terms f (IData specs) = fold (isa_co_data_spec_fold_terms f) specs
  | isa_cmd_fold_terms f (ICodata specs) = fold (isa_co_data_spec_fold_terms f) specs
  | isa_cmd_fold_terms f (IConst t) = f t
  | isa_cmd_fold_terms f (IRec specs) = fold (isa_rec_spec_fold_terms f) specs
  | isa_cmd_fold_terms f (ISpec spec) = isa_spec_spec_fold_terms f spec
  | isa_cmd_fold_terms f (IAxiom t) = f t
  | isa_cmd_fold_terms f (IGoal t) = f t;

fun atomize_toward_False ctxt t =
  let val t' = Object_Logic.atomize_term ctxt t in
    if fastype_of t' = HOLogic.boolT then t' else @{const False}
  end;

fun isa_problem_of_goal ctxt goal0 =
  let
    val goal = atomize_toward_False ctxt goal0;
    val isa_prob0 = [IGoal goal];

    fun add_consts (t as Const _) = insert (op aconv) t
      | add_consts (t as Free _) = insert (op aconv) t
      | add_consts (t $ u) = add_consts t #> add_consts u
      | add_consts (Abs (_, _, t)) = add_consts t
      | add_consts _ = I;

    val isa_consts = fold (isa_cmd_fold_terms add_consts) isa_prob0 []
      |> map IConst;
  in
    isa_consts @ isa_prob0
  end;

end;
