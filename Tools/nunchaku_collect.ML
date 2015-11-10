(*  Title:      HOL/Tools/Nunchaku/nunchaku_collect.ML
    Author:     Jasmin Blanchette, Inria Nancy, LORIA, MPII
    Copyright   2015

Collection of Isabelle/HOL definitions etc. for Nunchaku.
*)

signature NUNCHAKU_COLLECT =
sig
  type isa_co_data_spec =
    {ty: term,
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

  val isa_problem_of_goal: term -> isa_problem
end;

structure Nunchaku_Collect : NUNCHAKU_COLLECT =
struct

type isa_co_data_spec =
  {ty: term,
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

fun isa_problem_of_goal goal =
  [IGoal goal];

end;
