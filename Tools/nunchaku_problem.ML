(*  Title:      HOL/Tools/Nunchaku/nunchaku_problem.ML
    Author:     Jasmin Blanchette, Inria Nancy, LORIA, MPII
    Copyright   2015

Problem generation for Nunchaku.
*)

signature NUNCHAKU_PROBLEM =
sig
  type ident = string

  datatype tm =
    NConst of ident * ty
  | NRawConst of ident * ty
  | NVar of ident * ty
  | NAbs of tm * tm
  | NApp of tm * tm

  datatype ty =
    NType of ident * ty list
  | NTVar of ident

  type ctr_spec =
    {ctr: ident,
     arg_tys: ty list}

  type co_data_spec =
    {ty: ty,
     ctrs: ctr_spec list}

  type aliased_func =
    {func: tm,
     alias: ident}

  type rec_spec =
    {func: tm,
     eqs: tm list}

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

  val strs_of_problem: problem -> string list
end;

structure Nunchaku_Problem : NUNCHAKU_PROBLEM =
struct

type ident = string;

datatype tm =
  NConst of ident * ty
| NRawConst of ident * ty
| NVar of ident * ty
| NAbs of tm * tm
| NApp of tm * tm;

datatype ty =
  NType of ident * ty list
| NTVar of ident;

type ctr_spec =
  {ctr: ident,
   arg_tys: ty list};

type co_data_spec =
  {ty: ty,
   ctrs: ctr_spec list};

type aliased_func =
  {func: tm,
   alias: ident};

type rec_spec =
  {func: tm,
   eqs: tm list};

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

fun str_of_command (Val (tm, ty)) = "val " ^ str_of_tm tm ^ " : " ^ str_of_ty ty
  | str_of_command (Data specs) = "data " ^ and_list str_of_co_data_spec specs
  | str_of_command (Codata specs) = "codata " ^ and_list str_of_co_data_spec specs
  | str_of_command (Rec specs) = "rec " ^ and_list str_of_rec_spec specs
  | str_of_command (Spec spec) = "spec " ^ str_of_spec_spec spec
  | str_of_command (Axiom tm) = "axiom " ^ str_of_tm tm
  | str_of_command (Goal tm) = "goal " ^ str_of_tm tm

val strs_of_problem = map str_of_command;

end;
