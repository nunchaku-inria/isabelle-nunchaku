(*  Title:      HOL/Tools/Nunchaku/nunchaku_model.ML
    Author:     Jasmin Blanchette, Inria Nancy, LORIA, MPII
    Copyright   2015, 2016

Model reconstruction for Nunchaku.
*)

signature NUNCHAKU_MODEL =
sig
  type ty = Nunchaku_Problem.ty
  type tm = Nunchaku_Problem.tm
  type name_pool = Nunchaku_Problem.name_pool

  type ty_entry = ty * tm list
  type tm_entry = tm * tm

  type nun_model =
    {ty_model: ty_entry list,
     skolem_model: tm_entry list,
     const_model: tm_entry list}

  val allocate_ugly: name_pool -> string * string -> string * name_pool

  val ugly_nun_model: name_pool -> nun_model -> nun_model
  val nun_model_of_str: string -> nun_model
end;

structure Nunchaku_Model : NUNCHAKU_MODEL =
struct

open Nunchaku_Problem;

type ty_entry = ty * tm list;
type tm_entry = tm * tm;

type nun_model =
  {ty_model: ty_entry list,
   skolem_model: tm_entry list,
   const_model: tm_entry list};

fun fold_map_ty_entry_idents f (ty, atoms) =
  fold_map_ty_idents f ty
  ##>> fold_map (fold_map_tm_idents f) atoms;

fun fold_map_tm_entry_idents f (tm, value) =
  fold_map_tm_idents f tm
  ##>> fold_map_tm_idents f value;

fun fold_map_nun_model_idents f {ty_model, skolem_model, const_model} =
  fold_map (fold_map_ty_entry_idents f) ty_model
  ##>> fold_map (fold_map_tm_entry_idents f) skolem_model
  ##>> fold_map (fold_map_tm_entry_idents f) const_model
  #>> (fn ((ty_model, skolem_model), const_model) =>
    {ty_model = ty_model, skolem_model = skolem_model, const_model = const_model});

fun swap_name_pool ({nice_of_ugly, ugly_of_nice} : name_pool) =
  {nice_of_ugly = ugly_of_nice, ugly_of_nice = nice_of_ugly};

val allocate_ugly = allocate_nice o swap_name_pool;

fun ugly_ident nice (pool as {ugly_of_nice, ...}) =
  (case Symtab.lookup ugly_of_nice nice of
    NONE => allocate_ugly pool (nice, nice)
  | SOME ugly => (ugly, pool));

fun ugly_nun_model pool model =
  fst (fold_map_nun_model_idents ugly_ident model pool);

fun nun_model_of_str str =
  {ty_model = [], skolem_model = [], const_model = []};

end;
