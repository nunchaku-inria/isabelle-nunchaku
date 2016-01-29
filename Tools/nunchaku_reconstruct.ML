(*  Title:      HOL/Tools/Nunchaku/nunchaku_reconstruct.ML
    Author:     Jasmin Blanchette, Inria Nancy, LORIA, MPII
    Copyright   2015, 2016

Reconstruction of Nunchaku models in Isabelle/HOL.
*)

signature NUNCHAKU_RECONSTRUCT =
sig
  type nun_model = Nunchaku_Model.nun_model

  type typ_entry = typ * term list
  type term_entry = term * term

  type isa_model =
    {type_model: typ_entry list,
     skolem_model: term_entry list,
     const_model: term_entry list}

  val isa_model_of_nun: Proof.context -> nun_model -> isa_model
end;

structure Nunchaku_Reconstruct : NUNCHAKU_RECONSTRUCT =
struct

open Nunchaku_Problem;
open Nunchaku_Translate;
open Nunchaku_Model;

type typ_entry = typ * term list;
type term_entry = term * term;

type isa_model =
  {type_model: typ_entry list,
   skolem_model: term_entry list,
   const_model: term_entry list};

fun typ_of_nun ctxt =
  let
    fun typ_of (NType (id, tys)) =
      let val Ts = map typ_of tys in
        if id = nun_dummy then
          dummyT
        else if id = nun_prop then
          @{typ bool}
        else if id = nun_fun then
          Type (@{type_name fun}, Ts)
        else
          (case try str_of_nun_const id of
            SOME s =>
            let
              val s' = s; (* FIXME *)
              val Ts' = []; (* FIXME *)
            in
              Type (s', Ts')
            end
          | NONE =>
            (case try str_of_nun_var id of
              SOME s => TFree (Proof_Context.check_tfree ctxt (flip_quote s, dummyS))
            | NONE => raise Fail ("unknown type identifier: " ^ quote id)))
      end;
  in
    typ_of
  end;

fun term_of_nun ctxt =
  let
    val typ_of = typ_of_nun ctxt;

    fun term_of (NConst (id, tys, ty)) =
        (* FIXME *)
        (case try str_of_nun_var id of
          SOME s => Free (s, typ_of ty)
        | NONE => Free (str_of_nun_atom id, typ_of ty))
      | term_of (NVar (id, ty)) =
        (case try str_of_nun_var id of
          SOME s => Var ((s, 0), typ_of ty)
        | NONE => raise Fail ("unknown term identifier: " ^ quote id))
      | term_of (NAbs (var, body)) = lambda (term_of var) (term_of body)
      | term_of (NMatch _) = raise Fail "match not supported"
      | term_of (NApp (func, arg)) = term_of func $ term_of arg;
  in
    term_of
  end;

(*
fun tm_of_isa ctxt t =
  let
    val thy = Proof_Context.theory_of ctxt;

    fun id'_of_const (x as (s, _)) =
      let
        val Ts = Sign.const_typargs thy x;

        val id = nun_const_of_str s;
        val tys = map ty_of_isa Ts;
        val args' = space_implode (ascii_of ",") (map str_of_ty tys);
      in
        ascii_of "(" ^ args' ^ ascii_of ")." ^ id
      end;

    fun tm_of_branch ctr_id var_count f_arg_tm =
      let val (vars, body) = strip_nun_abs var_count f_arg_tm in
        (ctr_id, vars, body)
      end;

    fun tm_of bounds (Const (x as (s, T))) =
        (case try (dest_co_datatype_case ctxt) x of
          SOME ctrs =>
          let
            val num_f_args = length ctrs;
            val min_args = num_f_args + 1;
            val var_counts = map (num_binder_types o snd) ctrs;

            val dummy_free = Free (Name.uu, T);
            val tm = tm_of bounds dummy_free;
            val tm' = eta_expandN_tm min_args tm;
            val (vars, body) = strip_nun_abs min_args tm';
            val (_, (f_args, obj :: other_args)) = strip_nun_comb body ||> chop num_f_args;
            val f_args' = map2 eta_expandN_tm var_counts f_args;

            val ctr_ids = map id'_of_const ctrs;
          in
            NMatch (obj, @{map 3} tm_of_branch ctr_ids var_counts f_args')
            |> rcomb_tms other_args
            |> abs_tms vars
          end
        | NONE =>
          let
            val id' =
              (case s of
                @{const_name All} => nun_forall
              | @{const_name conj} => nun_conj
              | @{const_name disj} => nun_disj
              | @{const_name HOL.eq} => nun_equals
              | @{const_name Ex} => nun_exists
              | @{const_name False} => nun_false
              | @{const_name If} => nun_if
              | @{const_name implies} => nun_implies
              | @{const_name Not} => nun_not
              | @{const_name True} => nun_true
              | _ => id'_of_const x);
          in
            NConst (id', [], ty_of_isa T)
          end)
  in
    t
    |> tm_of Name.context
    |> beta_reduce_tm
    |> eta_expand_builtin_tm
  end;
*)

fun isa_typ_entry_of_nun ctxt (ty, atoms) =
  (typ_of_nun ctxt ty, map (term_of_nun ctxt) atoms);

fun isa_term_entry_of_nun ctxt (tm, value) =
  (term_of_nun ctxt tm, term_of_nun ctxt value);

fun isa_model_of_nun ctxt {type_model, skolem_model, const_model} =
  {type_model = map (isa_typ_entry_of_nun ctxt) type_model,
   skolem_model = map (isa_term_entry_of_nun ctxt) skolem_model,
   const_model = map (isa_term_entry_of_nun ctxt) const_model};

end;
