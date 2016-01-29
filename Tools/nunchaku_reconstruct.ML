(*  Title:      HOL/Tools/Nunchaku/nunchaku_reconstruct.ML
    Author:     Jasmin Blanchette, Inria Nancy, LORIA, MPII
    Copyright   2015, 2016

Reconstruction of Nunchaku models in Isabelle/HOL.
*)

signature NUNCHAKU_RECONSTRUCT =
sig
  type nun_model = Nunchaku_Model.nun_model

  type typ_entry = typ * typ list
  type term_entry = term * term

  type isa_model =
    {type_model: typ_entry list,
     skolem_model: term_entry list,
     const_model: term_entry list}

  val empty_isa_model: isa_model

  val isa_model_of_nun: nun_model -> isa_model
end;

structure Nunchaku_Reconstruct : NUNCHAKU_RECONSTRUCT =
struct

open Nunchaku_Problem;
open Nunchaku_Model;

type typ_entry = typ * typ list;
type term_entry = term * term;

type isa_model =
  {type_model: typ_entry list,
   skolem_model: term_entry list,
   const_model: term_entry list};

val empty_isa_model = {type_model = [], skolem_model = [], const_model = []};

fun typ_of_nun (NType (id, tys)) = raise Fail "";

(*
fun ty_of_isa (Type (s, Ts)) =
    let val tys = map ty_of_isa Ts in
      (case s of
        @{type_name bool} => nun_prop_ty
      | @{type_name fun} => NType (nun_fun, tys)
      | _ =>
        let
          val id = nun_tconst_of_str s;
          val args' = space_implode (ascii_of ",") (map str_of_ty tys);
          val id' = ascii_of "(" ^ args' ^ ascii_of ")." ^ id;
        in
          NType (id', [])
        end)
    end
  | ty_of_isa (TFree (s, _)) = NType (nun_tconst_of_str (flip_quote s), [])
*)

fun term_of_nun (NConst (id, tys, ty)) = raise Fail ""
  | term_of_nun (NVar (id, ty)) = raise Fail ""
  | term_of_nun (NAbs (var, body)) = raise Fail ""
  | term_of_nun (NMatch _) = raise Fail ""
  | term_of_nun (NApp (func, arg)) = raise Fail "";

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
      | tm_of _ (Free (s, T)) = NConst (nun_const_of_str s, [], ty_of_isa T)
      | tm_of _ (Var (x, T)) = NVar (nun_var_of_str (string_of_indexname x), ty_of_isa T)
      | tm_of bounds (Abs (s, T, t)) =
        let
          val (s', bounds') = Name.variant s bounds;
          val x = Var ((s', 0), T);
        in
          NAbs (tm_of bounds' x, tm_of bounds' (subst_bound (x, t)))
        end
      | tm_of bounds (t $ u) = NApp (tm_of bounds t, tm_of bounds u)
      | tm_of _ (Bound _) = raise Fail "unexpected Bound";
  in
    t
    |> tm_of Name.context
    |> beta_reduce_tm
    |> eta_expand_builtin_tm
  end;
*)

fun isa_typ_entry_of_nun (ty, atoms) =
  (typ_of_nun ty, map term_of_nun atoms);

fun isa_term_entry_of_nun (tm, value) =
  (term_of_nun tm, term_of_nun value);

fun isa_model_of_nun {type_model, skolem_model, const_model} =
  {type_model = map isa_typ_entry_of_nun type_model,
   skolem_model = map isa_term_entry_of_nun skolem_model,
   const_model = map isa_term_entry_of_nun const_model};

end;
