(*  Title:      HOL/Tools/Nunchaku/nunchaku_translate.ML
    Author:     Jasmin Blanchette, Inria Nancy, LORIA, MPII
    Copyright   2015

Translation from Isabelle/HOL to Nunchaku problems.
*)

signature NUNCHAKU_TRANSLATE =
sig
  type isa_problem = Nunchaku_Collect.isa_problem
  type nun_problem = Nunchaku_Problem.nun_problem

  val nun_problem_of_isa: Proof.context -> isa_problem -> nun_problem
end;

structure Nunchaku_Translate : NUNCHAKU_TRANSLATE =
struct

open Nunchaku_Util;
open Nunchaku_Collect;
open Nunchaku_Problem;

fun varify_free (t $ u) = varify_free t $ varify_free u
  | varify_free (Abs (s, T, t)) = Abs (s, T, varify_free t)
  | varify_free (Free (s, T)) = Var ((s, 0), T)
  | varify_free t = t;

fun dest_abss 0 t = ([], t)
  | dest_abss n (Abs (s, T, t)) =
    let
      val (frees, t') = dest_abss (n - 1) t;
      val (free_name, t'') = Term.dest_abs (s, T, t');
      val free = Free (free_name, T);
    in
      (free :: frees, t'')
    end;

fun dest_abss_Var bounds n =
  dest_abss n
  #>> map varify_free
  ##> varify_free;

fun flip_quote s =
  (case try (unprefix "'") s of
    SOME s' => s'
  | NONE => prefix "'" s);

fun nun_ty_of_isa (Type (s, Ts)) =
    let val tys = map nun_ty_of_isa Ts in
      (case s of
        @{type_name bool} => nun_prop_ty
      | @{type_name fun} => NType (nun_fun, tys)
      | @{type_name set} => NType (nun_fun, tys @ [nun_prop_ty])
      | _ =>
        let
          val id = nun_tconst_of_str s;
          val args' = space_implode (ascii_of ",") (map str_of_ty tys);
          val id' = ascii_of "(" ^ args' ^ ascii_of ")." ^ id;
        in
          NType (id', [])
        end)
    end
  | nun_ty_of_isa (TFree (s, _)) = NType (nun_tconst_of_str (flip_quote s), [])
  | nun_ty_of_isa (TVar (x, _)) = NTVar (nun_tvar_of_str (flip_quote (string_of_indexname x)));

fun nun_tm_of_isa ctxt t =
  let
    val thy = Proof_Context.theory_of ctxt;

    fun tm_of bounds (Const (@{const_name Collect}, T)) =
        tm_of bounds (Abs (Name.uu, domain_type T, Bound 0))
      | tm_of bounds (Const (@{const_name Set.member}, T)) =
        tm_of bounds (Abs (Name.uu, domain_type T,
          Abs (Name.uu, domain_type (range_type T), Bound 0 $ Bound 1)))
      | tm_of bounds (t as Const (x as (s, T))) =
        let
          val Ts = Sign.const_typargs thy x;
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
            | _ =>
              (case dest_co_datatype_case ctxt x of
                SOME var_counts =>
                let
                  val num_f_args = length var_counts;
                  val t' = eta_expand bounds t (n + 1);
                  val (func, (f_args, obj :: rest)) = strip_comb t' ||> chop num_f_args;
                  val f_args' = map2 (eta_expand bounds) f_args var_counts;

                  val ctr_ids = []; (* FIXME *)

                  fun do_branch ctr_id var_count f_arg =
                    let
                      val (vars, body) = dest_abss_Var bounds var_count f_arg;
                    in
                      (ctr_id, vars, body)
                    end;
                in
                  NMatch (obj, map3 do_branch ctr_ids var_counts f_args')
                end
              | NONE =>
                let
                  val id = nun_const_of_str s;
                  val tys = map nun_ty_of_isa Ts;
                  val args' = space_implode (ascii_of ",") (map str_of_ty tys);
                in
                  ascii_of "(" ^ args' ^ ascii_of ")." ^ id
                end));
        in
          NConst (id', [], nun_ty_of_isa T)
        end
      | tm_of _ (Free (s, T)) = NConst (nun_const_of_str s, [], nun_ty_of_isa T)
      | tm_of _ (Var (x, T)) = NVar (nun_var_of_str (string_of_indexname x), nun_ty_of_isa T)
      | tm_of bounds (Abs (s, T, t)) =
        let
          val (s', bounds') = Name.variant s bounds;
          val x = Var ((s', 0), T);
        in
          NAbs (tm_of bounds' x, tm_of bounds' (subst_bound (x, t)))
        end
      | tm_of bounds (t $ u) = NApp (tm_of bounds t, tm_of bounds u)
      | tm_of _ (Bound _) = raise Fail "unexpected Bound"
  in
    t
    |> tm_of Name.context
    |> beta_reduce_tm
    |> eta_expand_builtin_tm
  end;

fun nun_type_spec_of_isa ctxt {abs_typ, rep_typ, wrt, abs, rep} =
  {abs_ty = nun_ty_of_isa abs_typ, rep_ty = nun_ty_of_isa rep_typ, wrt = nun_tm_of_isa ctxt wrt,
   abs = nun_tm_of_isa ctxt abs, rep = nun_tm_of_isa ctxt rep};

fun nun_ctr_of_isa ctxt ctr =
  {ctr = nun_tm_of_isa ctxt ctr, arg_tys = map nun_ty_of_isa (binder_types (fastype_of ctr))};

fun nun_co_data_spec_of_isa ctxt {typ, ctrs} =
  {ty = nun_ty_of_isa typ, ctrs = map (nun_ctr_of_isa ctxt) ctrs};

fun nun_const_spec_of_isa ctxt {const, props} =
  {const = nun_tm_of_isa ctxt const, props = map (nun_tm_of_isa ctxt) props};

fun nun_consts_spec_of_isa ctxt {consts, props} =
  {consts = map (nun_tm_of_isa ctxt) consts, props = map (nun_tm_of_isa ctxt) props};

fun nun_problem_of_isa ctxt =
  let
    fun cmd_of cmd =
      (case cmd of
        ITVal T => NTVal (nun_ty_of_isa T)
      | ICopy spec => NCopy (nun_type_spec_of_isa ctxt spec)
      | IQuotient spec => NQuotient (nun_type_spec_of_isa ctxt spec)
      | ICoData (fp, specs) =>
        BNF_Util.case_fp fp NData NCodata (map (nun_co_data_spec_of_isa ctxt) specs)
      | IVal t => NVal (nun_tm_of_isa ctxt t, nun_ty_of_isa (fastype_of t))
      | ICoPred (fp, specs) =>
        BNF_Util.case_fp fp NPred NCopred (map (nun_const_spec_of_isa ctxt) specs)
      | IRec specs => NRec (map (nun_const_spec_of_isa ctxt) specs)
      | ISpec spec => NSpec (nun_consts_spec_of_isa ctxt spec)
      | IAxiom prop => NAxiom (nun_tm_of_isa ctxt prop)
      | IGoal prop => NGoal (nun_tm_of_isa ctxt prop));
  in
    map (map cmd_of)
  end;

end;
