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

open Nunchaku_Collect;
open Nunchaku_Problem;

fun flip_quote s =
  (case try (unprefix "'") s of
    SOME s' => s'
  | NONE => prefix "'" s);

fun nun_ty_of_isa (Type (s, Ts)) = NType (nun_tconst_of_str s, map nun_ty_of_isa Ts)
  | nun_ty_of_isa (TFree (s, _)) = NType (nun_tconst_of_str (flip_quote s), [])
  | nun_ty_of_isa (TVar (x, _)) = NTVar (nun_tvar_of_str (flip_quote (string_of_indexname x)));

fun nun_tm_of_isa ctxt t =
  let
    val thy = Proof_Context.theory_of ctxt;

    val j = maxidx_of_term t + 1;

    fun tm_of (Const (s, T)) =
        let
          val Ts = Sign.const_typargs thy (s, T);
          val id =
            (case s of
              @{const_name conj} => nun_conj
            | @{const_name disj} => nun_disj
            | @{const_name HOL.eq} => nun_equals
            | @{const_name False} => nun_false
            | @{const_name implies} => nun_implies
            | @{const_name Not} => nun_not
            | @{const_name True} => nun_true
            | _ => nun_const_of_str s);
        in
          NConst (id, map nun_ty_of_isa Ts, nun_ty_of_isa T)
        end
      | tm_of (Free (s, T)) = NConst (nun_const_of_str s, [], nun_ty_of_isa T)
      | tm_of (Var (x, T)) = NVar (nun_var_of_str (string_of_indexname x), nun_ty_of_isa T)
      | tm_of (Abs (s, T, t)) =
        let val x = Var ((s, j), T) in
          NAbs (tm_of x, tm_of (subst_bound (x, t)))
        end
      | tm_of (t $ u) = NApp (tm_of t, tm_of u)
      | tm_of (Bound _) = raise Fail "unexpected Bound"
  in
    tm_of t
  end;

fun nun_ctr_of_isa (Const (s, T)) =
    {ctr_id = nun_const_of_str s, arg_tys = map nun_ty_of_isa (binder_types T)}
  | nun_ctr_of_isa _ = raise Fail "expected Const";

fun nun_co_data_spec_of_isa {typ, ctrs} =
  {ty = nun_ty_of_isa typ, ctrs = map nun_ctr_of_isa ctrs};

fun nun_rec_spec_of_isa ctxt {func, eqs} =
  {func = nun_tm_of_isa ctxt func, eqs = map (nun_tm_of_isa ctxt) eqs};

fun nun_spec_spec_of_isa ctxt {funcs, props} =
  let
    fun func_of func alias =
      {func = nun_tm_of_isa ctxt func, alias = nun_tm_of_isa ctxt alias};

    val j = fold (Integer.max o maxidx_of_term) props ~1 + 1;

    val aliases =
      map_index (fn (i, func) => Var ((("F" ^ string_of_int i), j), fastype_of func)) funcs;
    val props' = map (subst_atomic (funcs ~~ aliases)) props;
  in
    {funcs = map2 func_of funcs aliases, props = map (nun_tm_of_isa ctxt) props'}
  end;

fun nun_problem_of_isa ctxt =
  let
    fun prob_of [] = []
      | prob_of (cmd :: prob) =
        let
          val cmds' =
            (case cmd of
              ITypedecl T => [NTVal (nun_ty_of_isa T)]
            | IData specs => [NData (map nun_co_data_spec_of_isa specs)]
            | ICodata specs => [NCodata (map nun_co_data_spec_of_isa specs)]
            | IConst t => [NVal (nun_tm_of_isa ctxt t, nun_ty_of_isa (fastype_of t))]
            | IRec specs => [NRec (map (nun_rec_spec_of_isa ctxt) specs)]
            | ISpec spec => [NSpec (nun_spec_spec_of_isa ctxt spec)]
            | IAxiom prop => [NAxiom (nun_tm_of_isa ctxt prop)]
            | IGoal prop => [NGoal (nun_tm_of_isa ctxt prop)]);
        in
          cmds' @ prob_of prob
        end;
  in
    prob_of
  end

end;
