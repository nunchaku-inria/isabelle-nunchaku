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

datatype encoding = Mono | Poly_Experimental;

fun flip_quote s =
  (case try (unprefix "'") s of
    SOME s' => s'
  | NONE => prefix "'" s);

fun nun_ty_of_isa enc (Type (s, Ts)) =
    let
      val id =
        (case s of
          @{type_name bool} => nun_prop
        | @{type_name fun} => nun_fun
        | _ => nun_tconst_of_str s);
      val tys = map (nun_ty_of_isa enc) Ts;
    in
      (case enc of
        Mono =>
        let
          val args' = space_implode (ascii_of ",") (map str_of_ty tys);
          val id' = id ^ ascii_of "(" ^ args' ^ ascii_of ")";
        in
          NType (id', [])
        end
      | Poly_Experimental => NType (id, tys))
    end
  | nun_ty_of_isa _ (TFree (s, _)) = NType (nun_tconst_of_str (flip_quote s), [])
  | nun_ty_of_isa _ (TVar (x, _)) = NTVar (nun_tvar_of_str (flip_quote (string_of_indexname x)));

fun nun_tm_of_isa ctxt enc t =
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
          val tys =
            (case enc of
              Mono => []
            | Poly_Experimental => map (nun_ty_of_isa enc) Ts);
        in
          NConst (id, tys, nun_ty_of_isa enc T)
        end
      | tm_of (Free (s, T)) = NConst (nun_const_of_str s, [], nun_ty_of_isa enc T)
      | tm_of (Var (x, T)) = NVar (nun_var_of_str (string_of_indexname x), nun_ty_of_isa enc T)
      | tm_of (Abs (s, T, t)) =
        let val x = Var ((s, j), T) in
          NAbs (tm_of x, tm_of (subst_bound (x, t)))
        end
      | tm_of (t $ u) = NApp (tm_of t, tm_of u)
      | tm_of (Bound _) = raise Fail "unexpected Bound"
  in
    tm_of t
  end;

fun nun_ctr_of_isa enc (Const (s, T)) =
    {ctr_id = nun_const_of_str s, arg_tys = map (nun_ty_of_isa enc) (binder_types T)}
  | nun_ctr_of_isa _ _ = raise Fail "expected Const";

fun nun_co_data_spec_of_isa enc {typ, ctrs} =
  {ty = nun_ty_of_isa enc typ, ctrs = map (nun_ctr_of_isa enc) ctrs};

fun nun_rec_spec_of_isa ctxt enc {func, eqs} =
  {func = nun_tm_of_isa ctxt enc func, eqs = map (nun_tm_of_isa ctxt enc) eqs};

fun nun_spec_spec_of_isa ctxt enc {funcs, props} =
  let
    fun func_of func alias =
      {func = nun_tm_of_isa ctxt enc func, alias = nun_tm_of_isa ctxt enc alias};

    val j = fold (Integer.max o maxidx_of_term) props ~1 + 1;

    val aliases =
      map_index (fn (i, func) => Var ((("F" ^ string_of_int i), j), fastype_of func)) funcs;
    val props' = map (subst_atomic (funcs ~~ aliases)) props;
  in
    {funcs = map2 func_of funcs aliases, props = map (nun_tm_of_isa ctxt enc) props'}
  end;

fun nun_problem_of_isa ctxt =
  let
    val enc = Mono;

    fun prob_of [] = []
      | prob_of (cmd :: prob) =
        let
          val cmds' =
            (case cmd of
              ITypedecl T => [NTVal (nun_ty_of_isa enc T)]
            | IData specs => [NData (map (nun_co_data_spec_of_isa enc) specs)]
            | ICodata specs => [NCodata (map (nun_co_data_spec_of_isa enc) specs)]
            | IConst t => [NVal (nun_tm_of_isa ctxt enc t, nun_ty_of_isa enc (fastype_of t))]
            | IRec specs => [NRec (map (nun_rec_spec_of_isa ctxt enc) specs)]
            | ISpec spec => [NSpec (nun_spec_spec_of_isa ctxt enc spec)]
            | IAxiom prop => [NAxiom (nun_tm_of_isa ctxt enc prop)]
            | IGoal prop => [NGoal (nun_tm_of_isa ctxt enc prop)]);
        in
          cmds' @ prob_of prob
        end;
  in
    prob_of
  end

end;
