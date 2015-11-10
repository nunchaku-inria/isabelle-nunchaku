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

fun nun_ty_of_isa (Type (s, Ts)) = NType (nun_const_of_str s, map nun_ty_of_isa Ts)
  | nun_ty_of_isa (TFree (s, _)) = NType (nun_const_of_str (flip_quote s), [])
  | nun_ty_of_isa (TVar (x, _)) = NTVar (nun_var_of_str (flip_quote (string_of_indexname x)));

fun nun_tm_of_isa thy t =
  let
    val j = maxidx_of_term t + 1;

    fun tm_of (Const (s, T)) =
        let val Ts = Sign.const_typargs thy (s, T) in
          NConst (s, map nun_ty_of_isa Ts, nun_ty_of_isa T)
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

fun nun_problem_of_isa ctxt =
  let
    val thy = Proof_Context.theory_of ctxt;

    fun prob_of [] = []
      | prob_of (cmd :: prob) =
        let
          val cmds' =
            (case cmd of
              ITypedecl T => [NTVal (nun_ty_of_isa T)]
(*
            | IData specs =>
            | ICodata specs =>
*)
            | IConst t => [NVal (nun_tm_of_isa thy t, nun_ty_of_isa (fastype_of t))]
(*
            | IRec specs =>
            | ISpec spec =>
            | IAxiom prop =>
            | IGoal prop => 
*)
            )
        in
          cmds' @ prob_of prob
        end;
  in
    prob_of
  end

end;
