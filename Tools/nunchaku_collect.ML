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
  val str_of_isa_problem: Proof.context -> isa_problem -> string
end;

structure Nunchaku_Collect : NUNCHAKU_COLLECT =
struct

open Nunchaku_Util;

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

fun atomize_toward_False ctxt t =
  let val t' = Object_Logic.atomize_term ctxt t in
    if fastype_of t' = HOLogic.boolT then t' else @{const False}
  end;

fun mutual_co_datatypes_of ctxt T_name =
  (case BNF_FP_Def_Sugar.fp_sugar_of ctxt T_name of
    SOME (fp_sugar as {fp, fp_res = {Ts, ...}, ...}) =>
    SOME (fp,
      (case Ts of
        [_] => [fp_sugar]
      | _ => map (the o BNF_FP_Def_Sugar.fp_sugar_of ctxt o fst o dest_Type) Ts)
      |> map (#ctr_sugar o #fp_ctr_sugar))
  | NONE =>
    (case Ctr_Sugar.ctr_sugar_of ctxt T_name of
      SOME (ctr_sugar as {kind, ...}) =>
      (case kind of
        Ctr_Sugar.Datatype => SOME (BNF_Util.Least_FP, [ctr_sugar])
      | Ctr_Sugar.Codatatype => SOME (BNF_Util.Greatest_FP, [ctr_sugar])
      | _ => NONE)
    | NONE => NONE));

fun is_co_data_ctr ctxt (s, T) =
  (case body_type T of
    dataT as Type (dataT_name, Ts) =>
    let
      fun is_right_ctr (t' as Const (s', T')) =
        s = s' andalso fastype_of (Ctr_Sugar.mk_ctr Ts t') = T;

      val ctrs =
        (case Ctr_Sugar.ctr_sugar_of ctxt dataT_name of
          SOME {ctrs, ...} => ctrs
        | _ => []);
    in
      exists is_right_ctr ctrs
    end
  | _  => false);

val is_typ_builtin = member (op =) [@{type_name bool}, @{type_name fun}];
val is_const_builtin =
  member (op =) [@{const_name conj}, @{const_name disj}, @{const_name HOL.eq}, @{const_name False},
    @{const_name implies}, @{const_name True}];

fun isa_cmd_of_ctr_sugars fp (ctr_sugars : Ctr_Sugar.ctr_sugar list) =
  (case fp of
    BNF_Util.Least_FP => IData
  | BNF_Util.Greatest_FP => ICodata)
    (map (fn {T, ctrs, ...} => {typ = T, ctrs = ctrs}) ctr_sugars);

(* Prevents divergence in case of cyclic or infinite axiom dependencies. *)
val axioms_max_depth = 255

fun isa_problem_of_goal ctxt goal0 =
  let
    fun consider_sort depth T S = I;

    fun consider_type depth T =
      (case T of
        Type (@{type_name fun}, Ts) => fold (consider_type depth) Ts
      | @{typ prop} => I
      | @{typ bool} => I
      | _ =>
        (fn (seens as (seenS, seenT, seen), prob) =>
            if member (op =) seenT T then
              (seens, prob)
            else
              let
                val seenT = T :: seenT;
                val seens = (seenS, seenT, seen);
              in
                (case T of
                  TFree (_, S) =>
                  (fn (seen, prob) =>
                      (seen, ITypedecl T :: prob)
                      |> consider_sort depth T S)
                | TVar (_, S) => consider_sort depth T S
                | Type (s, Ts) =>
                  fold (consider_type depth) Ts
                  #> (case mutual_co_datatypes_of ctxt s of
                       SOME (kind, ctr_sugars0) =>
                       (fn ((seenS, seenT, seen), prob) =>
                           let
                             val ctr_sugars = ctr_sugars0; (* FIXME *)
                             val dataTs = map #T ctr_sugars;
                             val ctrss = map #ctrs ctr_sugars;
                             val co_data = isa_cmd_of_ctr_sugars kind ctr_sugars;
                             val prob = co_data :: prob;
                           in
                             ((seenS, union (op =) dataTs seenT, seen), prob)
                             |> fold (fold (consider_type (depth + 1) o fastype_of)) ctrss
                           end)
                     | NONE => (fn (seen, prob) => (seen, ITypedecl T :: prob))))
                  (seens, prob)
              end));

    fun consider_term depth t =
      (case t of
        t1 $ t2 => fold (consider_term depth) [t1, t2]
      | Var (_, T) => consider_type depth T
      | Bound _ => I
      | Abs (_, T, t') =>
        consider_term depth t'
        #> consider_type depth T
      | _ => (fn (seens as (seenS, seenT, seen), prob) =>
          if member (op aconv) seen t then
            (seens, prob)
          else if depth > axioms_max_depth then
            raise Fail "too many nested axioms"
          else
            let
              val seen = t :: seen;
              val seens = (seenS, seenT, seen);
            in
              (case t of
                Const (x as (s, T)) =>
                (if is_const_builtin s orelse is_co_data_ctr ctxt x then
                   (seens, prob)
                 else
                   (seens, IConst t :: prob))
                |> consider_type depth T
              | Free (_, T) =>
                (seens, IConst t :: prob)
                |> consider_type depth T)
            end));

    val goal = atomize_toward_False ctxt goal0;
  in
    (([], [], []), [IGoal goal])
    |> consider_term 0 goal
    |> snd
  end;

fun str_of_isa_term_with_type ctxt t =
  Syntax.string_of_term ctxt t ^ " : " ^ Syntax.string_of_typ ctxt (fastype_of t);

fun str_of_isa_co_data_spec ctxt {typ, ctrs} =
  Syntax.string_of_typ ctxt typ ^ " =\n  " ^
  space_implode "\n| " (map (str_of_isa_term_with_type ctxt) ctrs);

fun str_of_isa_rec_spec ctxt {func, eqs} =
  str_of_isa_term_with_type ctxt func ^ " :=\n  " ^
  space_implode ";\n  " (map (Syntax.string_of_term ctxt) eqs);

fun str_of_isa_spec_spec ctxt {funcs, props} =
  space_implode " and " (map (str_of_isa_term_with_type ctxt) funcs) ^ " :=\n" ^
  space_implode ";\n  " (map (Syntax.string_of_term ctxt) props);

fun str_of_isa_command ctxt (ITypedecl T) = "typedecl " ^ Syntax.string_of_typ ctxt T
  | str_of_isa_command ctxt (IData specs) =
    "data " ^ str_of_and_list (str_of_isa_co_data_spec ctxt) specs
  | str_of_isa_command ctxt (ICodata specs) = 
    "data " ^ str_of_and_list (str_of_isa_co_data_spec ctxt) specs
  | str_of_isa_command ctxt (IConst t) = "const " ^ str_of_isa_term_with_type ctxt t
  | str_of_isa_command ctxt (IRec specs) = "rec " ^ str_of_and_list (str_of_isa_rec_spec ctxt) specs
  | str_of_isa_command ctxt (ISpec spec) = "spec " ^ str_of_isa_spec_spec ctxt spec
  | str_of_isa_command ctxt (IAxiom t) = "axiom " ^ Syntax.string_of_term ctxt t
  | str_of_isa_command ctxt (IGoal t) = "goal " ^ Syntax.string_of_term ctxt t;

fun str_of_isa_problem ctxt =
  map (suffix "." o str_of_isa_command ctxt) #> space_implode "\n\n" #> suffix "\n";

end;
