(*  Title:      HOL/Tools/Nunchaku/nunchaku.ML
    Author:     Jasmin Blanchette, Inria Nancy, LORIA, MPII
    Copyright   2015

The core of the Nunchaku integration in Isabelle.
*)

signature NUNCHAKU =
sig
  datatype mode = Auto_Try | Try | Normal

  type mode_of_operation_params =
    {falsify: bool,
     assms: bool,
     spy: bool,
     overlord: bool,
     expect: string}

  type scope_of_search_params =
    {cards_assigns: (typ option * int list) list,
     maxes_assigns: ((string * typ) option * int list) list,
     wfs: ((string * typ) option * bool option) list,
     iters_assigns: ((string * typ) option * int list) list,
     finitizes: (typ option * bool option) list,
     monos: (typ option * bool option) list,
     merge_type_vars: bool}

  type output_format_params =
    {verbose: bool,
     debug: bool,
     show_skolems: bool,
     show_consts: bool,
     max_potential: int,
     max_genuine: int,
     evals: term list,
     atomss: (typ option * string list) list,
     formats: (term option * int list) list}

  type optimization_params =
    {specialize: bool,
     whacks: term list,
     multithread: bool}

  type timeout_params =
    {timeout: Time.time,
     wf_timeout: Time.time}

  type params =
    {mode_of_operation_params: mode_of_operation_params,
     scope_of_search_params: scope_of_search_params,
     output_format_params: output_format_params,
     optimization_params: optimization_params,
     timeout_params: timeout_params}

  val genuineN: string
  val quasi_genuineN: string
  val potentialN: string
  val noneN: string
  val unknownN: string
  val where_is_nunchakuN: string

  val run_chaku_on_subgoal: Proof.state -> params -> mode -> int -> int -> string * string list
end;

structure Nunchaku : NUNCHAKU =
struct

open Nunchaku_Collect;
open Nunchaku_Problem;
open Nunchaku_Translate;

datatype mode = Auto_Try | Try | Normal;

type mode_of_operation_params =
  {falsify: bool,
   assms: bool,
   spy: bool,
   overlord: bool,
   expect: string};

type scope_of_search_params =
  {cards_assigns: (typ option * int list) list,
   maxes_assigns: ((string * typ) option * int list) list,
   wfs: ((string * typ) option * bool option) list,
   iters_assigns: ((string * typ) option * int list) list,
   finitizes: (typ option * bool option) list,
   monos: (typ option * bool option) list,
   merge_type_vars: bool};

type output_format_params =
  {verbose: bool,
   debug: bool,
   show_skolems: bool,
   show_consts: bool,
   max_potential: int,
   max_genuine: int,
   evals: term list,
   atomss: (typ option * string list) list,
   formats: (term option * int list) list};

type optimization_params =
  {specialize: bool,
   whacks: term list,
   multithread: bool};

type timeout_params =
  {timeout: Time.time,
   wf_timeout: Time.time};

type params =
  {mode_of_operation_params: mode_of_operation_params,
   scope_of_search_params: scope_of_search_params,
   output_format_params: output_format_params,
   optimization_params: optimization_params,
   timeout_params: timeout_params};

val genuineN = "genuine";
val quasi_genuineN = "quasi_genuine";
val potentialN = "potential";
val noneN = "none";
val unknownN = "unknown";

val where_is_nunchakuN = "where_is_nunchaku";

(* Give the inner timeout a chance. *)
val timeout_bonus = seconds 1.0;

fun plazy f = Pretty.para (f ());

fun run_chaku_on_prop state (params as {mode_of_operation_params = {expect, ...},
    timeout_params = {timeout, ...}, ...}) mode i n step subst def_assm_ts nondef_assm_ts goal =
  let
    val ctxt = Proof.context_of state;

    val print_n = if mode = Normal then writeln else K ();
  in
    if getenv "NUNCHAKU" = "" then
      (* The "expect" argument is deliberately ignored if the "nunchaku" command-line tool is
         missing is missing so that "Nunchaku_Examples" can be processed on any machine. *)
      (print_n (Pretty.string_of (plazy (K "External tool \"nunchaku\" not installed")));
       (where_is_nunchakuN, []))
    else
      let
        val unknown_outcome = (unknownN, []);
        val deadline = Time.+ (Time.now (), timeout);

        fun run goal =
          let
            val isa_prob = isa_problem_of_goal ctxt goal;
val _ = tracing ("isa_prob = " ^ @{make_string} isa_prob);
            val nun_prob = nun_problem_of_isa ctxt isa_prob;
val _ = tracing ("nun_prob = " ^ @{make_string} nun_prob);
            val nun_prob_str = str_of_nun_problem nun_prob;
val _ = tracing ("nun_prob_str = " ^ nun_prob_str);
          in
            (unknownN, [])
          end;

        val outcome as (outcome_code, _) =
          TimeLimit.timeLimit (Time.+ (timeout, timeout_bonus)) run goal
          handle
          (* TODO:
            TOO_LARGE (_, details) =>
            (print_n ("Limit reached: " ^ details ^ "."); unknown_outcome)
          | TOO_SMALL (_, details) =>
            (print_n ("Limit reached: " ^ details ^ "."); unknown_outcome)
          | Nunchaku_Tool.SYNTAX (_, details) =>
            (print_n ("Malformed Kodkodi output: " ^ details ^ "."); unknown_outcome)
          | *)
            TimeLimit.TimeOut => (print_n "Nitpick ran out of time."; unknown_outcome);
      in
        if expect = "" orelse outcome_code = expect then outcome
        else error ("Unexpected outcome: " ^ quote outcome_code)
      end
  end;

fun is_fixed_equation ctxt (Const (@{const_name Pure.eq}, _) $ Free (s, _) $ Const _) =
    Variable.is_fixed ctxt s
  | is_fixed_equation _ _ = false;

fun extract_fixed_frees ctxt (assms, t) =
  let
    val (subst, other_assms) =
      List.partition (is_fixed_equation ctxt) assms
      |>> map Logic.dest_equals;
  in
    (subst, other_assms, subst_atomic subst t)
  end;

fun run_chaku_on_subgoal state params mode i step =
  let
    val ctxt = Proof.context_of state;
    val t = state |> Proof.raw_goal |> #goal |> Thm.prop_of;
  in
    (case Logic.count_prems t of
      0 => (writeln "No subgoal!"; (noneN, []))
    | n =>
      let
        val t = Logic.goal_params t i |> fst;
        val assms = map Thm.term_of (Assumption.all_assms_of ctxt);
        val (subst, assms, t) = extract_fixed_frees ctxt (assms, t);
      in
        run_chaku_on_prop state params mode i n step subst [] assms t
      end)
  end;

end;
