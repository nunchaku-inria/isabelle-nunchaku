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
    {wfs: ((string * typ) option * bool option) list,
     monos: (typ option * bool option) list}

  type output_format_params =
    {verbose: bool,
     debug: bool,
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
  val no_nunchakuN: string

  val run_chaku_on_subgoal: Proof.state -> params -> mode -> int -> string * string list
end;

structure Nunchaku : NUNCHAKU =
struct

open Nunchaku_Util;
open Nunchaku_Collect;
open Nunchaku_Problem;
open Nunchaku_Translate;
open Nunchaku_Tool;

datatype mode = Auto_Try | Try | Normal;

type mode_of_operation_params =
  {falsify: bool,
   assms: bool,
   spy: bool,
   overlord: bool,
   expect: string};

type scope_of_search_params =
  {wfs: ((string * typ) option * bool option) list,
   monos: (typ option * bool option) list};

type output_format_params =
  {verbose: bool,
   debug: bool,
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

val no_nunchakuN = "no_nunchaku";

fun str_of_mode Auto_Try = "Auto_Try"
  | str_of_mode Try = "Try"
  | str_of_mode Normal = "Normal";

(* Give the soft timeout a chance. *)
val timeout_slack = seconds 1.0;

fun run_chaku_on_prop state
    (params as {mode_of_operation_params = {falsify, assms, spy, overlord, expect},
       output_format_params = {debug, ...}, timeout_params = {timeout, ...}, ...})
    mode i all_assms subgoal =
  let
    val ctxt = Proof.context_of state;

    val print = writeln;
    val print_n =
      (case mode of
        Normal => writeln
      | _ => K ());

    val das_wort_Model = if falsify then "Countermodel" else "Model";
    val das_wort_model = if falsify then "countermodel" else "model";

    val tool_params = {overlord = overlord, debug = debug, timeout = timeout};

    fun run () =
      let
        val (too_meta, poly_axioms, isa_prob) =
          isa_problem_of_subgoal ctxt falsify (if assms then all_assms else []) subgoal;
val _ = tracing ("*** ISA PROB ***\n" ^ str_of_isa_problem ctxt isa_prob);

        val outcome as (outcome_code, _) =
          (case too_meta of
            SOME t =>
            (print_n ("Problem too meta for Nunchaku (because of proposition " ^
               Syntax.string_of_term ctxt t ^ ")"); (unknownN, []))
          | NONE =>
            let
              val ugly_nun_prob = nun_problem_of_isa ctxt isa_prob;
              val (nice_nun_prob, pool) = nice_nun_problem ugly_nun_prob;
val _ = tracing ("*** NUN PROB ***\n" ^ str_of_nun_problem nice_nun_prob);
            in
              (case solve_nun_problem tool_params nice_nun_prob of
                Unsat => (print_n ("No " ^ das_wort_model ^ " exists"); (noneN, []))
              | Sat (output, _) =>
                if null poly_axioms then
                  (print (das_wort_Model ^ ":\n" ^ output); (genuineN, []))
                else
                  (print (das_wort_Model ^ " (ignoring polymorphic axioms):\n" ^ output ^
                     "\nIgnored axioms:\n" ^
                     cat_lines (map (prefix "  " o Syntax.string_of_term ctxt) poly_axioms));
                   (quasi_genuineN, []))
              | Timeout => (print_n "Time out"; (unknownN, []))
              | Nunchaku_Var_Not_Set =>
                (print_n ("Variable $" ^ nunchaku_env_var ^ " not set"); (unknownN, []))
              | Nunchaku_Cannot_Execute =>
                (print_n "External tool \"nunchaku\" cannot execute"; (unknownN, []))
              | Nunchaku_Not_Found =>
                (print_n "External tool \"nunchaku\" not found"; (unknownN, []))
              | CVC4_Cannot_Execute =>
                (print_n "External tool \"cvc4\" cannot execute"; (unknownN, []))
              | CVC4_Not_Found => (print_n "External tool \"cvc4\" not found"; (unknownN, []))
              | Unknown_Error (code, msg) =>
                (print_n ("Unknown error: " ^ msg ^
                   (if code = 0 then "" else " (code " ^ string_of_int code ^ ")"));
                 (unknownN, [])))
            end);
      in
        if expect = "" orelse outcome_code = expect then outcome
        else error ("Unexpected outcome: " ^ quote outcome_code)
      end;

    val _ = spying spy (fn () => (state, i, "starting " ^ str_of_mode mode ^ " mode"));

    val outcome as (outcome_code, _) =
      TimeLimit.timeLimit (Time.+ (timeout, timeout_slack)) run ()
      handle TimeLimit.TimeOut => (print_n "Time out"; (unknownN, []));

    val _ = spying spy (fn () => (state, i, "outcome: " ^ outcome_code));
  in
    if expect = "" orelse outcome_code = expect then outcome
    else error ("Unexpected outcome: " ^ quote outcome_code)
  end;

fun run_chaku_on_subgoal state params mode i =
  let
    val ctxt = Proof.context_of state;
    val goal = Thm.prop_of (#goal (Proof.raw_goal state));
  in
    if Logic.count_prems goal = 0 then
      (writeln "No subgoal!"; (noneN, []))
    else
      let
        val subgoal = fst (Logic.goal_params goal i);
        val all_assms = map Thm.term_of (Assumption.all_assms_of ctxt);
      in
        run_chaku_on_prop state params mode i all_assms subgoal
      end
  end;

end;
