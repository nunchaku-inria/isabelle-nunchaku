(*  Title:      HOL/Tools/Nunchaku/nunchaku.ML
    Author:     Jasmin Blanchette, Inria Nancy, LORIA, MPII
    Copyright   2015

The core of the Nunchaku integration in Isabelle.
*)

signature NUNCHAKU =
sig
  datatype mode = Auto_Try | Try | Normal | TPTP

  type mode_of_operation_params =
    {falsify: bool,
     assms: bool,
     spy: bool,
     overlord: bool,
     expect: string}

  type scope_of_search_params =
    {wfs: ((string * typ) option * bool option) list,
     finitizes: (typ option * bool option) list,
     monos: (typ option * bool option) list,
     merge_type_vars: bool}

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

  val run_chaku_on_subgoal: Proof.state -> params -> mode -> int -> int -> string * string list
end;

structure Nunchaku : NUNCHAKU =
struct

open Nunchaku_Collect;
open Nunchaku_Problem;
open Nunchaku_Translate;
open Nunchaku_Tool;

datatype mode = Auto_Try | Try | Normal | TPTP;

type mode_of_operation_params =
  {falsify: bool,
   assms: bool,
   spy: bool,
   overlord: bool,
   expect: string};

type scope_of_search_params =
  {wfs: ((string * typ) option * bool option) list,
   finitizes: (typ option * bool option) list,
   monos: (typ option * bool option) list,
   merge_type_vars: bool};

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

(* Give the soft timeout a chance. *)
val timeout_slack = seconds 1.0;

fun run_chaku_on_prop state (params as {mode_of_operation_params = {falsify, overlord, expect, ...},
    output_format_params = {debug, ...}, timeout_params = {timeout, ...}, ...}) mode i n step
    def_assm_ts nondef_assm_ts goal =
  let
    val ctxt = Proof.context_of state;

    val print = writeln;
    val print_nt =
      (case mode of
        Normal => writeln
      | TPTP => writeln o prefix "%%% "
      | _ => K ());

    val das_wort_Model = if falsify then "Countermodel" else "Model";
    val das_wort_model = if falsify then "countermodel" else "model";
  in
    if getenv nunchaku_env_var = "" then
      (* The "expect" argument is deliberately ignored if the "nunchaku" command-line tool is
         missing so that "Nunchaku_Examples" can be processed on any machine. *)
      (print_nt ("$" ^ nunchaku_env_var ^ " not set"); (no_nunchakuN, []))
    else
      let
        val deadline = Time.+ (Time.now (), timeout);

        val tool_params = {overlord = overlord, debug = debug, timeout = timeout};

        fun run () =
          let
            val (too_meta, poly_axioms, isa_prob) = isa_problem_of_goal ctxt falsify goal;
val _ = tracing ("*** ISA PROB ***\n" ^ str_of_isa_problem ctxt isa_prob);

            val outcome as (outcome_code, _) =
              (case too_meta of
                SOME t =>
                (print_nt ("Problem too meta for Nunchaku (because of proposition " ^
                   Syntax.string_of_term ctxt t ^ ")"); (unknownN, []))
              | NONE =>
                let
                  val ugly_nun_prob = nun_problem_of_isa ctxt isa_prob;
                  val (nice_nun_prob, pool) = nice_nun_problem ugly_nun_prob;
val _ = tracing ("*** NUN PROB ***\n" ^ str_of_nun_problem nice_nun_prob);
                in
                  (case solve_nun_problem tool_params nice_nun_prob of
                    Unsat => (print_nt ("No " ^ das_wort_model ^ " exists"); (noneN, []))
                  | Sat (output, _) =>
                    if null poly_axioms then
                      (print (das_wort_Model ^ ":\n" ^ output); (genuineN, []))
                    else
                      (print (das_wort_Model ^ " (ignoring polymorphic axioms):\n" ^ output ^
                         "\nIgnored axioms:\n" ^
                         cat_lines (map (prefix "  " o Syntax.string_of_term ctxt) poly_axioms));
                       (quasi_genuineN, []))
                  | Timeout => (print_nt "Time out"; (unknownN, []))
                  | Nunchaku_Not_Found =>
                    (print_nt "External tool \"nunchaku\" not found"; (unknownN, []))
                  | CVC4_Not_Found => (print_nt "External tool \"cvc4\" not found"; (unknownN, []))
                  | Unknown_Error (_, msg) => (print_nt ("Unknown error: " ^ msg); (unknownN, [])))
                end);
          in
            if expect = "" orelse outcome_code = expect then outcome
            else error ("Unexpected outcome: " ^ quote outcome_code)
          end;

        val outcome as (outcome_code, _) =
          TimeLimit.timeLimit (Time.+ (timeout, timeout_slack)) run ()
          handle TimeLimit.TimeOut => (print_nt "Time out"; (unknownN, []));
      in
        if expect = "" orelse outcome_code = expect then outcome
        else error ("Unexpected outcome: " ^ quote outcome_code)
      end
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
      in
        run_chaku_on_prop state params mode i n step [] assms t
      end)
  end;

end;
