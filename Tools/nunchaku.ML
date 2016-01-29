(*  Title:      HOL/Tools/Nunchaku/nunchaku.ML
    Author:     Jasmin Blanchette, Inria Nancy, LORIA, MPII
    Copyright   2015, 2016

The core of the Nunchaku integration in Isabelle.
*)

signature NUNCHAKU =
sig
  type isa_model = Nunchaku_Reconstruct.isa_model

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

  val run_chaku_on_prop: Proof.state -> params -> mode -> int -> term list -> term ->
    string * isa_model option
  val run_chaku_on_subgoal: Proof.state -> params -> mode -> int -> string * isa_model option
end;

structure Nunchaku : NUNCHAKU =
struct

open Nunchaku_Util;
open Nunchaku_Collect;
open Nunchaku_Problem;
open Nunchaku_Translate;
open Nunchaku_Model;
open Nunchaku_Reconstruct;
open Nunchaku_Display;
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

fun none_true assigns = forall (curry (op <>) (SOME true) o snd) assigns;

fun has_lonely_bool_var (@{const Pure.conjunction} $ (@{const Trueprop} $ Free _) $ _) = true
  | has_lonely_bool_var _ = false;

val syntactic_sorts =
  @{sort "{default,zero,one,plus,minus,uminus,times,inverse,abs,sgn,ord,equal}"} @ @{sort numeral};

fun has_tfree_syntactic_sort (TFree (_, S as _ :: _)) = subset (op =) (S, syntactic_sorts)
  | has_tfree_syntactic_sort _ = false;

val has_syntactic_sorts = exists_type (exists_subtype has_tfree_syntactic_sort);

(* Give the soft timeout a chance. *)
val timeout_slack = seconds 1.0;

fun run_chaku_on_prop state
    ({mode_of_operation_params = {falsify, assms, spy, overlord, expect},
      scope_of_search_params = {wfs, ...},
      output_format_params = {verbose, debug, show_consts, evals, ...},
      timeout_params = {timeout, wf_timeout}, ...})
    mode i all_assms subgoal =
  let
    val ctxt = Proof.context_of state;

    val timer = Timer.startRealTimer ()

    val print = writeln;
    val print_n = if mode = Normal then writeln else K ();
    fun print_v f = if verbose then writeln (f ()) else ();
    fun print_d f = if debug then writeln (f ()) else ();

    val das_wort_Model = if falsify then "Countermodel" else "Model";
    val das_wort_model = if falsify then "countermodel" else "model";

    val tool_params = {overlord = overlord, debug = debug, timeout = timeout};

    fun run () =
      let
        val outcome as (outcome_code, _) =
          let
            val (poly_axioms, isa_problem) =
              isa_problem_of_subgoal ctxt falsify wfs debug wf_timeout evals
                (if assms then all_assms else []) subgoal;
            val _ = print_d (fn () => "*** ISA PROB ***\n" ^ str_of_isa_problem ctxt isa_problem);
            val ugly_nun_problem = nun_problem_of_isa ctxt isa_problem;
            val (nice_nun_problem, pool) = nice_nun_problem ugly_nun_problem;
            val _ = print_d (fn () => "*** NUN PROB ***\n" ^ str_of_nun_problem nice_nun_problem);

            fun print_any_hints () =
              if has_lonely_bool_var subgoal then
                print "Hint: Maybe you forgot a colon after the lemma's name?"
              else if has_syntactic_sorts subgoal then
                print "Hint: Maybe you forgot a type constraint?"
              else
                ();
          in
            (case solve_nun_problem tool_params nice_nun_problem of
              Unsat =>
              (print_n ("No " ^ das_wort_model ^ " exists (the goal is a theorem)"); (noneN, NONE))
            | Sat (output, _) =>
              let
                val nice_nun_model = nun_model_of_str output;
                val ugly_nun_model = ugly_nun_model pool nice_nun_model;
                val isa_model = isa_model_of_nun ctxt ugly_nun_model;
                val model_str = pretty_of_isa_model ctxt show_consts isa_model |> Pretty.string_of;
              in
                (case (null poly_axioms, none_true wfs) of
                  (true, true) =>
                  (print (das_wort_Model ^ ":\n" ^ model_str); print_any_hints ();
                   (genuineN, SOME isa_model))
                | (no_poly, no_wf) =>
                  let
                    val ignorings = []
                      |> not no_poly ? cons "polymorphic axioms"
                      |> not no_wf ? cons "unchecked well-foundedness";
                  in
                    (print (das_wort_Model ^ " (ignoring " ^ space_implode " and " ignorings ^
                       "):\n" ^ model_str ^
                       (if no_poly then
                          ""
                        else
                          "\nIgnored axioms:\n" ^
                          cat_lines (map (prefix "  " o Syntax.string_of_term ctxt) poly_axioms)));
                     print_any_hints ();
                     (quasi_genuineN, SOME isa_model))
                  end)
              end
            | Timeout => (print_n "Time out"; (unknownN, NONE))
            | Nunchaku_Var_Not_Set =>
              (print_n ("Variable $" ^ nunchaku_env_var ^ " not set"); (unknownN, NONE))
            | Nunchaku_Cannot_Execute =>
              (print_n "External tool \"nunchaku\" cannot execute"; (unknownN, NONE))
            | Nunchaku_Not_Found =>
              (print_n "External tool \"nunchaku\" not found"; (unknownN, NONE))
            | CVC4_Cannot_Execute =>
              (print_n "External tool \"cvc4\" cannot execute"; (unknownN, NONE))
            | CVC4_Not_Found => (print_n "External tool \"cvc4\" not found"; (unknownN, NONE))
            | Unknown_Error (code, msg) =>
              (print_n ("Unknown error: " ^ msg ^
                 (if code = 0 then "" else " (code " ^ string_of_int code ^ ")"));
               (unknownN, NONE)))
          end
          handle
            CYCLIC_DEPS () =>
            (print_n "Cyclic dependencies (or bug in Nunchaku)"; (unknownN, NONE))
          | TOO_DEEP_DEPS () =>
            (print_n "Too deep dependencies (or bug in Nunchaku)"; (unknownN, NONE))
          | TOO_META t =>
            (print_n ("Formula too meta for Nunchaku:\n" ^ Syntax.string_of_term ctxt t);
             (unknownN, NONE))
          | UNEXPECTED_POLYMORPHISM t =>
            (print_n ("Unexpected polymorphism in term\n" ^ Syntax.string_of_term ctxt t);
             (unknownN, NONE))
          | UNEXPECTED_VAR t =>
            (print_n ("Unexpected schematic variables in term\n" ^ Syntax.string_of_term ctxt t);
             (unknownN, NONE))
          | UNSUPPORTED_FUNC t =>
            (print_n ("Unsupported low-level constant in problem: " ^ Syntax.string_of_term ctxt t);
             (unknownN, NONE));
      in
        if expect = "" orelse outcome_code = expect then outcome
        else error ("Unexpected outcome: " ^ quote outcome_code)
      end;

    val _ = spying spy (fn () => (state, i, "starting " ^ str_of_mode mode ^ " mode"));

    val outcome as (outcome_code, _) =
      TimeLimit.timeLimit (Time.+ (timeout, timeout_slack)) run ()
      handle TimeLimit.TimeOut => (print_n "Time out"; (unknownN, NONE));

    val _ = print_v (fn () => "Total time: " ^ string_of_time (Timer.checkRealTimer timer));

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
      (writeln "No subgoal!"; (noneN, NONE))
    else
      let
        val subgoal = fst (Logic.goal_params goal i);
        val all_assms = map Thm.term_of (Assumption.all_assms_of ctxt);
      in
        run_chaku_on_prop state params mode i all_assms subgoal
      end
  end;

end;
