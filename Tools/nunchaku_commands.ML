(*  Title:      HOL/Tools/Nunchaku/nunchaku_commands.ML
    Author:     Jasmin Blanchette, Inria Nancy, LORIA, MPII
    Copyright   2015

Adds the "nunchaku" and "nunchaku_params" commands to Isabelle/Isar's outer syntax.
*)

signature NUNCHAKU_COMMANDS =
sig
  
end;

structure Nunchaku_Commands : NUNCHAKU_COMMANDS =
struct

open Nunchaku_Util;
open Nunchaku;

type raw_param = string * string list;

val default_default_params = [];

val negated_params = [];

fun is_known_raw_param s =
  AList.defined (op =) default_default_params s orelse
  AList.defined (op =) negated_params s orelse
  member (op =) ["max", "show_all", "whack", "eval", "need", "atoms", "expect"] s orelse
  exists (fn p => String.isPrefix (p ^ " ") s)
    ["card", "max", "iter", "finitize", "dont_finitize", "mono", "non_mono", "wf", "non_wf",
     "format", "atoms"];

fun check_raw_param (s, _) =
  if is_known_raw_param s then () else error ("Unknown parameter: " ^ quote s);

fun unnegate_param_name name =
  (case AList.lookup (op =) negated_params name of
    NONE =>
    if String.isPrefix "dont_" name then SOME (unprefix "dont_" name)
    else if String.isPrefix "non_" name then SOME (unprefix "non_" name)
    else NONE
  | some_name => some_name);

fun normalize_raw_param (name, value) =
  (case unnegate_param_name name of
    SOME name' =>
    [(name',
      (case value of
        ["false"] => ["true"]
      | ["true"] => ["false"]
      | [] => ["false"]
      | _ => value))]
  | NONE =>
    if name = "show_all" then
      [("show_types", value), ("show_skolems", value), ("show_consts", value)]
    else
      [(name, value)]);

structure Data = Theory_Data
(
  type T = raw_param list
  val empty = default_default_params |> map (apsnd single)
  val extend = I
  fun merge data = AList.merge (op =) (K true) data
);

val set_default_raw_param = Data.map o fold (AList.update (op =)) o normalize_raw_param;
val default_raw_params = Data.get;

fun is_punctuation s = (s = "," orelse s = "-" orelse s = "\<emdash>");

fun stringify_raw_param_value [] = ""
  | stringify_raw_param_value [s] = s
  | stringify_raw_param_value (s1 :: s2 :: ss) =
    s1 ^ (if is_punctuation s1 orelse is_punctuation s2 then "" else " ") ^
    stringify_raw_param_value (s2 :: ss);

fun maxed_int_from_string min_int s = Int.max (min_int, the (Int.fromString s));

fun extract_params ctxt mode default_params override_params =
  let
    val override_params = maps normalize_raw_param override_params;
    val raw_params = rev override_params @ rev default_params;
    val raw_lookup = AList.lookup (op =) raw_params;
    val lookup = Option.map stringify_raw_param_value o raw_lookup;
    val lookup_string = the_default "" o lookup;

    fun general_lookup_bool option default_value name =
      (case lookup name of
        SOME s => parse_bool_option option name s
      | NONE => default_value);
    val lookup_bool = the o general_lookup_bool false (SOME false);
    val lookup_bool_option = general_lookup_bool true NONE;

    fun do_int name value =
      (case value of
        SOME s =>
        (case Int.fromString s of
          SOME i => i
        | NONE => error ("Parameter " ^ quote name ^ " must be assigned an integer value"))
      | NONE => 0);

    fun lookup_int name = do_int name (lookup name);

    fun lookup_int_option name =
      (case lookup name of
        SOME "smart" => NONE
      | value => SOME (do_int name value));

    fun int_range_from_string name min_int s =
      let
        val (k1, k2) =
          (case space_explode "-" s of
             [s] => the_default (s, s) (first_field "\<emdash>" s)
           | ["", s2] => ("-" ^ s2, "-" ^ s2)
           | [s1, s2] => (s1, s2)
           | _ => raise Option.Option)
          |> apply2 (maxed_int_from_string min_int);
      in
        if k1 <= k2 then k1 upto k2 else k1 downto k2
      end
      handle Option.Option =>
        error ("Parameter " ^ quote name ^ " must be assigned a sequence of integers");

    fun int_seq_from_string name min_int s =
      maps (int_range_from_string name min_int) (space_explode "," s);

    fun lookup_int_seq name min_int =
      (case lookup name of
        SOME s => (case int_seq_from_string name min_int s of
                     [] => [min_int]
                   | value => value)
      | NONE => [min_int]);

    fun lookup_assigns read prefix default convert =
      (NONE, convert (the_default default (lookup prefix))) ::
      map (fn (name, value) => (SOME (read (String.extract (name, size prefix + 1, NONE))),
          convert (stringify_raw_param_value value)))
        (filter (String.isPrefix (prefix ^ " ") o fst) raw_params);

    fun lookup_ints_assigns read prefix min_int =
      lookup_assigns read prefix (signed_string_of_int min_int)
        (int_seq_from_string prefix min_int);

    fun lookup_bool_option_assigns read prefix =
      lookup_assigns read prefix "" (parse_bool_option true prefix);

    fun lookup_strings_assigns read prefix =
      lookup_assigns read prefix "" (space_explode " ");

    fun lookup_time name =
      (case lookup name of
        SOME s => parse_time name s
      | NONE => Time.zeroTime);

    val read_type_polymorphic =
      Syntax.read_typ ctxt #> Logic.mk_type
      #> singleton (Variable.polymorphic ctxt) #> Logic.dest_type;
    val read_term_polymorphic =
      Syntax.read_term ctxt #> singleton (Variable.polymorphic ctxt);
    val lookup_term_list_option_polymorphic =
      AList.lookup (op =) raw_params #> Option.map (map read_term_polymorphic);
    val read_const_polymorphic = read_term_polymorphic #> dest_Const;





    val cards_assigns = lookup_ints_assigns read_type_polymorphic "card" 1;
    val maxes_assigns = lookup_ints_assigns read_const_polymorphic "max" ~1;
    val iters_assigns = lookup_ints_assigns read_const_polymorphic "iter" 0;
    val bitss = lookup_int_seq "bits" 1;
    val bisim_depths = lookup_int_seq "bisim_depth" ~1;
    val boxes = lookup_bool_option_assigns read_type_polymorphic "box";
    val finitizes = lookup_bool_option_assigns read_type_polymorphic "finitize";
    val monos =
      if mode = Auto_Try then [(NONE, SOME true)]
      else lookup_bool_option_assigns read_type_polymorphic "mono";
    val wfs = lookup_bool_option_assigns read_const_polymorphic "wf";
    val falsify = lookup_bool "falsify";
    val debug = (mode <> Auto_Try andalso lookup_bool "debug");
    val verbose = debug orelse (mode <> Auto_Try andalso lookup_bool "verbose");
    val overlord = lookup_bool "overlord";
    val spy = getenv "NUNCHAKU_SPY" = "yes" orelse lookup_bool "spy";
    val assms = lookup_bool "assms";
    val whacks = lookup_term_list_option_polymorphic "whack" |> these;
    val merge_type_vars = lookup_bool "merge_type_vars";
    val specialize = lookup_bool "specialize";
    val total_consts = lookup_bool_option "total_consts";
    val timeout = lookup_time "timeout";
    val wf_timeout = lookup_time "wf_timeout";
    val multithread = mode = Normal andalso lookup_bool "multithread";
    val show_types = debug orelse lookup_bool "show_types";
    val show_skolems = debug orelse lookup_bool "show_skolems";
    val show_consts = debug orelse lookup_bool "show_consts";
    val evals = these (lookup_term_list_option_polymorphic "eval");
    val formats = lookup_ints_assigns read_term_polymorphic "format" 0;
    val atomss = lookup_strings_assigns read_type_polymorphic "atoms";
    val max_potential = if mode = Normal then Int.max (0, lookup_int "max_potential") else 0;
    val max_genuine = Int.max (0, lookup_int "max_genuine");
    val expect = lookup_string "expect";

    val mode_of_operation_params =
      {falsify = falsify, assms = assms, spy = spy, overlord = overlord,
       expect = expect};

    val scope_of_search_params =
      {cards_assigns = cards_assigns, maxes_assigns = maxes_assigns, wfs = wfs,
       iters_assigns = iters_assigns, finitizes = finitizes, monos = monos,
       merge_type_vars = merge_type_vars};

    val output_format_params =
      {verbose = verbose, debug = debug, show_skolems = show_skolems, show_consts = show_consts,
       max_potential = max_potential, max_genuine = max_genuine, evals = evals, atomss = atomss,
       formats = formats};

    val optimization_params =
      {specialize = specialize, whacks = whacks, multithread = multithread};

    val timeout_params =
      {timeout = timeout, wf_timeout = wf_timeout};
  in
    {mode_of_operation_params = mode_of_operation_params,
     scope_of_search_params = scope_of_search_params,
     output_format_params = output_format_params,
     optimization_params = optimization_params,
     timeout_params = timeout_params}
  end;

fun default_params thy =
  extract_params (Proof_Context.init_global thy) Normal (default_raw_params thy)
  o map (apsnd single);

val parse_key = Scan.repeat1 Parse.typ_group >> space_implode " ";
val parse_value =
  Scan.repeat1 (Parse.minus >> single
    || Scan.repeat1 (Scan.unless Parse.minus (Parse.name || Parse.float_number))
    || @{keyword ","} |-- Parse.number >> prefix "," >> single)
  >> flat;
val parse_param = parse_key -- Scan.optional (@{keyword "="} |-- parse_value) [];
val parse_params = Scan.optional (@{keyword "["} |-- Parse.list parse_param --| @{keyword "]"}) [];

fun run_chaku override_params mode i step state =
  let
    val thy = Proof.theory_of state;
    val ctxt = Proof.context_of state;
    val _ = List.app check_raw_param override_params;
    val params = extract_params ctxt mode (default_raw_params thy) override_params;
  in
    (if mode = Auto_Try then perhaps o try else fn f => fn x => f x)
      (fn _ => run_chaku_on_subgoal state params mode i step) (unknownN, [])
    |> `(fn (outcome_code, _) => outcome_code = genuineN)
  end;

fun string_for_raw_param (name, value) =
  name ^ " = " ^ stringify_raw_param_value value;

fun nunchaku_params_trans params =
  Toplevel.theory (fold set_default_raw_param params
    #> tap (fn thy => writeln ("Default parameters for Nunchaku:\n" ^
      (case rev (default_raw_params thy) of
        [] => "none"
      | params =>
        (map check_raw_param params;
         params |> map string_for_raw_param |> sort_strings |> cat_lines)))));

val _ =
  Outer_Syntax.command @{command_keyword nunchaku}
    "try to find a counterexample for a given subgoal using Nunchaku"
    (parse_params -- Scan.optional Parse.nat 1 >> (fn (params, i) =>
      Toplevel.keep_proof (fn state =>
        ignore (run_chaku params Normal i (Toplevel.proof_position_of state)
          (Toplevel.proof_of state)))));

val _ =
  Outer_Syntax.command @{command_keyword nunchaku_params}
    "set and display the default parameters for Nunchaku"
    (parse_params #>> nunchaku_params_trans);

end;
