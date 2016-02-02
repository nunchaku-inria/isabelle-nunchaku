(*  Title:      HOL/Tools/Nunchaku/nunchaku_display.ML
    Author:     Jasmin Blanchette, Inria Nancy, LORIA, MPII
    Copyright   2015, 2016

Pretty printing of Isabelle/HOL models for Nunchaku.
*)

signature NUNCHAKU_DISPLAY =
sig
  type isa_model = Nunchaku_Reconstruct.isa_model

  val pretty_of_isa_model_opt: Proof.context -> bool option -> isa_model option -> Pretty.T
end;

structure Nunchaku_Display : NUNCHAKU_DISPLAY =
struct

open Nunchaku_Util;
open Nunchaku_Reconstruct;

val indent_size = 2;

val pretty_indent = Pretty.indent indent_size;

fun sorting_str_of_typ (TFree (s, _)) = "a" ^ s
  | sorting_str_of_typ (Type (s, Ts)) = "b" ^ s ^ space_implode " " (map sorting_str_of_typ Ts)
  | sorting_str_of_typ (TVar _) = "X";

fun sorting_str_of_term (Const (s, T)) = "b" ^ s ^ sorting_str_of_typ T
  | sorting_str_of_term (Free (s, _)) = "a" ^ s
  | sorting_str_of_term (t $ u) = sorting_str_of_term t ^ " " ^ sorting_str_of_term u
  | sorting_str_of_term (Abs (_, T, t)) = "c" ^ sorting_str_of_typ T ^ " " ^ sorting_str_of_term t
  | sorting_str_of_term _ = "X";

fun pretty_of_isa_model_opt _ _ NONE =
    pretty_indent (Pretty.str "Model unavailable (internal error)")
  | pretty_of_isa_model_opt ctxt0 show_consts
      (SOME {type_model, free_model, const_model, skolem_model}) =
    let
      val ctxt = ctxt0 (* TODO: keep or remove: |> Config.put show_question_marks false *);

      fun pretty_of_typ_entry (T, atoms) =
        Pretty.block (Pretty.breaks [Syntax.pretty_typ ctxt T, Pretty.str "=",
           Pretty.enum "," "{" "}" (map (Syntax.pretty_term ctxt) atoms)]);

      fun pretty_of_term_entry (t, value) =
        Pretty.block (Pretty.breaks [Syntax.pretty_term ctxt t, Pretty.str "=",
           Syntax.pretty_term ctxt value]);

      fun chunks_of_entries sorting_str_of pretty_of title entries =
        if not (null entries) then
          (if title = "" then [] else [Pretty.str (title ^ plural_s_for_list entries ^ ":")]) @
          map (pretty_indent o pretty_of) (sort_by (sorting_str_of o fst) entries)
        else
          [];

      val chunks =
        (if null free_model then
           [pretty_indent (Pretty.str "No free variables")]
         else
           chunks_of_entries sorting_str_of_term pretty_of_term_entry "" free_model) @
        (if show_consts |> the_default true then
           chunks_of_entries sorting_str_of_term pretty_of_term_entry "Skolem constant" skolem_model
         else
           []) @
        (if show_consts |> the_default (null free_model) then
           chunks_of_entries sorting_str_of_term pretty_of_term_entry "Constant" const_model
         else
           []) @
        chunks_of_entries sorting_str_of_typ pretty_of_typ_entry "Type" type_model;
    in
      Pretty.chunks chunks
    end;

end;
