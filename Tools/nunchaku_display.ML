(*  Title:      HOL/Tools/Nunchaku/nunchaku_display.ML
    Author:     Jasmin Blanchette, Inria Nancy, LORIA, MPII
    Copyright   2015, 2016

Pretty printing of Isabelle/HOL models for Nunchaku.
*)

signature NUNCHAKU_DISPLAY =
sig
  type isa_model = Nunchaku_Reconstruct.isa_model

  val pretty_of_isa_model: Proof.context -> bool -> isa_model -> Pretty.T
end;

structure Nunchaku_Display : NUNCHAKU_DISPLAY =
struct

open Nunchaku_Util;
open Nunchaku_Reconstruct;

val indent_size = 2;

fun sorting_str_of_typ (TFree (s, _)) = "a" ^ s
  | sorting_str_of_typ (Type (s, Ts)) = "b" ^ s ^ space_implode " " (map sorting_str_of_typ Ts)
  | sorting_str_of_typ (TVar _) = "X";

fun sorting_str_of_term (Const (s, T)) = "b" ^ s ^ sorting_str_of_typ T
  | sorting_str_of_term (Free (s, _)) = "a" ^ s
  | sorting_str_of_term (t $ u) = sorting_str_of_term t ^ " " ^ sorting_str_of_term u
  | sorting_str_of_term (Abs (_, T, t)) = "c" ^ sorting_str_of_typ T ^ " " ^ sorting_str_of_term t
  | sorting_str_of_term _ = "X";

fun pretty_of_isa_model ctxt show_consts {type_model, free_model, const_model, skolem_model} =
  let
    fun pretty_of_typ_entry (T, atoms) =
      Pretty.block (Pretty.breaks [Syntax.pretty_typ ctxt T, Pretty.str "=",
         Pretty.enum "," "{" "}" (map (Syntax.pretty_term ctxt) atoms)]);

    fun pretty_of_term_entry (t, value) =
      Pretty.block (Pretty.breaks [Syntax.pretty_term ctxt t, Pretty.str "=",
         Syntax.pretty_term ctxt value]);

    fun chunks_of_entries sorting_str_of pretty_of title entries =
      if not (null entries) then
        Pretty.str (title ^ plural_s_for_list entries ^ ":")
        :: map (Pretty.indent indent_size o pretty_of)
          (sort_by (sorting_str_of o fst) entries)
      else
        [];

    val chunks = chunks_of_entries sorting_str_of_typ pretty_of_typ_entry "Type" type_model @
      chunks_of_entries sorting_str_of_term pretty_of_term_entry "Free variable" free_model @
      (if show_consts then
         chunks_of_entries sorting_str_of_term pretty_of_term_entry "Constant" const_model @
         chunks_of_entries sorting_str_of_term pretty_of_term_entry "Skolem constant" skolem_model
       else
         []);
  in
    Pretty.chunks (if null chunks then [Pretty.str "Empty assignment"] else chunks)
  end;

end;
