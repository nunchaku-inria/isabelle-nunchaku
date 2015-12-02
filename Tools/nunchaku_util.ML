(*  Title:      HOL/Tools/Nunchaku/nunchaku_util.ML
    Author:     Jasmin Blanchette, Inria Nancy, LORIA, MPII
    Copyright   2015

General-purpose functions used by Nunchaku.
*)

signature NUNCHAKU_UTIL =
sig
  val parens: string -> string
  val parens_if_space: string -> string
  val str_of_arg_list: ('a -> string) -> 'a list -> string
  val str_of_and_list: ('a -> string) -> 'a list -> string
  val parse_bool_option: bool -> string -> string -> bool option
  val parse_time: string -> string -> Time.time
  val ascii_of: string -> string
  val unascii_of: string -> string
  val with_overlord_file: string -> string -> (Path.T -> 'a) -> 'a
  val with_tmp_or_overlord_file: bool -> string -> string -> (Path.T -> 'a) -> 'a
  val attach_typeS: term -> term
end;

structure Nunchaku_Util : NUNCHAKU_UTIL =
struct

val parens = enclose "(" ")";

fun parens_if_space s = s |> String.isSubstring " " s ? parens;

fun str_of_arg_list str_of_arg =
  map (prefix " " o parens_if_space o str_of_arg) #> space_implode "";

fun str_of_and_list str_of_elem =
  map str_of_elem #> space_implode "\nand ";

val parse_bool_option = Sledgehammer_Util.parse_bool_option;
val parse_time = Sledgehammer_Util.parse_time;
val ascii_of = ATP_Problem_Generate.ascii_of;
val unascii_of = ATP_Problem_Generate.unascii_of;

fun with_overlord_file name ext f =
  let val path = Path.explode ("$ISABELLE_HOME_USER/" ^ name ^ "." ^ ext) in
    f path
  end;

fun with_tmp_or_overlord_file overlord =
  if overlord then with_overlord_file else Isabelle_System.with_tmp_file;

(* Clone from "HOL/Tools/inductive_realizer.ML" *)
val attach_typeS =
  map_types (map_atyps
    (fn TFree (s, []) => TFree (s, @{sort type})
      | TVar (ixn, []) => TVar (ixn, @{sort type})
      | T => T));

end;
