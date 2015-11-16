(*  Title:      HOL/Tools/Nunchaku/nunchaku_util.ML
    Author:     Jasmin Blanchette, Inria Nancy, LORIA, MPII
    Copyright   2015

General-purpose functions used by Nunchaku.
*)

signature NUNCHAKU_UTIL =
sig
  val parse_bool_option: bool -> string -> string -> bool option
  val parse_time: string -> string -> Time.time
  val ascii_of: string -> string
  val with_overlord_file: string -> string -> (Path.T -> 'a) -> 'a
  val with_tmp_or_overlord_file: bool -> string -> string -> (Path.T -> 'a) -> 'a
end;

structure Nunchaku_Util : NUNCHAKU_UTIL =
struct

val parse_bool_option = Sledgehammer_Util.parse_bool_option;
val parse_time = Sledgehammer_Util.parse_time;
val ascii_of = ATP_Problem_Generate.ascii_of;

fun with_overlord_file name ext f =
  let val path = Path.explode ("$ISABELLE_HOME_USER/" ^ name ^ "." ^ ext) in
    f path
  end;

fun with_tmp_or_overlord_file overlord =
  if overlord then with_overlord_file else Isabelle_System.with_tmp_file;

end;
