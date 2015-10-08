(*  Title:      HOL/Tools/Nunchaku/nunchaku_util.ML
    Author:     Jasmin Blanchette, Inria Nancy, LORIA, MPII
    Copyright   2015

General-purpose functions used by Nunchaku.
*)

signature NUNCHAKU_UTIL =
sig
  val parse_bool_option: bool -> string -> string -> bool option
  val parse_time: string -> string -> Time.time
end;

structure Nunchaku_Util : NUNCHAKU_UTIL =
struct

val parse_bool_option = Sledgehammer_Util.parse_bool_option;
val parse_time = Sledgehammer_Util.parse_time;

end;
