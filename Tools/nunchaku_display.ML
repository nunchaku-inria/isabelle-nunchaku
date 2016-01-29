(*  Title:      HOL/Tools/Nunchaku/nunchaku_display.ML
    Author:     Jasmin Blanchette, Inria Nancy, LORIA, MPII
    Copyright   2015, 2016

Pretty printing of Isabelle/HOL models for Nunchaku.
*)

signature NUNCHAKU_DISPLAY =
sig
  type isa_model = Nunchaku_Reconstruct.isa_model

  val pretty_of_isa_model: isa_model -> Pretty.T
end;

structure Nunchaku_Display : NUNCHAKU_DISPLAY =
struct

open Nunchaku_Reconstruct;

fun pretty_of_isa_model model =
  Pretty.chunks [];

end;
