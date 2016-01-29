(*  Title:      HOL/Tools/Nunchaku/nunchaku_reconstruct.ML
    Author:     Jasmin Blanchette, Inria Nancy, LORIA, MPII
    Copyright   2015, 2016

Reconstruction of Nunchaku models in Isabelle/HOL.
*)

signature NUNCHAKU_RECONSTRUCT =
sig
  type nun_model = Nunchaku_Model.nun_model

  type typ_entry = typ * typ list
  type term_entry = term * term

  type isa_model =
    {typ_model: typ_entry list,
     skolem_model: term_entry list,
     const_model: term_entry list}

  val isa_model_of_nun: nun_model -> isa_model
end;

structure Nunchaku_Reconstruct : NUNCHAKU_RECONSTRUCT =
struct

open Nunchaku_Model;

type typ_entry = typ * typ list;
type term_entry = term * term;

type isa_model =
  {typ_model: typ_entry list,
   skolem_model: term_entry list,
   const_model: term_entry list};

fun isa_model_of_nun {ty_model, skolem_model, const_model} =
  {typ_model = [], skolem_model = [], const_model = []};

end;
