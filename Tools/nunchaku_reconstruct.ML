(*  Title:      HOL/Tools/Nunchaku/nunchaku_reconstruct.ML
    Author:     Jasmin Blanchette, Inria Nancy, LORIA, MPII
    Copyright   2015, 2016

Reconstruction of Nunchaku models in Isabelle/HOL.
*)

signature NUNCHAKU_RECONSTRUCT =
sig
  type nun_model = Nunchaku_Model.nun_model

  type typ_entry = typ * term list
  type term_entry = term * term

  type isa_model =
    {type_model: typ_entry list,
     free_model: term_entry list,
     const_model: term_entry list,
     skolem_model: term_entry list}

  val str_of_isa_model: Proof.context -> isa_model -> string

  val isa_model_of_nun: Proof.context -> (typ option * string list) list -> nun_model -> isa_model
end;

structure Nunchaku_Reconstruct : NUNCHAKU_RECONSTRUCT =
struct

open Nunchaku_Util;
open Nunchaku_Problem;
open Nunchaku_Translate;
open Nunchaku_Model;

type typ_entry = typ * term list;
type term_entry = term * term;

type isa_model =
  {type_model: typ_entry list,
   free_model: term_entry list,
   const_model: term_entry list,
   skolem_model: term_entry list};

fun str_of_typ_entry ctxt (T, ts) =
  "type " ^ Syntax.string_of_typ ctxt T  ^
  " := {" ^ commas (map (Syntax.string_of_term ctxt) ts) ^ "}.";

fun str_of_term_entry ctxt (tm, value) =
  "val " ^ Syntax.string_of_term ctxt tm ^ " := " ^ Syntax.string_of_term ctxt value ^ ".";

fun str_of_isa_model ctxt {type_model, free_model, const_model, skolem_model} =
  map (str_of_typ_entry ctxt) type_model @ "" :: map (str_of_term_entry ctxt) free_model @ "" ::
  map (str_of_term_entry ctxt) const_model @ "" :: map (str_of_term_entry ctxt) skolem_model
  |> cat_lines;

fun typ_of_nun ctxt =
  let
    fun typ_of (NType (id, tys)) =
      let val Ts = map typ_of tys in
        if id = nun_dummy then
          dummyT
        else if id = nun_prop then
          @{typ bool}
        else if id = nun_fun then
          Type (@{type_name fun}, Ts)
        else
          (case try str_of_nun_const id of
            SOME (args, s) =>
            (* TODO: more precise type *)
            let val tys = map (K nun_dummy_ty) args in
              Type (s, map typ_of tys)
            end
          | NONE =>
            (case try str_of_nun_var id of
              SOME s => TFree (Proof_Context.check_tfree ctxt (flip_quote s, dummyS))
            | NONE => raise Fail ("unknown type constructor: " ^ quote (str_of_ident id))))
      end;
  in
    typ_of
  end;

fun term_of_nun ctxt atomss =
  let
    val thy = Proof_Context.theory_of ctxt;

    val typ_of = typ_of_nun ctxt;

    fun one_letter_of s =
      let val c = String.sub (Long_Name.base_name s, 0) in
        String.str (if Char.isAlpha c then c else #"x")
      end;

    fun base_of_typ (Type (s, _)) = s
      | base_of_typ (TFree (s, _)) = flip_quote s
      | base_of_typ (TVar ((s, _), _)) = flip_quote s;

    fun nth_atom T j =
      let val ss = these (triple_lookup (typ_match thy) atomss T) in
        if j >= 0 andalso j < length ss then nth ss j
        else one_letter_of (base_of_typ T) ^ nat_subscript (j + 1)
      end;

    fun term_of (NAtom (j, ty)) = let val T = typ_of ty in Var ((nth_atom T j, 0), T) end
      | term_of (NConst (id, tys0, ty)) =
        if id = nun_false then
          @{const False}
        else if id = nun_true then
          @{const True}
        else
          (case try str_of_nun_const id of
            SOME (args, s) =>
            (* TODO: more precise type *)
            let val tys = map (K nun_dummy_ty) args in
              Sign.mk_const thy (s, map typ_of (tys @ tys0))
            end
          | NONE =>
            (case try str_of_nun_var id of
              SOME s => Free (s, typ_of ty)
            | NONE => raise Fail ("unknown constant: " ^ quote (str_of_ident id))))
      | term_of (NVar (id, ty)) =
        (case try str_of_nun_var id of
          SOME s => Var ((s, 0), typ_of ty)
        | NONE => Var ((str_of_ident id, 1), typ_of ty) (* Nunchaku-generated bound variable *))
      | term_of (NAbs (var, body)) = lambda (term_of var) (term_of body)
      | term_of (tm as NMatch _) = Var (("case", 0), typ_of (ty_of tm)) (* TODO *)
      | term_of (NApp (func, arg)) = term_of func $ term_of arg;
  in
    term_of
  end;

fun isa_typ_entry_of_nun ctxt atomss (ty, atoms) =
  (typ_of_nun ctxt ty, map (term_of_nun ctxt atomss) atoms);

fun isa_term_entry_of_nun ctxt atomss (tm, value) =
  (term_of_nun ctxt atomss tm, term_of_nun ctxt atomss value);

fun isa_model_of_nun ctxt atomss {type_model, const_model, skolem_model} =
  let
    val const_model' = map (isa_term_entry_of_nun ctxt atomss) const_model;
    val (free_model, const_model'') = List.partition (is_Free o fst) const_model';
  in
    {type_model = map (isa_typ_entry_of_nun ctxt atomss) type_model, free_model = free_model,
     const_model = const_model'',
     skolem_model = map (isa_term_entry_of_nun ctxt atomss) skolem_model}
  end;

end;
